//! TCP transport implementation.

use crate::config::TcpTransportConfig;
use crate::error::{Result, TcpTransportError};
use async_trait::async_trait;
use rumpsteak_aura_choreography::{Transport, TransportError, TransportResult};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::{TcpListener, TcpStream};
use tokio::sync::{mpsc, Mutex, RwLock};
use tracing::{debug, error, info, instrument, warn};

/// TCP transport state.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TransportState {
    /// Transport created but not started.
    Created,
    /// Transport is running and accepting connections.
    Running,
    /// Transport is shutting down.
    ShuttingDown,
    /// Transport has stopped.
    Stopped,
}

/// A TCP-based transport for inter-process communication.
///
/// This transport provides reliable message delivery over TCP with:
/// - Length-prefixed framing
/// - Automatic connection retry with exponential backoff
/// - Connection pooling and reuse
/// - Role-based routing
pub struct TcpTransport {
    /// Configuration.
    config: TcpTransportConfig,
    /// Current state.
    state: Arc<RwLock<TransportState>>,
    /// Outgoing connections (role -> stream).
    outgoing: Arc<RwLock<HashMap<String, Arc<Mutex<TcpStream>>>>>,
    /// Incoming message queues (role -> receiver).
    incoming: Arc<Mutex<HashMap<String, mpsc::Receiver<Vec<u8>>>>>,
    /// Senders for incoming messages (used by accept loop).
    incoming_senders: Arc<Mutex<HashMap<String, mpsc::Sender<Vec<u8>>>>>,
    /// Shutdown signal sender.
    shutdown_tx: Arc<Mutex<Option<mpsc::Sender<()>>>>,
}

impl TcpTransport {
    /// Create a new TCP transport with the given configuration.
    pub fn new(config: TcpTransportConfig) -> Self {
        Self {
            config,
            state: Arc::new(RwLock::new(TransportState::Created)),
            outgoing: Arc::new(RwLock::new(HashMap::new())),
            incoming: Arc::new(Mutex::new(HashMap::new())),
            incoming_senders: Arc::new(Mutex::new(HashMap::new())),
            shutdown_tx: Arc::new(Mutex::new(None)),
        }
    }

    /// Get the role name.
    pub fn role(&self) -> &str {
        &self.config.role
    }

    /// Get the current transport state.
    pub async fn state(&self) -> TransportState {
        *self.state.read().await
    }

    /// Start the transport (begin listening for connections).
    #[instrument(skip(self), fields(role = %self.config.role))]
    pub async fn start(&self) -> Result<()> {
        // Check state
        {
            let mut state = self.state.write().await;
            if *state != TransportState::Created {
                return Err(TcpTransportError::AlreadyStarted);
            }
            *state = TransportState::Running;
        }

        // Bind listener
        let listener = TcpListener::bind(&self.config.listen_addr)
            .await
            .map_err(|e| TcpTransportError::ConnectionFailed {
                peer: "listener".to_string(),
                reason: e.to_string(),
            })?;

        info!(addr = %self.config.listen_addr, "TCP transport listening");

        // Initialize incoming channels for each peer
        for peer in self.config.peers.keys() {
            let (tx, rx) = mpsc::channel(self.config.buffer_size);
            self.incoming_senders.lock().await.insert(peer.clone(), tx);
            self.incoming.lock().await.insert(peer.clone(), rx);
        }

        // Create shutdown channel
        let (shutdown_tx, mut shutdown_rx) = mpsc::channel::<()>(1);
        *self.shutdown_tx.lock().await = Some(shutdown_tx);

        // Spawn accept loop
        let incoming_senders = Arc::clone(&self.incoming_senders);
        let state = Arc::clone(&self.state);
        let role = self.config.role.clone();
        let buffer_size = self.config.buffer_size;

        tokio::spawn(async move {
            loop {
                tokio::select! {
                    accept_result = listener.accept() => {
                        match accept_result {
                            Ok((stream, addr)) => {
                                debug!(peer_addr = %addr, "Accepted connection");
                                let senders = Arc::clone(&incoming_senders);
                                let role_name = role.clone();
                                tokio::spawn(async move {
                                    if let Err(e) = handle_connection(stream, senders, &role_name, buffer_size).await {
                                        warn!(error = %e, "Connection handler error");
                                    }
                                });
                            }
                            Err(e) => {
                                error!(error = %e, "Accept error");
                            }
                        }
                    }
                    _ = shutdown_rx.recv() => {
                        info!("Shutting down listener");
                        break;
                    }
                }
            }
            *state.write().await = TransportState::Stopped;
        });

        Ok(())
    }

    /// Connect to a peer role.
    #[instrument(skip(self), fields(role = %self.config.role))]
    pub async fn connect_to(&self, peer_role: &str) -> Result<()> {
        let addr = self
            .config
            .peers
            .get(peer_role)
            .ok_or_else(|| TcpTransportError::UnknownPeer(peer_role.to_string()))?;

        let retry = &self.config.retry;
        let mut attempts = 0;
        let mut delay = retry.initial_delay;

        loop {
            match TcpStream::connect(addr).await {
                Ok(mut stream) => {
                    // Send our role name
                    let role_bytes = self.config.role.as_bytes();
                    let len = role_bytes.len() as u32;
                    stream.write_all(&len.to_be_bytes()).await?;
                    stream.write_all(role_bytes).await?;
                    stream.flush().await?;

                    info!(peer = peer_role, addr = %addr, "Connected to peer");
                    self.outgoing
                        .write()
                        .await
                        .insert(peer_role.to_string(), Arc::new(Mutex::new(stream)));
                    return Ok(());
                }
                Err(e) => {
                    attempts += 1;
                    if attempts >= retry.max_attempts {
                        return Err(TcpTransportError::ConnectionFailed {
                            peer: peer_role.to_string(),
                            reason: format!("Failed after {} attempts: {}", attempts, e),
                        });
                    }
                    warn!(
                        peer = peer_role,
                        attempt = attempts,
                        delay_ms = delay.as_millis(),
                        "Connection failed, retrying"
                    );
                    tokio::time::sleep(delay).await;
                    delay = std::cmp::min(
                        Duration::from_secs_f64(delay.as_secs_f64() * retry.backoff_multiplier),
                        retry.max_delay,
                    );
                }
            }
        }
    }

    /// Connect to all configured peers.
    pub async fn connect_all(&self) -> Result<()> {
        for peer in self.config.peers.keys() {
            self.connect_to(peer).await?;
        }
        Ok(())
    }
}

/// Handle an incoming TCP connection.
async fn handle_connection(
    mut stream: TcpStream,
    senders: Arc<Mutex<HashMap<String, mpsc::Sender<Vec<u8>>>>>,
    local_role: &str,
    _buffer_size: usize,
) -> Result<()> {
    // Read peer's role name
    let mut len_buf = [0u8; 4];
    stream.read_exact(&mut len_buf).await?;
    let len = u32::from_be_bytes(len_buf) as usize;

    if len > 1024 {
        return Err(TcpTransportError::InvalidMessage(
            "Role name too long".to_string(),
        ));
    }

    let mut role_buf = vec![0u8; len];
    stream.read_exact(&mut role_buf).await?;
    let peer_role = String::from_utf8(role_buf)
        .map_err(|e| TcpTransportError::InvalidMessage(format!("Invalid role name: {}", e)))?;

    debug!(peer = %peer_role, local = local_role, "Identified peer");

    // Read messages in a loop
    loop {
        let mut len_buf = [0u8; 4];
        match stream.read_exact(&mut len_buf).await {
            Ok(_) => {}
            Err(e) if e.kind() == std::io::ErrorKind::UnexpectedEof => {
                debug!(peer = %peer_role, "Connection closed by peer");
                break;
            }
            Err(e) => return Err(e.into()),
        }
        let len = u32::from_be_bytes(len_buf) as usize;

        // Sanity check message size (16 MB limit)
        if len > 16 * 1024 * 1024 {
            return Err(TcpTransportError::InvalidMessage(
                "Message too large".to_string(),
            ));
        }

        let mut payload = vec![0u8; len];
        stream.read_exact(&mut payload).await?;

        // Forward to channel
        let senders = senders.lock().await;
        if let Some(sender) = senders.get(&peer_role) {
            if sender.send(payload).await.is_err() {
                debug!(peer = %peer_role, "Receiver dropped");
                break;
            }
        } else {
            warn!(peer = %peer_role, "No channel for peer");
        }
    }

    Ok(())
}

use std::time::Duration;

#[async_trait]
impl Transport for TcpTransport {
    #[instrument(skip(self, message), fields(role = %self.config.role, to = to_role, msg_len = message.len()))]
    async fn send(&self, to_role: &str, message: Vec<u8>) -> TransportResult<()> {
        let outgoing = self.outgoing.read().await;
        let stream = outgoing
            .get(to_role)
            .ok_or_else(|| TransportError::UnknownRole(to_role.to_string()))?;

        let mut stream = stream.lock().await;

        // Write length prefix
        let len = message.len() as u32;
        stream
            .write_all(&len.to_be_bytes())
            .await
            .map_err(TransportError::IoError)?;

        // Write payload
        stream
            .write_all(&message)
            .await
            .map_err(TransportError::IoError)?;
        stream.flush().await.map_err(TransportError::IoError)?;

        debug!(msg_len = message.len(), "Message sent");
        Ok(())
    }

    #[instrument(skip(self), fields(role = %self.config.role, from = from_role))]
    async fn recv(&self, from_role: &str) -> TransportResult<Vec<u8>> {
        let mut incoming = self.incoming.lock().await;
        let receiver = incoming
            .get_mut(from_role)
            .ok_or_else(|| TransportError::UnknownRole(from_role.to_string()))?;

        let msg = receiver.recv().await.ok_or(TransportError::ChannelClosed)?;
        debug!(msg_len = msg.len(), "Message received");
        Ok(msg)
    }

    fn is_connected(&self, role: &str) -> bool {
        self.config.peers.contains_key(role)
    }

    async fn close(&self) -> TransportResult<()> {
        *self.state.write().await = TransportState::ShuttingDown;

        // Send shutdown signal
        if let Some(tx) = self.shutdown_tx.lock().await.take() {
            let _ = tx.send(()).await;
        }

        // Close all connections
        self.outgoing.write().await.clear();

        info!(role = %self.config.role, "Transport closed");
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_transport_state_transitions() {
        let config = TcpTransportConfig::new("Test", "127.0.0.1:0");
        let transport = TcpTransport::new(config);

        assert_eq!(transport.state().await, TransportState::Created);
    }

    #[tokio::test]
    async fn test_transport_lifecycle() {
        let config =
            TcpTransportConfig::new("Alice", "127.0.0.1:0").with_peer("Bob", "127.0.0.1:9999");

        let transport = TcpTransport::new(config);
        assert_eq!(transport.role(), "Alice");

        // Starting should work
        // Note: Using port 0 lets the OS assign a port
        transport.start().await.unwrap();
        assert_eq!(transport.state().await, TransportState::Running);

        // Double start should fail
        assert!(transport.start().await.is_err());

        // Close
        transport.close().await.unwrap();
    }
}
