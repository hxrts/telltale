//! TCP transport implementation.

use crate::config::{TcpPeerAuthentication, TcpTransportConfig};

const TCP_AUTH_NONE: u8 = 0;
const TCP_AUTH_PSK: u8 = 1;
use crate::error::{TcpResult, TcpTransportError};
use async_trait::async_trait;
use std::collections::{BTreeMap, BTreeSet};
use std::net::IpAddr;
use std::sync::Arc;
use std::time::{Duration, Instant};
use telltale_runtime::{
    topology::wire, DocumentedTransportContract, MessageLenBytes, QueueCapacity, RoleName,
    Transport, TransportContractProfile, TransportContractTier, TransportError,
    TransportOperationalContract, TransportResult, TransportSemanticContract, TransportStartupMode,
};
use telltale_types::effects::{ChaCha20Rng, Rng, SecureRng};
use telltale_types::FixedQ32;
use tokio::net::{TcpListener, TcpStream};
use tokio::sync::{mpsc, Mutex, OwnedSemaphorePermit, RwLock, Semaphore};
use tokio::task::JoinHandle;
use tracing::{debug, error, info, instrument, warn};

type IncomingReceiver = Arc<Mutex<mpsc::Receiver<Vec<u8>>>>;

#[cfg(feature = "redacted-logs")]
fn log_value(value: &str) -> String {
    let digest = blake3::hash(value.as_bytes());
    format!("redacted:{}", &digest.to_hex()[..16])
}

#[cfg(not(feature = "redacted-logs"))]
fn log_value(value: &str) -> &str {
    value
}

#[derive(Debug, Clone, Copy)]
struct SourceRateState {
    window_start: Instant,
    attempts: usize,
    live_connections: usize,
}

fn scale_duration_by_fixed(duration: Duration, factor: FixedQ32) -> Duration {
    if factor <= FixedQ32::zero() {
        return duration;
    }

    let duration_nanos = duration.as_nanos();
    let factor_bits = u128::try_from(factor.to_bits().max(0)).unwrap_or_default();
    let scaled = duration_nanos
        .saturating_mul(factor_bits)
        .checked_shr(FixedQ32::FRACTIONAL_BITS)
        .unwrap_or(0);
    let nanos = if duration_nanos > 0 && scaled == 0 {
        1
    } else {
        scaled
    };
    let nanos = u64::try_from(nanos).unwrap_or(u64::MAX);
    Duration::from_nanos(nanos)
}

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
    outgoing: Arc<RwLock<BTreeMap<String, Arc<Mutex<TcpStream>>>>>,
    /// Incoming message queues (role -> receiver).
    incoming: Arc<Mutex<BTreeMap<String, IncomingReceiver>>>,
    /// Senders for incoming messages (used by accept loop).
    incoming_senders: Arc<Mutex<BTreeMap<String, mpsc::Sender<Vec<u8>>>>>,
    /// Shutdown signal sender.
    shutdown_tx: Arc<Mutex<Option<mpsc::Sender<()>>>>,
    /// Accept-loop task.
    accept_task: Arc<Mutex<Option<JoinHandle<()>>>>,
    /// Active connection tasks.
    connection_tasks: Arc<Mutex<Vec<JoinHandle<()>>>>,
    /// Peer roles with currently live inbound connections.
    claimed_inbound_roles: Arc<Mutex<BTreeSet<String>>>,
    /// Global cap for payload bytes currently being read by inbound handlers.
    payload_budget: Arc<Semaphore>,
    /// Per-source connection and reconnect state.
    source_limits: Arc<Mutex<BTreeMap<IpAddr, SourceRateState>>>,
}

impl TcpTransport {
    /// Create a new TCP transport with the given configuration.
    pub fn new(config: TcpTransportConfig) -> Self {
        let max_inflight_payload_bytes = config.max_inflight_payload_bytes;
        Self {
            config,
            state: Arc::new(RwLock::new(TransportState::Created)),
            outgoing: Arc::new(RwLock::new(BTreeMap::new())),
            incoming: Arc::new(Mutex::new(BTreeMap::new())),
            incoming_senders: Arc::new(Mutex::new(BTreeMap::new())),
            shutdown_tx: Arc::new(Mutex::new(None)),
            accept_task: Arc::new(Mutex::new(None)),
            connection_tasks: Arc::new(Mutex::new(Vec::new())),
            claimed_inbound_roles: Arc::new(Mutex::new(BTreeSet::new())),
            payload_budget: Arc::new(Semaphore::new(max_inflight_payload_bytes)),
            source_limits: Arc::new(Mutex::new(BTreeMap::new())),
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

    async fn ensure_created_and_mark_running(&self) -> TcpResult<()> {
        ensure_authentication_configured(&self.config.authentication)?;
        let mut state = self.state.write().await;
        if *state != TransportState::Created {
            return Err(TcpTransportError::AlreadyStarted);
        }
        *state = TransportState::Running;
        drop(state);
        Ok(())
    }

    async fn initialize_incoming_channels(&self) {
        for peer in self.config.peers.keys() {
            let (tx, rx) = mpsc::channel(self.config.buffer_size.as_usize());
            self.incoming_senders.lock().await.insert(peer.clone(), tx);
            self.incoming
                .lock()
                .await
                .insert(peer.clone(), Arc::new(Mutex::new(rx)));
        }
    }

    async fn install_shutdown_channel(&self) -> mpsc::Receiver<()> {
        let (shutdown_tx, shutdown_rx) = mpsc::channel::<()>(1);
        *self.shutdown_tx.lock().await = Some(shutdown_tx);
        shutdown_rx
    }

    fn spawn_accept_loop(
        &self,
        listener: TcpListener,
        mut shutdown_rx: mpsc::Receiver<()>,
    ) -> JoinHandle<()> {
        let incoming_senders = Arc::clone(&self.incoming_senders);
        let claimed_roles = Arc::clone(&self.claimed_inbound_roles);
        let payload_budget = Arc::clone(&self.payload_budget);
        let source_limits = Arc::clone(&self.source_limits);
        let state = Arc::clone(&self.state);
        let connection_tasks = Arc::clone(&self.connection_tasks);
        let role = self.config.role.clone();
        let buffer_size = self.config.buffer_size;
        let max_connections = self.config.max_connections;
        let per_source_connection_limit = self.config.per_source_connection_limit;
        let per_source_reconnect_limit = self.config.per_source_reconnect_limit;
        let reconnect_window = self.config.reconnect_window;
        let read_timeout = self.config.read_timeout;
        let authentication = self.config.authentication.clone();

        tokio::spawn(async move {
            loop {
                // forever: runs until shutdown signal received via shutdown_rx
                tokio::select! {
                    accept_result = listener.accept() => {
                        match accept_result {
                            Ok((stream, addr)) => {
                                debug!(peer_addr = %log_value(&addr.to_string()), "Accepted connection");
                                let source_ip = addr.ip();
                                let mut tasks = connection_tasks.lock().await;
                                tasks.retain(|join_handle| !join_handle.is_finished());
                                if tasks.len() >= max_connections {
                                    warn!(
                                        peer_addr = %log_value(&addr.to_string()),
                                        max_connections,
                                        "Rejecting connection because max_connections is reached"
                                    );
                                    continue;
                                }
                                if let Err(error) = admit_source(
                                    &source_limits,
                                    source_ip,
                                    per_source_connection_limit,
                                    per_source_reconnect_limit,
                                    reconnect_window,
                                ).await {
                                    warn!(
                                        peer_addr = %log_value(&addr.to_string()),
                                        error = %error,
                                        "Rejecting connection because source limits are reached"
                                    );
                                    continue;
                                }
                                let senders = Arc::clone(&incoming_senders);
                                let claims = Arc::clone(&claimed_roles);
                                let budget = Arc::clone(&payload_budget);
                                let connection_authentication = authentication.clone();
                                let source_state = Arc::clone(&source_limits);
                                let role_name = role.clone();
                                let task = tokio::spawn(async move {
                                    if let Err(e) = handle_connection(
                                        stream,
                                        senders,
                                        claims,
                                        budget,
                                        connection_authentication,
                                        &role_name,
                                        buffer_size,
                                        read_timeout,
                                    ).await {
                                        warn!(error = %e, "Connection handler error");
                                    }
                                    release_source(&source_state, source_ip).await;
                                });
                                tasks.push(task);
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
        })
    }

    async fn incoming_receiver_for_role(
        &self,
        role_str: &str,
        from_role: &RoleName,
    ) -> TransportResult<IncomingReceiver> {
        self.incoming
            .lock()
            .await
            .get(role_str)
            .cloned()
            .ok_or_else(|| TransportError::UnknownRole(from_role.clone()))
    }

    async fn take_connection_tasks(&self) -> Vec<JoinHandle<()>> {
        std::mem::take(&mut *self.connection_tasks.lock().await)
    }

    /// Start the transport (begin listening for connections).
    #[instrument(skip(self), fields(role = %log_value(&self.config.role)))]
    pub async fn start(&self) -> TcpResult<()> {
        self.ensure_created_and_mark_running().await?;

        // Bind listener
        let listener = TcpListener::bind(&self.config.listen_addr)
            .await
            .map_err(|e| TcpTransportError::ConnectionFailed {
                peer: "listener".to_string(),
                reason: e.to_string(),
            })?;

        info!(addr = %log_value(&self.config.listen_addr), "TCP transport listening");

        self.initialize_incoming_channels().await;

        let shutdown_rx = self.install_shutdown_channel().await;
        let accept_task = self.spawn_accept_loop(listener, shutdown_rx);
        *self.accept_task.lock().await = Some(accept_task);

        Ok(())
    }

    /// Connect to a peer role.
    #[instrument(skip(self), fields(role = %log_value(&self.config.role)))]
    pub async fn connect_to(&self, peer_role: &str) -> TcpResult<()> {
        ensure_authentication_configured(&self.config.authentication)?;
        let addr = self
            .config
            .peers
            .get(peer_role)
            .ok_or_else(|| TcpTransportError::UnknownPeer(peer_role.to_string()))?;

        let retry = &self.config.retry;
        let mut attempts = 0;
        let mut delay = retry.initial_delay;

        loop {
            // bounded: exits on success or when attempts >= retry.max_attempts
            match TcpStream::connect(addr).await {
                Ok(mut stream) => {
                    let role_bytes = self.config.role.as_bytes();
                    wire::write_preamble(&mut stream, self.config.write_timeout).await?;
                    wire::write_role_name(&mut stream, role_bytes, self.config.write_timeout)
                        .await?;
                    write_authentication(
                        &mut stream,
                        &self.config.authentication,
                        role_bytes,
                        self.config.write_timeout,
                    )
                    .await?;
                    wire::flush_timeout(&mut stream, self.config.write_timeout).await?;

                    info!(
                        peer = %log_value(peer_role),
                        addr = %log_value(addr),
                        "Connected to peer"
                    );
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
                        peer = %log_value(peer_role),
                        attempt = attempts,
                        delay_ms = delay.as_millis(),
                        "Connection failed, retrying"
                    );
                    tokio::time::sleep(delay).await;
                    delay = std::cmp::min(
                        scale_duration_by_fixed(delay, retry.backoff_multiplier),
                        retry.max_delay,
                    );
                }
            }
        }
    }

    /// Connect to all configured peers.
    pub async fn connect_all(&self) -> TcpResult<()> {
        for peer in self.config.peers.keys() {
            self.connect_to(peer).await?;
        }
        Ok(())
    }
}

impl DocumentedTransportContract for TcpTransport {
    fn contract_profile() -> TransportContractProfile {
        TransportContractProfile {
            transport_name: "TcpTransport",
            tier: TransportContractTier::FirstPartyRuntime,
            semantics: TransportSemanticContract {
                role_addressed_routing: true,
                authenticated_peers: false,
                per_peer_fifo_delivery: true,
                fail_closed_unknown_role: true,
                no_message_synthesis: true,
                explicit_readiness_errors: true,
                deterministic_for_regression: false,
            },
            operational: TransportOperationalContract {
                transport_type: telltale_runtime::TransportType::Tcp,
                startup_mode: TransportStartupMode::ExplicitStart,
                environment_resolved: false,
            },
            notes: vec![
                "Reference TCP transport in the separate telltale-transport crate.",
                "Requires explicit start before first use.",
                "Authentication is configuration-dependent; this static profile is conservative.",
                "Use TcpTransportConfig::runtime_transport_contract() for theorem-pack admission.",
                "Unauthenticated mode is trusted-network only and must be explicitly enabled.",
            ],
        }
    }
}

/// Handle an incoming TCP connection.
async fn handle_connection(
    mut stream: TcpStream,
    senders: Arc<Mutex<BTreeMap<String, mpsc::Sender<Vec<u8>>>>>,
    claimed_roles: Arc<Mutex<BTreeSet<String>>>,
    payload_budget: Arc<Semaphore>,
    authentication: TcpPeerAuthentication,
    local_role: &str,
    _buffer_size: QueueCapacity,
    read_timeout: Duration,
) -> TcpResult<()> {
    wire::read_preamble(&mut stream, read_timeout).await?;
    let role_buf = wire::read_role_name_bytes(&mut stream, read_timeout).await?;
    let peer_role = String::from_utf8(role_buf)
        .map_err(|e| TcpTransportError::InvalidMessage(format!("Invalid role name: {}", e)))?;
    read_and_verify_authentication(
        &mut stream,
        &authentication,
        peer_role.as_bytes(),
        read_timeout,
    )
    .await?;

    debug!(
        peer = %log_value(&peer_role),
        local = %log_value(local_role),
        "Identified peer"
    );
    let sender = lookup_sender(&senders, &peer_role).await;
    let Some(sender) = sender else {
        warn!(
            peer = %log_value(&peer_role),
            local = %log_value(local_role),
            "Unknown peer attempted connection"
        );
        return Err(TcpTransportError::UnknownPeer(peer_role));
    };
    claim_peer_role(&claimed_roles, &peer_role).await?;
    let result = async {
        loop {
            // forever: reads messages until connection closed (EOF) or error
            let len = match wire::read_payload_len(&mut stream, read_timeout).await {
                Ok(len) => len,
                Err(wire::TcpWireError::Io(e)) if e.kind() == std::io::ErrorKind::UnexpectedEof => {
                    debug!(peer = %log_value(&peer_role), "Connection closed by peer");
                    break;
                }
                Err(e) => return Err(e.into()),
            };

            let _payload_permit = acquire_payload_budget(&payload_budget, len.as_usize()).await?;
            let mut payload = vec![0u8; len.as_usize()];
            wire::read_exact_timeout(&mut stream, &mut payload, read_timeout).await?;

            if sender.send(payload).await.is_err() {
                debug!(peer = %log_value(&peer_role), "Receiver dropped");
                break;
            }
        }
        Ok(())
    }
    .await;
    claimed_roles.lock().await.remove(&peer_role);
    result
}

fn ensure_authentication_configured(authentication: &TcpPeerAuthentication) -> TcpResult<()> {
    match authentication {
        TcpPeerAuthentication::PreSharedKey(_) => Ok(()),
        TcpPeerAuthentication::UnauthenticatedTrustedNetwork { explicit_allow } => {
            if *explicit_allow {
                Ok(())
            } else {
                Err(TcpTransportError::AuthenticationModeNotConfigured)
            }
        }
    }
}

fn psk_mac(key: &[u8; 32], role_bytes: &[u8], nonce: &[u8; 16]) -> [u8; 32] {
    let mut input =
        Vec::with_capacity(wire::TCP_WIRE_MAGIC.len() + 1 + role_bytes.len() + nonce.len());
    input.extend_from_slice(&wire::TCP_WIRE_MAGIC);
    input.push(wire::TCP_WIRE_VERSION);
    input.extend_from_slice(role_bytes);
    input.extend_from_slice(nonce);
    *blake3::keyed_hash(key, &input).as_bytes()
}

async fn write_authentication(
    stream: &mut TcpStream,
    authentication: &TcpPeerAuthentication,
    role_bytes: &[u8],
    timeout: Duration,
) -> TcpResult<()> {
    match authentication {
        TcpPeerAuthentication::UnauthenticatedTrustedNetwork { explicit_allow } => {
            if !explicit_allow {
                return Err(TcpTransportError::AuthenticationModeNotConfigured);
            }
            wire::write_all_timeout(stream, &[TCP_AUTH_NONE], timeout)
                .await
                .map_err(Into::into)
        }
        TcpPeerAuthentication::PreSharedKey(key) => {
            let mut nonce = [0_u8; 16];
            let mut rng = <ChaCha20Rng as SecureRng>::from_os_entropy();
            nonce[..8].copy_from_slice(&rng.next_u64().to_be_bytes());
            nonce[8..].copy_from_slice(&rng.next_u64().to_be_bytes());
            let mac = psk_mac(key, role_bytes, &nonce);
            wire::write_all_timeout(stream, &[TCP_AUTH_PSK], timeout).await?;
            wire::write_all_timeout(stream, &nonce, timeout).await?;
            wire::write_all_timeout(stream, &mac, timeout)
                .await
                .map_err(Into::into)
        }
    }
}

async fn read_and_verify_authentication(
    stream: &mut TcpStream,
    authentication: &TcpPeerAuthentication,
    role_bytes: &[u8],
    timeout: Duration,
) -> TcpResult<()> {
    let mut auth_mode = [0_u8; 1];
    wire::read_exact_timeout(stream, &mut auth_mode, timeout).await?;
    match authentication {
        TcpPeerAuthentication::UnauthenticatedTrustedNetwork { explicit_allow } => {
            if !explicit_allow {
                return Err(TcpTransportError::AuthenticationModeNotConfigured);
            }
            if auth_mode[0] == TCP_AUTH_NONE {
                Ok(())
            } else {
                Err(TcpTransportError::AuthenticationFailed(
                    "unexpected authenticated peer on unauthenticated transport".to_string(),
                ))
            }
        }
        TcpPeerAuthentication::PreSharedKey(key) => {
            if auth_mode[0] != TCP_AUTH_PSK {
                return Err(TcpTransportError::AuthenticationFailed(
                    "peer did not present PSK authentication".to_string(),
                ));
            }
            let mut nonce = [0_u8; 16];
            let mut mac = [0_u8; 32];
            wire::read_exact_timeout(stream, &mut nonce, timeout).await?;
            wire::read_exact_timeout(stream, &mut mac, timeout).await?;
            let expected = psk_mac(key, role_bytes, &nonce);
            if mac == expected {
                Ok(())
            } else {
                Err(TcpTransportError::AuthenticationFailed(
                    "invalid PSK MAC".to_string(),
                ))
            }
        }
    }
}

async fn admit_source(
    sources: &Arc<Mutex<BTreeMap<IpAddr, SourceRateState>>>,
    source_ip: IpAddr,
    live_limit: usize,
    reconnect_limit: usize,
    reconnect_window: Duration,
) -> TcpResult<()> {
    let mut sources = sources.lock().await;
    let now = Instant::now();
    let state = sources.entry(source_ip).or_insert(SourceRateState {
        window_start: now,
        attempts: 0,
        live_connections: 0,
    });

    if now.duration_since(state.window_start) > reconnect_window {
        state.window_start = now;
        state.attempts = 0;
    }

    if state.live_connections >= live_limit {
        return Err(TcpTransportError::ResourceLimitExceeded(format!(
            "source {source_ip} has too many live connections"
        )));
    }
    if state.attempts >= reconnect_limit {
        return Err(TcpTransportError::ResourceLimitExceeded(format!(
            "source {source_ip} exceeded reconnect limit"
        )));
    }

    state.live_connections += 1;
    state.attempts += 1;
    Ok(())
}

async fn release_source(
    sources: &Arc<Mutex<BTreeMap<IpAddr, SourceRateState>>>,
    source_ip: IpAddr,
) {
    let mut sources = sources.lock().await;
    if let Some(state) = sources.get_mut(&source_ip) {
        state.live_connections = state.live_connections.saturating_sub(1);
    }
}

async fn acquire_payload_budget(
    payload_budget: &Arc<Semaphore>,
    bytes: usize,
) -> TcpResult<OwnedSemaphorePermit> {
    let permits = u32::try_from(bytes).map_err(|_| {
        TcpTransportError::ResourceLimitExceeded("payload length exceeds permit range".to_string())
    })?;
    Arc::clone(payload_budget)
        .try_acquire_many_owned(permits)
        .map_err(|_| {
            TcpTransportError::ResourceLimitExceeded(
                "global in-flight payload byte cap reached".to_string(),
            )
        })
}

async fn claim_peer_role(
    claimed_roles: &Arc<Mutex<BTreeSet<String>>>,
    peer_role: &str,
) -> TcpResult<()> {
    let mut claimed = claimed_roles.lock().await;
    if !claimed.insert(peer_role.to_string()) {
        return Err(TcpTransportError::DuplicatePeer(peer_role.to_string()));
    }
    Ok(())
}

#[allow(clippy::type_complexity)]
async fn lookup_sender(
    senders: &Arc<Mutex<BTreeMap<String, mpsc::Sender<Vec<u8>>>>>,
    peer_role: &str,
) -> Option<mpsc::Sender<Vec<u8>>> {
    let sender_map = senders.lock().await;
    sender_map.get(peer_role).cloned()
}

#[async_trait]
impl Transport for TcpTransport {
    #[instrument(skip(self, message), fields(role = %log_value(&self.config.role), to = %log_value(to_role.as_str()), msg_len = message.len()))]
    async fn send(&self, to_role: &RoleName, message: Vec<u8>) -> TransportResult<()> {
        let role_str = to_role.as_str();
        let stream = {
            let outgoing = self.outgoing.read().await;
            outgoing
                .get(role_str)
                .cloned()
                .ok_or_else(|| TransportError::UnknownRole(to_role.clone()))?
        };

        // LOCK_AWAIT_OK: stream writes must be serialized per peer connection.
        let mut stream = stream.lock().await;

        // Write length prefix
        let len = MessageLenBytes::try_from(message.len())
            .map_err(|e| TransportError::SendFailed(e.to_string()))?;
        wire::write_payload_len(&mut *stream, len, self.config.write_timeout)
            .await
            .map_err(|e| TransportError::SendFailed(e.to_string()))?;

        // Write payload
        wire::write_all_timeout(&mut *stream, &message, self.config.write_timeout)
            .await
            .map_err(|e| TransportError::SendFailed(e.to_string()))?;
        wire::flush_timeout(&mut *stream, self.config.write_timeout)
            .await
            .map_err(|e| TransportError::SendFailed(e.to_string()))?;

        debug!(msg_len = message.len(), "Message sent");
        Ok(())
    }

    #[instrument(skip(self), fields(role = %log_value(&self.config.role), from = %log_value(from_role.as_str())))]
    async fn recv(&self, from_role: &RoleName) -> TransportResult<Vec<u8>> {
        let role_str = from_role.as_str();
        let receiver = self.incoming_receiver_for_role(role_str, from_role).await?;

        // LOCK_AWAIT_OK: receiver access is serialized to preserve per-peer FIFO.
        let mut receiver = receiver.lock().await;
        let bytes = receiver.recv().await.ok_or(TransportError::ChannelClosed)?;
        debug!(msg_len = bytes.len(), "Message received");
        Ok(bytes)
    }

    fn is_connected(&self, role: &RoleName) -> bool {
        self.config.peers.contains_key(role.as_str())
    }

    async fn close(&self) -> TransportResult<()> {
        *self.state.write().await = TransportState::ShuttingDown;

        // Send shutdown signal - receiver may be dropped during shutdown.
        if let Some(tx) = self.shutdown_tx.lock().await.take() {
            if tx.send(()).await.is_err() {
                debug!("shutdown receiver already dropped; continuing close");
            }
        }

        if let Some(task) = self.accept_task.lock().await.take() {
            if let Err(err) = task.await {
                debug!("best-effort accept task join failed during close: {err}");
            }
        }

        let mut tasks = self.take_connection_tasks().await;
        for task in &tasks {
            task.abort();
        }
        for task in tasks.drain(..) {
            if let Err(err) = task.await {
                debug!("best-effort connection task join failed during close: {err}");
            }
        }

        // Close all connections
        self.outgoing.write().await.clear();
        *self.state.write().await = TransportState::Stopped;

        info!(role = %log_value(&self.config.role), "Transport closed");
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::net::SocketAddr;

    #[tokio::test]
    async fn test_transport_state_transitions() {
        let config = TcpTransportConfig::new("Test", "127.0.0.1:0");
        let transport = TcpTransport::new(config);

        assert_eq!(transport.state().await, TransportState::Created);
    }

    #[tokio::test]
    async fn test_transport_lifecycle() {
        let config = TcpTransportConfig::new("Alice", "127.0.0.1:0")
            .allow_unauthenticated_for_trusted_network()
            .with_peer("Bob", "127.0.0.1:9999");

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
        assert_eq!(transport.state().await, TransportState::Stopped);
    }

    #[tokio::test]
    async fn test_transport_ipv6_lifecycle() {
        // Test that transport can bind to IPv6 loopback
        let config = TcpTransportConfig::new("Alice", "[::1]:0")
            .allow_unauthenticated_for_trusted_network()
            .with_peer("Bob", "[::1]:9999");

        let transport = TcpTransport::new(config);
        assert_eq!(transport.role(), "Alice");

        // Starting should work on IPv6
        transport.start().await.unwrap();
        assert_eq!(transport.state().await, TransportState::Running);

        // Close
        transport.close().await.unwrap();
    }

    #[tokio::test]
    async fn test_transport_ipv6_dual_stack() {
        // Test IPv6 any address (dual-stack if supported)
        let config =
            TcpTransportConfig::new("Server", "[::]:0").allow_unauthenticated_for_trusted_network();
        let transport = TcpTransport::new(config);

        transport.start().await.unwrap();
        assert_eq!(transport.state().await, TransportState::Running);

        transport.close().await.unwrap();
    }

    #[tokio::test]
    async fn test_transport_config_with_ipv6_peers() {
        // Verify configuration accepts IPv6 peer addresses
        let config = TcpTransportConfig::new("Alice", "127.0.0.1:0")
            .allow_unauthenticated_for_trusted_network()
            .with_peer("Bob", "[::1]:8080")
            .with_peer("Carol", "[2001:db8::1]:9000")
            .with_peer("Dave", "[fe80::1]:3000");

        assert!(config.peers.contains_key("Bob"));
        assert_eq!(config.peers.get("Bob"), Some(&"[::1]:8080".to_string()));
        assert_eq!(
            config.peers.get("Carol"),
            Some(&"[2001:db8::1]:9000".to_string())
        );
        assert_eq!(
            config.peers.get("Dave"),
            Some(&"[fe80::1]:3000".to_string())
        );
    }

    #[test]
    fn scale_duration_negative_factor_preserves_duration() {
        let duration = Duration::from_millis(25);
        let factor = FixedQ32::from_ratio(-1, 1).expect("negative fixed factor");
        assert_eq!(scale_duration_by_fixed(duration, factor), duration);
    }

    async fn connect_and_claim_role(addr: SocketAddr, role: &str) -> TcpStream {
        let mut stream = TcpStream::connect(addr).await.expect("connect test client");
        wire::write_preamble(&mut stream, Duration::from_secs(1))
            .await
            .expect("write wire preamble");
        wire::write_role_name(&mut stream, role.as_bytes(), Duration::from_secs(1))
            .await
            .expect("write role name");
        wire::write_all_timeout(&mut stream, &[TCP_AUTH_NONE], Duration::from_secs(1))
            .await
            .expect("write unauthenticated auth mode");
        wire::flush_timeout(&mut stream, Duration::from_secs(1))
            .await
            .expect("flush role claim");
        stream
    }

    #[tokio::test]
    async fn transport_start_requires_configured_authentication() {
        let config = TcpTransportConfig::new("Alice", "127.0.0.1:0");
        let transport = TcpTransport::new(config);
        let err = transport
            .start()
            .await
            .expect_err("start should reject implicit unauthenticated mode");
        assert!(matches!(
            err,
            TcpTransportError::AuthenticationModeNotConfigured
        ));
    }

    #[tokio::test]
    async fn psk_authentication_rejects_unauthenticated_peer() {
        let listener = TcpListener::bind("127.0.0.1:0")
            .await
            .expect("bind test listener");
        let addr = listener.local_addr().expect("test listener address");

        let (tx, _rx) = mpsc::channel(4);
        let senders = Arc::new(Mutex::new(BTreeMap::from([("Bob".to_string(), tx)])));
        let claimed_roles = Arc::new(Mutex::new(BTreeSet::new()));
        let payload_budget = Arc::new(Semaphore::new(1024 * 1024));
        let buffer_size = QueueCapacity::try_new(4).expect("test queue capacity");
        let read_timeout = Duration::from_secs(5);

        let accept = tokio::spawn(async move {
            let (stream, _) = listener.accept().await.expect("accept client");
            handle_connection(
                stream,
                senders,
                claimed_roles,
                payload_budget,
                TcpPeerAuthentication::PreSharedKey([7; 32]),
                "Alice",
                buffer_size,
                read_timeout,
            )
            .await
        });

        let _client = connect_and_claim_role(addr, "Bob").await;
        let err = tokio::time::timeout(Duration::from_secs(1), accept)
            .await
            .expect("auth failure should finish promptly")
            .expect("auth failure handler should not panic")
            .expect_err("unauthenticated peer must fail PSK admission");
        assert!(matches!(err, TcpTransportError::AuthenticationFailed(_)));
    }

    #[tokio::test]
    async fn unknown_role_claim_is_rejected() {
        let listener = TcpListener::bind("127.0.0.1:0")
            .await
            .expect("bind test listener");
        let addr = listener.local_addr().expect("test listener address");

        let (tx, _rx) = mpsc::channel(4);
        let senders = Arc::new(Mutex::new(BTreeMap::from([("Bob".to_string(), tx)])));
        let claimed_roles = Arc::new(Mutex::new(BTreeSet::new()));
        let payload_budget = Arc::new(Semaphore::new(1024 * 1024));
        let buffer_size = QueueCapacity::try_new(4).expect("test queue capacity");
        let read_timeout = Duration::from_secs(5);

        let accept = tokio::spawn(async move {
            let (stream, _) = listener.accept().await.expect("accept client");
            handle_connection(
                stream,
                senders,
                claimed_roles,
                payload_budget,
                TcpPeerAuthentication::UnauthenticatedTrustedNetwork {
                    explicit_allow: true,
                },
                "Alice",
                buffer_size,
                read_timeout,
            )
            .await
        });

        let _client = connect_and_claim_role(addr, "Mallory").await;
        let err = tokio::time::timeout(Duration::from_secs(1), accept)
            .await
            .expect("unknown role claim should finish promptly")
            .expect("unknown role handler should not panic")
            .expect_err("unknown role claim must fail closed");
        assert!(matches!(err, TcpTransportError::UnknownPeer(role) if role == "Mallory"));
    }

    #[tokio::test]
    async fn duplicate_live_role_claim_is_rejected() {
        let listener = TcpListener::bind("127.0.0.1:0")
            .await
            .expect("bind test listener");
        let addr = listener.local_addr().expect("test listener address");

        let (tx, _rx) = mpsc::channel(4);
        let senders = Arc::new(Mutex::new(BTreeMap::from([("Bob".to_string(), tx)])));
        let claimed_roles = Arc::new(Mutex::new(BTreeSet::new()));
        let payload_budget = Arc::new(Semaphore::new(1024 * 1024));
        let read_timeout = Duration::from_secs(5);
        let buffer_size = QueueCapacity::try_new(4).expect("test queue capacity");

        let first_senders = Arc::clone(&senders);
        let first_claims = Arc::clone(&claimed_roles);
        let first_budget = Arc::clone(&payload_budget);
        let first_accept = tokio::spawn(async move {
            let (stream, _) = listener.accept().await.expect("accept first client");
            handle_connection(
                stream,
                first_senders,
                first_claims,
                first_budget,
                TcpPeerAuthentication::UnauthenticatedTrustedNetwork {
                    explicit_allow: true,
                },
                "Alice",
                buffer_size,
                read_timeout,
            )
            .await
        });

        let first_client = connect_and_claim_role(addr, "Bob").await;
        tokio::time::timeout(Duration::from_secs(1), async {
            loop {
                if claimed_roles.lock().await.contains("Bob") {
                    break;
                }
                tokio::time::sleep(Duration::from_millis(10)).await;
            }
        })
        .await
        .expect("first role claim should become active");

        let listener = TcpListener::bind("127.0.0.1:0")
            .await
            .expect("bind second test listener");
        let second_addr = listener.local_addr().expect("second listener address");
        let second_senders = Arc::clone(&senders);
        let second_claims = Arc::clone(&claimed_roles);
        let second_budget = Arc::clone(&payload_budget);
        let second_accept = tokio::spawn(async move {
            let (stream, _) = listener.accept().await.expect("accept second client");
            handle_connection(
                stream,
                second_senders,
                second_claims,
                second_budget,
                TcpPeerAuthentication::UnauthenticatedTrustedNetwork {
                    explicit_allow: true,
                },
                "Alice",
                buffer_size,
                read_timeout,
            )
            .await
        });

        let _second_client = connect_and_claim_role(second_addr, "Bob").await;
        let err = tokio::time::timeout(Duration::from_secs(1), second_accept)
            .await
            .expect("duplicate role claim should finish promptly")
            .expect("duplicate handler task should not panic")
            .expect_err("duplicate role claim must fail");
        assert!(matches!(err, TcpTransportError::DuplicatePeer(role) if role == "Bob"));

        drop(first_client);
        tokio::time::timeout(Duration::from_secs(1), first_accept)
            .await
            .expect("first connection should close promptly")
            .expect("first handler task should not panic")
            .expect("first handler should close cleanly");
    }
}
