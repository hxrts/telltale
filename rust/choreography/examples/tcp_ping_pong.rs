//! TCP Transport Example for Telltale
//!
//! This example demonstrates how to implement the `Transport` trait over TCP
//! for real network communication between session-typed roles.
//!
//! ## Architecture
//!
//! Each role runs in its own process/task with a TCP server listening for
//! incoming connections and TCP clients connecting to peer roles.
//!
//! ```text
//! ┌─────────────────┐         TCP          ┌─────────────────┐
//! │     Alice       │ ◄──────────────────► │      Bob        │
//! │  (localhost:    │                      │  (localhost:    │
//! │   8080)         │                      │   8081)         │
//! └─────────────────┘                      └─────────────────┘
//! ```
//!
//! ## Running
//!
//! This example runs both roles in the same process for simplicity.
//! In production, each role would run in a separate process:
//!
//! ```bash
//! # Terminal 1: Run Alice
//! ROLE=Alice ALICE_ADDR=127.0.0.1:8080 BOB_ADDR=127.0.0.1:8081 cargo run --example tcp_ping_pong
//!
//! # Terminal 2: Run Bob
//! ROLE=Bob ALICE_ADDR=127.0.0.1:8080 BOB_ADDR=127.0.0.1:8081 cargo run --example tcp_ping_pong
//! ```
//!
//! ## Message Framing
//!
//! Messages are framed with a simple length-prefix protocol:
//! - 4 bytes: message length (big-endian u32)
//! - N bytes: message payload

use async_trait::async_trait;
use std::collections::HashMap;
use std::sync::Arc;
use telltale_choreography::{
    topology::{Transport, TransportError, TransportResult},
    RoleName,
};
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::{TcpListener, TcpStream};
use tokio::sync::{mpsc, Mutex, RwLock};

// ============================================================================
// TCP Transport Implementation
// ============================================================================

/// A TCP-based transport for inter-process communication.
///
/// This transport:
/// - Listens for incoming connections on a local address
/// - Connects to peer roles at their configured addresses
/// - Uses length-prefixed framing for messages
/// - Maintains persistent connections with automatic reconnection
pub struct TcpTransport {
    /// This role's name
    role: RoleName,
    /// Address this role listens on
    listen_addr: String,
    /// Map of role names to their addresses
    peer_addrs: HashMap<RoleName, String>,
    /// Outgoing connections (role -> stream)
    outgoing: Arc<RwLock<HashMap<RoleName, Arc<Mutex<TcpStream>>>>>,
    /// Incoming message queues (role -> receiver)
    incoming: Arc<Mutex<HashMap<RoleName, mpsc::Receiver<Vec<u8>>>>>,
    /// Senders for incoming messages (used by accept loop)
    incoming_senders: Arc<Mutex<HashMap<RoleName, mpsc::Sender<Vec<u8>>>>>,
    /// Shutdown signal
    shutdown: Arc<Mutex<Option<tokio::sync::oneshot::Sender<()>>>>,
}

impl TcpTransport {
    /// Create a new TCP transport.
    ///
    /// # Arguments
    ///
    /// * `role` - Name of this role
    /// * `listen_addr` - Address to listen for incoming connections
    /// * `peer_addrs` - Map of peer role names to their addresses
    pub fn new(
        role: RoleName,
        listen_addr: impl Into<String>,
        peer_addrs: HashMap<RoleName, String>,
    ) -> Self {
        Self {
            role,
            listen_addr: listen_addr.into(),
            peer_addrs,
            outgoing: Arc::new(RwLock::new(HashMap::new())),
            incoming: Arc::new(Mutex::new(HashMap::new())),
            incoming_senders: Arc::new(Mutex::new(HashMap::new())),
            shutdown: Arc::new(Mutex::new(None)),
        }
    }

    /// Start the transport (begin listening and accepting connections).
    pub async fn start(&self) -> TransportResult<()> {
        let listener = TcpListener::bind(&self.listen_addr)
            .await
            .map_err(|e| TransportError::ConnectionFailed(e.to_string()))?;

        println!("[{}] Listening on {}", self.role, self.listen_addr);

        let (shutdown_tx, mut shutdown_rx) = tokio::sync::oneshot::channel();
        *self.shutdown.lock().await = Some(shutdown_tx);

        let incoming_senders = Arc::clone(&self.incoming_senders);
        let role = self.role.clone();

        // Spawn accept loop
        tokio::spawn(async move {
            // Forever loop: exits via shutdown_rx signal
            loop {
                tokio::select! {
                    accept_result = listener.accept() => {
                        match accept_result {
                            Ok((stream, addr)) => {
                                println!("[{}] Accepted connection from {}", role, addr);
                                let senders = Arc::clone(&incoming_senders);
                                let role_name = role.clone();
                                tokio::spawn(async move {
                                    if let Err(e) = handle_incoming_connection(stream, senders, &role_name).await {
                                        eprintln!("[{}] Connection handler error: {}", role_name, e);
                                    }
                                });
                            }
                            Err(e) => {
                                eprintln!("[{}] Accept error: {}", role, e);
                            }
                        }
                    }
                    _ = &mut shutdown_rx => {
                        println!("[{}] Shutting down listener", role);
                        break;
                    }
                }
            }
        });

        // Initialize incoming channels for each peer
        for peer in self.peer_addrs.keys() {
            let (tx, rx) = mpsc::channel(32);
            self.incoming_senders.lock().await.insert(peer.clone(), tx);
            self.incoming.lock().await.insert(peer.clone(), rx);
        }

        Ok(())
    }

    /// Connect to a peer role.
    pub async fn connect_to(&self, peer_role: &RoleName) -> TransportResult<()> {
        let addr = self
            .peer_addrs
            .get(peer_role)
            .ok_or_else(|| TransportError::UnknownRole(peer_role.clone()))?;

        // Retry connection with backoff
        let mut attempts = 0;
        let max_attempts = 5;
        let mut delay = std::time::Duration::from_millis(100);

        // BOUND: exits on success or when attempts >= max_attempts (5)
        loop {
            match TcpStream::connect(addr).await {
                Ok(mut stream) => {
                    // Send our role name so the peer knows who connected
                    let role_bytes = self.role.as_str().as_bytes();
                    let len = role_bytes.len() as u32;
                    stream.write_all(&len.to_be_bytes()).await?;
                    stream.write_all(role_bytes).await?;
                    stream.flush().await?;

                    println!("[{}] Connected to {} at {}", self.role, peer_role, addr);
                    self.outgoing
                        .write()
                        .await
                        .insert(peer_role.clone(), Arc::new(Mutex::new(stream)));
                    return Ok(());
                }
                Err(e) => {
                    attempts += 1;
                    if attempts >= max_attempts {
                        return Err(TransportError::ConnectionFailed(format!(
                            "Failed to connect to {} after {} attempts: {}",
                            peer_role, attempts, e
                        )));
                    }
                    println!(
                        "[{}] Connection to {} failed, retrying in {:?}...",
                        self.role, peer_role, delay
                    );
                    tokio::time::sleep(delay).await;
                    delay *= 2; // Exponential backoff
                }
            }
        }
    }

    /// Get the role name.
    pub fn role(&self) -> &RoleName {
        &self.role
    }
}

/// Handle an incoming TCP connection.
async fn handle_incoming_connection(
    mut stream: TcpStream,
    senders: Arc<Mutex<HashMap<RoleName, mpsc::Sender<Vec<u8>>>>>,
    local_role: &RoleName,
) -> TransportResult<()> {
    // First, read the peer's role name
    let mut len_buf = [0u8; 4];
    stream.read_exact(&mut len_buf).await?;
    let len = u32::from_be_bytes(len_buf) as usize;

    let mut role_buf = vec![0u8; len];
    stream.read_exact(&mut role_buf).await?;
    let peer_role = String::from_utf8(role_buf)
        .map_err(|e| TransportError::ReceiveFailed(format!("Invalid role name: {}", e)))?;
    let peer_role = RoleName::new(peer_role)
        .map_err(|e| TransportError::ReceiveFailed(format!("Invalid role name: {}", e)))?;

    println!("[{}] Identified peer as: {}", local_role, peer_role);

    // Forever loop: reads messages until connection closed (EOF) or error
    loop {
        // Read message length
        let mut len_buf = [0u8; 4];
        match stream.read_exact(&mut len_buf).await {
            Ok(_) => {}
            Err(e) if e.kind() == std::io::ErrorKind::UnexpectedEof => {
                println!("[{}] Connection closed by {}", local_role, peer_role);
                break;
            }
            Err(e) => return Err(e.into()),
        }
        let len = u32::from_be_bytes(len_buf) as usize;

        // Read message payload
        let mut payload = vec![0u8; len];
        stream.read_exact(&mut payload).await?;

        // Forward to the appropriate channel
        let senders = senders.lock().await;
        if let Some(sender) = senders.get(&peer_role) {
            if sender.send(payload).await.is_err() {
                println!("[{}] Receiver dropped for {}", local_role, peer_role);
                break;
            }
        } else {
            eprintln!("[{}] No channel for peer: {}", local_role, peer_role);
        }
    }

    Ok(())
}

#[async_trait]
impl Transport for TcpTransport {
    async fn send(&self, to_role: &RoleName, message: Vec<u8>) -> TransportResult<()> {
        let outgoing = self.outgoing.read().await;
        let stream = outgoing
            .get(to_role)
            .ok_or_else(|| TransportError::UnknownRole(to_role.clone()))?;

        let mut stream = stream.lock().await;

        // Write length prefix
        let len = message.len() as u32;
        stream.write_all(&len.to_be_bytes()).await?;

        // Write payload
        stream.write_all(&message).await?;
        stream.flush().await?;

        Ok(())
    }

    async fn recv(&self, from_role: &RoleName) -> TransportResult<Vec<u8>> {
        let mut incoming = self.incoming.lock().await;
        let receiver = incoming
            .get_mut(from_role)
            .ok_or_else(|| TransportError::UnknownRole(from_role.clone()))?;

        receiver.recv().await.ok_or(TransportError::ChannelClosed)
    }

    fn is_connected(&self, role: &RoleName) -> bool {
        // Check if we have an outgoing connection
        // Note: This is a sync method, so we can't await here
        // In a real impl, you'd track connection state separately
        self.peer_addrs.contains_key(role)
    }

    async fn close(&self) -> TransportResult<()> {
        // Send shutdown signal - ignore send failure since receiver may already be dropped
        if let Some(shutdown) = self.shutdown.lock().await.take() {
            let _ = shutdown.send(());
        }

        // Close all outgoing connections
        let mut outgoing = self.outgoing.write().await;
        outgoing.clear();

        Ok(())
    }
}

// ============================================================================
// Ping-Pong Protocol Implementation
// ============================================================================

/// Simple message type for our protocol.
#[derive(Debug, Clone)]
enum Message {
    Ping(u32),
    Pong(u32),
}

impl Message {
    fn to_bytes(&self) -> Vec<u8> {
        match self {
            Message::Ping(n) => {
                let mut buf = vec![0u8]; // Tag for Ping
                buf.extend_from_slice(&n.to_be_bytes());
                buf
            }
            Message::Pong(n) => {
                let mut buf = vec![1u8]; // Tag for Pong
                buf.extend_from_slice(&n.to_be_bytes());
                buf
            }
        }
    }

    fn from_bytes(bytes: &[u8]) -> Option<Self> {
        if bytes.is_empty() {
            return None;
        }
        let tag = bytes[0];
        let n = u32::from_be_bytes(bytes[1..5].try_into().ok()?);
        match tag {
            0 => Some(Message::Ping(n)),
            1 => Some(Message::Pong(n)),
            _ => None,
        }
    }
}

/// Run Alice's role (sends pings, receives pongs).
async fn run_alice(transport: Arc<TcpTransport>) -> TransportResult<()> {
    println!("\n[Alice] Starting ping-pong...\n");
    let bob = RoleName::from_static("Bob");

    for i in 1..=5 {
        // Send Ping
        let ping = Message::Ping(i);
        println!("[Alice] Sending: {:?}", ping);
        transport.send(&bob, ping.to_bytes()).await?;

        // Receive Pong
        let bytes = transport.recv(&bob).await?;
        let pong = Message::from_bytes(&bytes).expect("Invalid message");
        println!("[Alice] Received: {:?}", pong);

        tokio::time::sleep(std::time::Duration::from_millis(500)).await;
    }

    println!("\n[Alice] Done!");
    Ok(())
}

/// Run Bob's role (receives pings, sends pongs).
async fn run_bob(transport: Arc<TcpTransport>) -> TransportResult<()> {
    println!("\n[Bob] Waiting for pings...\n");
    let alice = RoleName::from_static("Alice");

    for _ in 1..=5 {
        // Receive Ping
        let bytes = transport.recv(&alice).await?;
        let ping = Message::from_bytes(&bytes).expect("Invalid message");
        println!("[Bob] Received: {:?}", ping);

        // Send Pong
        if let Message::Ping(n) = ping {
            let pong = Message::Pong(n);
            println!("[Bob] Sending: {:?}", pong);
            transport.send(&alice, pong.to_bytes()).await?;
        }
    }

    println!("\n[Bob] Done!");
    Ok(())
}

// ============================================================================
// Main
// ============================================================================

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== TCP Transport Example ===\n");
    println!("This example demonstrates implementing the Transport trait over TCP.\n");

    // Configuration
    let alice_addr = "127.0.0.1:18080";
    let bob_addr = "127.0.0.1:18081";
    let alice_role = RoleName::from_static("Alice");
    let bob_role = RoleName::from_static("Bob");

    // Create transports for both roles
    let alice_transport = Arc::new(TcpTransport::new(
        alice_role.clone(),
        alice_addr,
        HashMap::from([(bob_role.clone(), bob_addr.to_string())]),
    ));

    let bob_transport = Arc::new(TcpTransport::new(
        bob_role.clone(),
        bob_addr,
        HashMap::from([(alice_role.clone(), alice_addr.to_string())]),
    ));

    // Start both transports (begin listening)
    alice_transport.start().await?;
    bob_transport.start().await?;

    // Small delay to ensure listeners are ready
    tokio::time::sleep(std::time::Duration::from_millis(100)).await;

    // Establish connections
    // Alice connects to Bob
    alice_transport.connect_to(&bob_role).await?;
    // Bob connects to Alice
    bob_transport.connect_to(&alice_role).await?;

    // Small delay for connections to stabilize
    tokio::time::sleep(std::time::Duration::from_millis(100)).await;

    // Run the protocol
    let alice = {
        let transport = Arc::clone(&alice_transport);
        tokio::spawn(async move { run_alice(transport).await })
    };

    let bob = {
        let transport = Arc::clone(&bob_transport);
        tokio::spawn(async move { run_bob(transport).await })
    };

    // Wait for both to complete
    let (alice_result, bob_result) = tokio::join!(alice, bob);
    alice_result??;
    bob_result??;

    // Cleanup
    alice_transport.close().await?;
    bob_transport.close().await?;

    println!("\n=== Example Complete ===");
    println!("\nKey takeaways:");
    println!("1. Implement the Transport trait for your network protocol");
    println!("2. Use length-prefixed framing for reliable message boundaries");
    println!("3. Handle connection setup before running the session protocol");
    println!("4. The same Transport trait works for in-memory (testing) and TCP (production)");

    Ok(())
}
