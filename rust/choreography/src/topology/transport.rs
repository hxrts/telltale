//! Transport trait and implementations for topology-aware communication.
//!
//! This module provides abstractions for different transport mechanisms:
//! - `InMemoryTransport`: In-process communication using channels
//! - `TcpTransport`: Network communication over TCP
//! - Discovery-based transports (Kubernetes, Consul)

use super::{Location, Topology, TopologyMode};
use async_trait::async_trait;
use std::collections::HashMap;
use std::sync::Arc;
use thiserror::Error;
use tokio::sync::{mpsc, Mutex};

/// Errors that can occur during transport operations.
#[derive(Debug, Error)]
pub enum TransportError {
    #[error("Connection failed: {0}")]
    ConnectionFailed(String),

    #[error("Send failed: {0}")]
    SendFailed(String),

    #[error("Receive failed: {0}")]
    ReceiveFailed(String),

    #[error("Timeout")]
    Timeout,

    #[error("Channel closed")]
    ChannelClosed,

    #[error("Unknown role: {0}")]
    UnknownRole(String),

    #[error("Transport not ready")]
    NotReady,

    #[error("IO error: {0}")]
    IoError(#[from] std::io::Error),
}

/// Result type for transport operations.
pub type TransportResult<T> = Result<T, TransportError>;

/// A message that can be sent over a transport.
pub trait TransportMessage: Send + Sync + 'static {
    /// Serialize the message to bytes.
    fn to_bytes(&self) -> Vec<u8>;

    /// Deserialize from bytes.
    fn from_bytes(bytes: &[u8]) -> Result<Self, String>
    where
        Self: Sized;
}

/// Simple byte message for basic transport.
#[derive(Debug, Clone)]
pub struct ByteMessage(pub Vec<u8>);

impl TransportMessage for ByteMessage {
    fn to_bytes(&self) -> Vec<u8> {
        self.0.clone()
    }

    fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
        Ok(ByteMessage(bytes.to_vec()))
    }
}

/// Transport trait for sending and receiving messages between roles.
#[async_trait]
pub trait Transport: Send + Sync + 'static {
    /// Send a message to a specific role.
    async fn send(&self, to_role: &str, message: Vec<u8>) -> TransportResult<()>;

    /// Receive a message from a specific role.
    async fn recv(&self, from_role: &str) -> TransportResult<Vec<u8>>;

    /// Check if the transport is connected to a role.
    fn is_connected(&self, role: &str) -> bool;

    /// Close the transport connection.
    async fn close(&self) -> TransportResult<()>;
}

/// In-memory transport using channels.
///
/// This is the default transport for local testing where all roles
/// run in the same process.
pub struct InMemoryChannelTransport {
    /// Role this transport belongs to.
    role: String,
    /// Sender channels to other roles (role -> sender).
    senders: Arc<Mutex<HashMap<String, mpsc::Sender<Vec<u8>>>>>,
    /// Receiver channels from other roles (role -> receiver).
    receivers: Arc<Mutex<HashMap<String, mpsc::Receiver<Vec<u8>>>>>,
}

impl InMemoryChannelTransport {
    /// Create a new in-memory transport for a role.
    pub fn new(role: impl Into<String>) -> Self {
        Self {
            role: role.into(),
            senders: Arc::new(Mutex::new(HashMap::new())),
            receivers: Arc::new(Mutex::new(HashMap::new())),
        }
    }

    /// Connect this transport to another role's transport.
    pub async fn connect(&self, other: &InMemoryChannelTransport) {
        let (tx1, rx1) = mpsc::channel(32);
        let (tx2, rx2) = mpsc::channel(32);

        // Self -> Other
        self.senders.lock().await.insert(other.role.clone(), tx1);
        other.receivers.lock().await.insert(self.role.clone(), rx1);

        // Other -> Self
        other.senders.lock().await.insert(self.role.clone(), tx2);
        self.receivers.lock().await.insert(other.role.clone(), rx2);
    }

    /// Get the role name.
    pub fn role(&self) -> &str {
        &self.role
    }
}

#[async_trait]
impl Transport for InMemoryChannelTransport {
    async fn send(&self, to_role: &str, message: Vec<u8>) -> TransportResult<()> {
        let senders = self.senders.lock().await;
        let sender = senders
            .get(to_role)
            .ok_or_else(|| TransportError::UnknownRole(to_role.to_string()))?;

        sender
            .send(message)
            .await
            .map_err(|_| TransportError::ChannelClosed)
    }

    async fn recv(&self, from_role: &str) -> TransportResult<Vec<u8>> {
        let mut receivers = self.receivers.lock().await;
        let receiver = receivers
            .get_mut(from_role)
            .ok_or_else(|| TransportError::UnknownRole(from_role.to_string()))?;

        receiver.recv().await.ok_or(TransportError::ChannelClosed)
    }

    fn is_connected(&self, _role: &str) -> bool {
        // For in-memory, assume always connected after setup
        // In production, this should check if we have a sender for this role
        true
    }

    async fn close(&self) -> TransportResult<()> {
        self.senders.lock().await.clear();
        self.receivers.lock().await.clear();
        Ok(())
    }
}

/// Factory for creating transports based on topology.
pub struct TransportFactory;

impl TransportFactory {
    /// Create a transport for a role based on the topology.
    pub fn create(topology: &Topology, role: &str) -> Box<dyn Transport> {
        match &topology.mode {
            Some(TopologyMode::Local) | None => Box::new(InMemoryChannelTransport::new(role)),
            Some(TopologyMode::PerRole) => {
                // For per-role mode, we'd use TCP but for now fall back to in-memory
                Box::new(InMemoryChannelTransport::new(role))
            }
            Some(TopologyMode::Kubernetes(_namespace)) => {
                // Placeholder: would use K8s service discovery
                Box::new(InMemoryChannelTransport::new(role))
            }
            Some(TopologyMode::Consul(_datacenter)) => {
                // Placeholder: would use Consul service discovery
                Box::new(InMemoryChannelTransport::new(role))
            }
        }
    }

    /// Select transport type based on location.
    pub fn transport_for_location(
        _from_role: &str,
        to_role: &str,
        topology: &Topology,
    ) -> TransportType {
        let location = topology.get_location(to_role);
        match location {
            Location::Local => TransportType::InMemory,
            Location::Colocated(_) => TransportType::SharedMemory,
            Location::Remote(_) => TransportType::Tcp,
        }
    }
}

/// Types of transport available.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TransportType {
    /// In-process channels.
    InMemory,
    /// Shared memory (for colocated roles).
    SharedMemory,
    /// TCP network transport.
    Tcp,
    /// WebSocket transport.
    WebSocket,
}

impl TransportType {
    /// Check if this transport type is local (no network).
    pub fn is_local(&self) -> bool {
        matches!(self, TransportType::InMemory | TransportType::SharedMemory)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_in_memory_transport() {
        let alice = InMemoryChannelTransport::new("Alice");
        let bob = InMemoryChannelTransport::new("Bob");

        alice.connect(&bob).await;

        // Alice sends to Bob
        alice.send("Bob", b"Hello Bob".to_vec()).await.unwrap();

        // Bob receives from Alice
        let msg = bob.recv("Alice").await.unwrap();
        assert_eq!(msg, b"Hello Bob".to_vec());

        // Bob sends to Alice
        bob.send("Alice", b"Hello Alice".to_vec()).await.unwrap();

        // Alice receives from Bob
        let msg = alice.recv("Bob").await.unwrap();
        assert_eq!(msg, b"Hello Alice".to_vec());
    }

    #[test]
    fn test_transport_type_for_location() {
        let topology = Topology::builder()
            .local_role("Alice")
            .remote_role("Bob", "localhost:8080")
            .colocated_role("Carol", "Alice")
            .build();

        assert_eq!(
            TransportFactory::transport_for_location("Alice", "Alice", &topology),
            TransportType::InMemory
        );
        assert_eq!(
            TransportFactory::transport_for_location("Alice", "Bob", &topology),
            TransportType::Tcp
        );
        assert_eq!(
            TransportFactory::transport_for_location("Alice", "Carol", &topology),
            TransportType::SharedMemory
        );
    }

    #[test]
    fn test_transport_type_is_local() {
        assert!(TransportType::InMemory.is_local());
        assert!(TransportType::SharedMemory.is_local());
        assert!(!TransportType::Tcp.is_local());
        assert!(!TransportType::WebSocket.is_local());
    }
}
