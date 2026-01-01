//! Transport trait and implementations for topology-aware communication.
//!
//! This module provides abstractions for different transport mechanisms:
//! - `InMemoryTransport`: In-process communication using channels
//! - `TcpTransport`: Network communication over TCP
//! - Discovery-based transports (Kubernetes, Consul)

use super::{Location, Topology, TopologyMode};
use crate::identifiers::RoleName;
use crate::runtime::sync::{mpsc, Mutex};
use crate::mutex_lock;
use async_trait::async_trait;
#[cfg(target_arch = "wasm32")]
use futures::{SinkExt, StreamExt};
use std::collections::HashMap;
use std::sync::Arc;
use thiserror::Error;

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
    UnknownRole(RoleName),

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
    async fn send(&self, to_role: &RoleName, message: Vec<u8>) -> TransportResult<()>;

    /// Receive a message from a specific role.
    async fn recv(&self, from_role: &RoleName) -> TransportResult<Vec<u8>>;

    /// Check if the transport is connected to a role.
    fn is_connected(&self, role: &RoleName) -> bool;

    /// Close the transport connection.
    async fn close(&self) -> TransportResult<()>;
}

/// In-memory transport using channels.
///
/// This is the default transport for local testing where all roles
/// run in the same process.
pub struct InMemoryChannelTransport {
    /// Role this transport belongs to.
    role: RoleName,
    /// Sender channels to other roles (role -> sender).
    senders: Arc<Mutex<HashMap<RoleName, mpsc::Sender<Vec<u8>>>>>,
    /// Receiver channels from other roles (role -> receiver).
    receivers: Arc<Mutex<HashMap<RoleName, mpsc::Receiver<Vec<u8>>>>>,
}

impl InMemoryChannelTransport {
    /// Create a new in-memory transport for a role.
    pub fn new(role: RoleName) -> Self {
        Self {
            role,
            senders: Arc::new(Mutex::new(HashMap::new())),
            receivers: Arc::new(Mutex::new(HashMap::new())),
        }
    }

    /// Connect this transport to another role's transport.
    pub async fn connect(&self, other: &InMemoryChannelTransport) {
        let (tx1, rx1) = mpsc::channel(32);
        let (tx2, rx2) = mpsc::channel(32);

        // Self -> Other
        mutex_lock!(self.senders).insert(other.role.clone(), tx1);
        mutex_lock!(other.receivers).insert(self.role.clone(), rx1);

        // Other -> Self
        mutex_lock!(other.senders).insert(self.role.clone(), tx2);
        mutex_lock!(self.receivers).insert(other.role.clone(), rx2);
    }

    /// Get the role name.
    pub fn role(&self) -> &RoleName {
        &self.role
    }
}

#[async_trait]
impl Transport for InMemoryChannelTransport {
    async fn send(&self, to_role: &RoleName, message: Vec<u8>) -> TransportResult<()> {
        #[cfg(not(target_arch = "wasm32"))]
        {
            let senders = mutex_lock!(self.senders);
            let sender = senders
                .get(to_role)
                .ok_or_else(|| TransportError::UnknownRole(to_role.clone()))?;

            sender
                .send(message)
                .await
                .map_err(|_| TransportError::ChannelClosed)
        }

        #[cfg(target_arch = "wasm32")]
        {
            // Clone the sender to release the lock before awaiting
            // futures::channel::mpsc::Sender is Clone
            let sender = {
                let senders = mutex_lock!(self.senders);
                senders
                    .get(to_role)
                    .cloned()
                    .ok_or_else(|| TransportError::UnknownRole(to_role.clone()))?
            };

            let mut sender = sender;
            sender
                .send(message)
                .await
                .map_err(|_| TransportError::ChannelClosed)
        }
    }

    async fn recv(&self, from_role: &RoleName) -> TransportResult<Vec<u8>> {
        #[cfg(not(target_arch = "wasm32"))]
        {
            let mut receivers = mutex_lock!(self.receivers);
            let receiver = receivers
                .get_mut(from_role)
                .ok_or_else(|| TransportError::UnknownRole(from_role.clone()))?;
            receiver.recv().await.ok_or(TransportError::ChannelClosed)
        }

        #[cfg(target_arch = "wasm32")]
        {
            // For WASM, we need to take the receiver out, use it, and put it back
            // to avoid holding the lock across the await
            let mut receiver = {
                let mut receivers = mutex_lock!(self.receivers);
                receivers
                    .remove(from_role)
                    .ok_or_else(|| TransportError::UnknownRole(from_role.clone()))?
            };

            let result = receiver.next().await;

            // Put the receiver back
            {
                let mut receivers = mutex_lock!(self.receivers);
                receivers.insert(from_role.clone(), receiver);
            }

            result.ok_or(TransportError::ChannelClosed)
        }
    }

    fn is_connected(&self, _role: &RoleName) -> bool {
        // For in-memory, assume always connected after setup
        // In production, this should check if we have a sender for this role
        true
    }

    async fn close(&self) -> TransportResult<()> {
        mutex_lock!(self.senders).clear();
        mutex_lock!(self.receivers).clear();
        Ok(())
    }
}

/// Factory for creating transports based on topology.
pub struct TransportFactory;

impl TransportFactory {
    /// Create a transport for a role based on the topology.
    pub fn create(topology: &Topology, role: &RoleName) -> Box<dyn Transport> {
        match &topology.mode {
            Some(TopologyMode::Local) | None => Box::new(InMemoryChannelTransport::new(role.clone())),
            Some(TopologyMode::PerRole) => {
                // For per-role mode, we'd use TCP but for now fall back to in-memory
                Box::new(InMemoryChannelTransport::new(role.clone()))
            }
            Some(TopologyMode::Kubernetes(_namespace)) => {
                // Placeholder: would use K8s service discovery
                Box::new(InMemoryChannelTransport::new(role.clone()))
            }
            Some(TopologyMode::Consul(_datacenter)) => {
                // Placeholder: would use Consul service discovery
                Box::new(InMemoryChannelTransport::new(role.clone()))
            }
        }
    }

    /// Select transport type based on location.
    pub fn transport_for_location(
        _from_role: &RoleName,
        to_role: &RoleName,
        topology: &Topology,
    ) -> Result<TransportType, super::TopologyError> {
        match topology.get_location(to_role)? {
            Location::Local => Ok(TransportType::InMemory),
            Location::Colocated(_) => Ok(TransportType::SharedMemory),
            Location::Remote(_) => Ok(TransportType::Tcp),
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
        let alice = InMemoryChannelTransport::new(RoleName::from_static("Alice"));
        let bob = InMemoryChannelTransport::new(RoleName::from_static("Bob"));

        alice.connect(&bob).await;

        // Alice sends to Bob
        alice
            .send(&RoleName::from_static("Bob"), b"Hello Bob".to_vec())
            .await
            .unwrap();

        // Bob receives from Alice
        let msg = bob.recv(&RoleName::from_static("Alice")).await.unwrap();
        assert_eq!(msg, b"Hello Bob".to_vec());

        // Bob sends to Alice
        bob.send(&RoleName::from_static("Alice"), b"Hello Alice".to_vec())
            .await
            .unwrap();

        // Alice receives from Bob
        let msg = alice.recv(&RoleName::from_static("Bob")).await.unwrap();
        assert_eq!(msg, b"Hello Alice".to_vec());
    }

    #[test]
    fn test_transport_type_for_location() {
        let topology = Topology::builder()
            .local_role(RoleName::from_static("Alice"))
            .remote_role(
                RoleName::from_static("Bob"),
                crate::identifiers::Endpoint::new("localhost:8080").unwrap(),
            )
            .colocated_role(
                RoleName::from_static("Carol"),
                RoleName::from_static("Alice"),
            )
            .build();

        assert_eq!(
            TransportFactory::transport_for_location(
                &RoleName::from_static("Alice"),
                &RoleName::from_static("Alice"),
                &topology
            )
            .unwrap(),
            TransportType::InMemory
        );
        assert_eq!(
            TransportFactory::transport_for_location(
                &RoleName::from_static("Alice"),
                &RoleName::from_static("Bob"),
                &topology
            )
            .unwrap(),
            TransportType::Tcp
        );
        assert_eq!(
            TransportFactory::transport_for_location(
                &RoleName::from_static("Alice"),
                &RoleName::from_static("Carol"),
                &topology
            )
            .unwrap(),
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
