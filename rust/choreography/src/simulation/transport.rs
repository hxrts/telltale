//! Simulated transport traits for protocol execution
//!
//! These traits abstract message transport for simulation and testing,
//! allowing custom delivery semantics (delays, reordering, failures).

use async_trait::async_trait;
use std::collections::{HashMap, VecDeque};
use std::sync::{Arc, Mutex};

use super::envelope::ProtocolEnvelope;
use crate::runtime::RoleId;

/// Type alias for the message queue storage shared between transports.
type MessageQueues = Arc<Mutex<HashMap<(String, String), VecDeque<ProtocolEnvelope>>>>;

/// Errors that can occur during transport operations.
#[derive(Debug, thiserror::Error)]
pub enum TransportError {
    /// The destination is not reachable.
    #[error("Destination unreachable: {0}")]
    Unreachable(String),

    /// No message available for receive.
    #[error("No message available from {0}")]
    NoMessage(String),

    /// The channel is closed.
    #[error("Channel closed")]
    ChannelClosed,

    /// Serialization/deserialization error.
    #[error("Serialization error: {0}")]
    Serialization(String),

    /// Timeout waiting for message.
    #[error("Timeout waiting for message")]
    Timeout,

    /// Generic transport error.
    #[error("Transport error: {0}")]
    Other(String),
}

/// Result type for transport operations.
pub type TransportResult<T> = Result<T, TransportError>;

/// Synchronous simulated transport trait.
///
/// This trait is used for step-by-step simulation where the simulator
/// controls message delivery timing.
pub trait SimulatedTransport: Send {
    /// Send a message to a destination.
    fn send(&mut self, to: RoleId, envelope: ProtocolEnvelope) -> TransportResult<()>;

    /// Receive a message from a source.
    ///
    /// Returns `Err(TransportError::NoMessage)` if no message is available.
    fn recv(&mut self, from: RoleId) -> TransportResult<ProtocolEnvelope>;

    /// Check if a message is available from a source without consuming it.
    fn peek(&self, from: RoleId) -> bool;

    /// Get all pending messages (for debugging/inspection).
    fn pending_messages(&self) -> Vec<&ProtocolEnvelope>;
}

/// Asynchronous simulated transport trait.
///
/// This trait is used for async protocol execution with simulated transport.
#[async_trait]
pub trait AsyncSimulatedTransport: Send + Sync {
    /// Send a message to a destination.
    async fn send(&mut self, to: RoleId, envelope: ProtocolEnvelope) -> TransportResult<()>;

    /// Receive a message from a source, waiting if necessary.
    async fn recv(&mut self, from: RoleId) -> TransportResult<ProtocolEnvelope>;

    /// Try to receive a message without blocking.
    fn try_recv(&mut self, from: RoleId) -> TransportResult<Option<ProtocolEnvelope>>;

    /// Check if a message is available from a source.
    fn has_message(&self, from: RoleId) -> bool;
}

/// In-memory transport for testing.
///
/// Messages are delivered in FIFO order per sender-receiver pair.
#[derive(Debug, Default)]
pub struct InMemoryTransport {
    /// Current role using this transport.
    role: Option<RoleId>,
    /// Message queues: (from_role, to_role) -> queue.
    queues: MessageQueues,
}

impl InMemoryTransport {
    /// Create a new in-memory transport.
    #[must_use]
    pub fn new() -> Self {
        Self {
            role: None,
            queues: Arc::new(Mutex::new(HashMap::new())),
        }
    }

    /// Create a new transport with shared queues.
    ///
    /// Multiple transports sharing queues can communicate with each other.
    #[must_use]
    pub fn with_shared_queues(queues: MessageQueues) -> Self {
        Self { role: None, queues }
    }

    /// Set the role for this transport.
    pub fn set_role(&mut self, role: RoleId) {
        self.role = Some(role);
    }

    /// Get the current role.
    #[must_use]
    pub fn role(&self) -> Option<&RoleId> {
        self.role.as_ref()
    }

    /// Get the queue key for a sender-receiver pair.
    fn queue_key(from: &RoleId, to: &RoleId) -> (String, String) {
        (from.to_string(), to.to_string())
    }

    /// Get all messages in transit (for debugging).
    #[must_use]
    pub fn all_messages(&self) -> Vec<ProtocolEnvelope> {
        let queues = self.queues.lock().unwrap();
        queues.values().flatten().cloned().collect()
    }

    /// Clear all message queues.
    pub fn clear(&mut self) {
        let mut queues = self.queues.lock().unwrap();
        queues.clear();
    }

    /// Get the number of pending messages.
    #[must_use]
    pub fn pending_count(&self) -> usize {
        let queues = self.queues.lock().unwrap();
        queues.values().map(|q| q.len()).sum()
    }
}

impl Clone for InMemoryTransport {
    fn clone(&self) -> Self {
        Self {
            role: self.role.clone(),
            queues: Arc::clone(&self.queues),
        }
    }
}

impl SimulatedTransport for InMemoryTransport {
    fn send(&mut self, to: RoleId, envelope: ProtocolEnvelope) -> TransportResult<()> {
        let from = self
            .role
            .as_ref()
            .ok_or_else(|| TransportError::Other("Role not set".to_string()))?;
        let key = Self::queue_key(from, &to);

        let mut queues = self.queues.lock().unwrap();
        queues.entry(key).or_default().push_back(envelope);
        Ok(())
    }

    fn recv(&mut self, from: RoleId) -> TransportResult<ProtocolEnvelope> {
        let to = self
            .role
            .as_ref()
            .ok_or_else(|| TransportError::Other("Role not set".to_string()))?;
        let key = Self::queue_key(&from, to);

        let mut queues = self.queues.lock().unwrap();
        queues
            .get_mut(&key)
            .and_then(|q| q.pop_front())
            .ok_or_else(|| TransportError::NoMessage(from.to_string()))
    }

    fn peek(&self, from: RoleId) -> bool {
        let Some(to) = self.role.as_ref() else {
            return false;
        };
        let key = Self::queue_key(&from, to);

        let queues = self.queues.lock().unwrap();
        queues.get(&key).is_some_and(|q| !q.is_empty())
    }

    fn pending_messages(&self) -> Vec<&ProtocolEnvelope> {
        // Note: Can't return references with Mutex, so return empty
        // Use all_messages() for owned values instead
        Vec::new()
    }
}

#[async_trait]
impl AsyncSimulatedTransport for InMemoryTransport {
    async fn send(&mut self, to: RoleId, envelope: ProtocolEnvelope) -> TransportResult<()> {
        SimulatedTransport::send(self, to, envelope)
    }

    async fn recv(&mut self, from: RoleId) -> TransportResult<ProtocolEnvelope> {
        // In a real implementation, this would wait for a message.
        // For now, just try immediately.
        SimulatedTransport::recv(self, from)
    }

    fn try_recv(&mut self, from: RoleId) -> TransportResult<Option<ProtocolEnvelope>> {
        match SimulatedTransport::recv(self, from) {
            Ok(env) => Ok(Some(env)),
            Err(TransportError::NoMessage(_)) => Ok(None),
            Err(e) => Err(e),
        }
    }

    fn has_message(&self, from: RoleId) -> bool {
        self.peek(from)
    }
}

/// A transport wrapper that can inject delays and failures.
pub struct FaultyTransport<T> {
    inner: T,
    /// Drop probability (0.0 to 1.0).
    drop_rate: f64,
    /// Whether to delay messages.
    delay: bool,
    /// Random seed for reproducibility.
    seed: u64,
    /// Current random state.
    rng_state: u64,
}

impl<T> FaultyTransport<T> {
    /// Create a new faulty transport wrapper.
    pub fn new(inner: T) -> Self {
        Self {
            inner,
            drop_rate: 0.0,
            delay: false,
            seed: 12345,
            rng_state: 12345,
        }
    }

    /// Set the message drop rate (0.0 to 1.0).
    pub fn with_drop_rate(mut self, rate: f64) -> Self {
        self.drop_rate = rate.clamp(0.0, 1.0);
        self
    }

    /// Enable random delays.
    pub fn with_delays(mut self) -> Self {
        self.delay = true;
        self
    }

    /// Set the random seed for reproducibility.
    pub fn with_seed(mut self, seed: u64) -> Self {
        self.seed = seed;
        self.rng_state = seed;
        self
    }

    /// Get a random float between 0 and 1.
    fn random_float(&mut self) -> f64 {
        // Simple xorshift for reproducibility
        self.rng_state ^= self.rng_state << 13;
        self.rng_state ^= self.rng_state >> 7;
        self.rng_state ^= self.rng_state << 17;
        (self.rng_state as f64) / (u64::MAX as f64)
    }

    /// Check if message should be dropped.
    fn should_drop(&mut self) -> bool {
        self.random_float() < self.drop_rate
    }
}

impl<T: SimulatedTransport> SimulatedTransport for FaultyTransport<T> {
    fn send(&mut self, to: RoleId, envelope: ProtocolEnvelope) -> TransportResult<()> {
        if self.should_drop() {
            // Silently drop the message
            return Ok(());
        }
        self.inner.send(to, envelope)
    }

    fn recv(&mut self, from: RoleId) -> TransportResult<ProtocolEnvelope> {
        self.inner.recv(from)
    }

    fn peek(&self, from: RoleId) -> bool {
        self.inner.peek(from)
    }

    fn pending_messages(&self) -> Vec<&ProtocolEnvelope> {
        self.inner.pending_messages()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_envelope(from: &str, to: &str) -> ProtocolEnvelope {
        ProtocolEnvelope::builder()
            .protocol("Test")
            .sender(from)
            .recipient(to)
            .message_type("Msg")
            .payload(vec![1, 2, 3])
            .build()
            .unwrap()
    }

    #[test]
    fn test_in_memory_transport() {
        let queues = Arc::new(Mutex::new(HashMap::new()));

        let mut client = InMemoryTransport::with_shared_queues(Arc::clone(&queues));
        client.set_role(RoleId::new("Client"));

        let mut server = InMemoryTransport::with_shared_queues(Arc::clone(&queues));
        server.set_role(RoleId::new("Server"));

        // Client sends to server (use explicit trait method)
        let env = make_envelope("Client", "Server");
        SimulatedTransport::send(&mut client, RoleId::new("Server"), env).unwrap();

        // Server receives
        assert!(server.peek(RoleId::new("Client")));
        let received = SimulatedTransport::recv(&mut server, RoleId::new("Client")).unwrap();
        assert_eq!(received.from_role, "Client");
        assert_eq!(received.to_role, "Server");
    }

    #[test]
    fn test_no_message_error() {
        let mut transport = InMemoryTransport::new();
        transport.set_role(RoleId::new("Client"));

        let result = SimulatedTransport::recv(&mut transport, RoleId::new("Server"));
        assert!(matches!(result, Err(TransportError::NoMessage(_))));
    }

    #[test]
    fn test_faulty_transport_drops() {
        let inner = InMemoryTransport::new();
        let mut faulty = FaultyTransport::new(inner)
            .with_drop_rate(1.0) // Always drop
            .with_seed(42);

        faulty.inner.set_role(RoleId::new("Client"));

        let env = make_envelope("Client", "Server");
        faulty.send(RoleId::new("Server"), env).unwrap();

        // Message should be dropped, so pending count should be 0
        assert_eq!(faulty.inner.pending_count(), 0);
    }
}
