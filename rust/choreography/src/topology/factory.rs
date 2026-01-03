//! Transport factory trait and implementations.

use super::limits::CHANNEL_BUFFER_SIZE_DEFAULT;
use super::transport::{InMemoryChannelTransport, Transport, TransportError};
use crate::{QueueCapacity, RoleName};
use async_trait::async_trait;
use std::collections::HashMap;
use std::sync::Arc;

#[cfg(not(target_arch = "wasm32"))]
use tokio::sync::Mutex;

#[cfg(target_arch = "wasm32")]
use futures::lock::Mutex;

/// Factory for creating Transport instances.
///
/// Implementations of this trait provide different strategies for
/// creating transports based on role configuration.
#[async_trait]
pub trait TransportFactory: Send + Sync {
    /// Create a transport for the given role.
    ///
    /// The transport is configured and ready to use for sending
    /// and receiving messages.
    async fn create(&self, role: &RoleName) -> Result<Box<dyn Transport>, TransportError>;
}

/// Factory that creates in-memory channel transports.
///
/// All transports created by this factory are automatically connected
/// to each other, enabling in-process communication for testing.
#[derive(Debug)]
pub struct InMemoryTransportFactory {
    buffer_size: QueueCapacity,
    transports: Arc<Mutex<HashMap<RoleName, Arc<InMemoryChannelTransport>>>>,
}

impl InMemoryTransportFactory {
    /// Create a new factory with default buffer size.
    pub fn new() -> Self {
        Self {
            buffer_size: QueueCapacity::new(CHANNEL_BUFFER_SIZE_DEFAULT),
            transports: Arc::new(Mutex::new(HashMap::new())),
        }
    }

    /// Create a new factory with custom buffer size.
    pub fn with_buffer_size(buffer_size: QueueCapacity) -> Self {
        Self {
            buffer_size,
            transports: Arc::new(Mutex::new(HashMap::new())),
        }
    }

    /// Get or create a transport for a role.
    ///
    /// If a transport already exists for the role, it is returned.
    /// Otherwise, a new transport is created and connected to all
    /// existing transports.
    pub async fn get_or_create(&self, role: &RoleName) -> Arc<InMemoryChannelTransport> {
        let mut transports = self.transports.lock().await;

        if let Some(existing) = transports.get(role) {
            return existing.clone();
        }

        // Create new transport
        let transport = Arc::new(InMemoryChannelTransport::with_buffer_size(
            role.clone(),
            self.buffer_size,
        ));

        // Connect to all existing transports
        for (_other_role, other_transport) in transports.iter() {
            transport.connect(other_transport).await;
        }

        transports.insert(role.clone(), transport.clone());
        transport
    }

    /// Get all created transports.
    pub async fn transports(&self) -> HashMap<RoleName, Arc<InMemoryChannelTransport>> {
        self.transports.lock().await.clone()
    }

    /// Clear all transports.
    pub async fn clear(&self) {
        self.transports.lock().await.clear();
    }
}

impl Default for InMemoryTransportFactory {
    fn default() -> Self {
        Self::new()
    }
}

impl Clone for InMemoryTransportFactory {
    fn clone(&self) -> Self {
        Self {
            buffer_size: self.buffer_size,
            transports: Arc::clone(&self.transports),
        }
    }
}

#[async_trait]
impl TransportFactory for InMemoryTransportFactory {
    async fn create(&self, role: &RoleName) -> Result<Box<dyn Transport>, TransportError> {
        let transport = self.get_or_create(role).await;
        // Clone the Arc's contents to get an owned transport
        Ok(Box::new((*transport).clone()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::topology::Message;

    #[tokio::test]
    async fn test_in_memory_factory_creates_transport() {
        let factory = InMemoryTransportFactory::new();
        let transport = factory.create(&RoleName::from_static("Alice")).await.unwrap();
        assert!(transport.is_connected(&RoleName::from_static("Bob"))); // Always true for in-memory
    }

    #[tokio::test]
    async fn test_in_memory_factory_connects_transports() {
        let factory = InMemoryTransportFactory::new();

        let alice = factory.get_or_create(&RoleName::from_static("Alice")).await;
        let bob = factory.get_or_create(&RoleName::from_static("Bob")).await;

        // Send from Alice to Bob
        let msg = Message::new(b"Hello Bob".to_vec()).unwrap();
        alice.send(&RoleName::from_static("Bob"), msg).await.unwrap();

        // Receive at Bob
        let received = bob.recv(&RoleName::from_static("Alice")).await.unwrap();
        assert_eq!(received.as_bytes(), b"Hello Bob");
    }

    #[tokio::test]
    async fn test_in_memory_factory_custom_buffer_size() {
        let factory = InMemoryTransportFactory::with_buffer_size(QueueCapacity::new(64));
        let _transport = factory.create(&RoleName::from_static("Alice")).await.unwrap();
        // Buffer size is internal, just verify creation succeeds
    }

    #[tokio::test]
    async fn test_in_memory_factory_reuses_transport() {
        let factory = InMemoryTransportFactory::new();

        let t1 = factory.get_or_create(&RoleName::from_static("Alice")).await;
        let t2 = factory.get_or_create(&RoleName::from_static("Alice")).await;

        // Should be the same Arc
        assert!(Arc::ptr_eq(&t1, &t2));
    }

    #[tokio::test]
    async fn test_in_memory_factory_clear() {
        let factory = InMemoryTransportFactory::new();

        factory.get_or_create(&RoleName::from_static("Alice")).await;
        factory.get_or_create(&RoleName::from_static("Bob")).await;

        assert_eq!(factory.transports().await.len(), 2);

        factory.clear().await;

        assert!(factory.transports().await.is_empty());
    }

    #[tokio::test]
    async fn test_in_memory_factory_clone_shares_state() {
        let factory1 = InMemoryTransportFactory::new();
        let factory2 = factory1.clone();

        factory1.get_or_create(&RoleName::from_static("Alice")).await;

        // factory2 should see Alice's transport
        assert_eq!(factory2.transports().await.len(), 1);
    }
}
