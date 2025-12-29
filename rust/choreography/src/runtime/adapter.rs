//! Choreographic Adapter Trait
//!
//! This module provides the `ChoreographicAdapter` trait, a simplified interface
//! for executing choreographic protocols. Unlike `ChoreoHandler` which is designed
//! for the effect interpreter, `ChoreographicAdapter` is designed for direct use
//! by generated `run_{role}` functions.
//!
//! # Design Goals
//!
//! - Simpler interface than `ChoreoHandler` (no endpoint parameter threading)
//! - Generic over message types with `Message` trait bound
//! - Support for broadcast/collect patterns for indexed roles
//! - Easy integration with existing transport implementations
//!
//! # Example
//!
//! ```ignore
//! use rumpsteak_aura_choreography::runtime::ChoreographicAdapter;
//!
//! struct MyAdapter { /* ... */ }
//!
//! #[async_trait]
//! impl ChoreographicAdapter for MyAdapter {
//!     type Error = MyError;
//!
//!     async fn send<M: Message>(&mut self, to: RoleId, msg: M) -> Result<(), Self::Error> {
//!         // Send implementation
//!     }
//!
//!     async fn recv<M: Message>(&mut self, from: RoleId) -> Result<M, Self::Error> {
//!         // Receive implementation
//!     }
//! }
//! ```

use async_trait::async_trait;
use serde::{de::DeserializeOwned, Serialize};
use std::fmt::Debug;

/// Trait for message types that can be sent/received in a choreography.
///
/// Messages must be serializable, deserializable, sendable between threads,
/// and debuggable for tracing purposes.
pub trait Message: Serialize + DeserializeOwned + Send + Sync + Debug + 'static {}

/// Blanket implementation for all types satisfying the bounds.
impl<T: Serialize + DeserializeOwned + Send + Sync + Debug + 'static> Message for T {}

/// Role identifier for choreographic protocols.
///
/// This is a simplified role ID that can represent both static roles
/// and indexed roles (e.g., `Witness[0]`, `Worker[n]`).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RoleId {
    /// The base role name (e.g., "Witness", "Worker")
    pub name: &'static str,
    /// Optional index for parameterized roles
    pub index: Option<u32>,
}

impl RoleId {
    /// Create a new static (non-indexed) role.
    #[must_use]
    pub const fn new(name: &'static str) -> Self {
        Self { name, index: None }
    }

    /// Create a new indexed role.
    #[must_use]
    pub const fn indexed(name: &'static str, index: u32) -> Self {
        Self {
            name,
            index: Some(index),
        }
    }

    /// Check if this role has an index.
    #[must_use]
    pub const fn is_indexed(&self) -> bool {
        self.index.is_some()
    }
}

impl std::fmt::Display for RoleId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.index {
            Some(i) => write!(f, "{}[{}]", self.name, i),
            None => write!(f, "{}", self.name),
        }
    }
}

/// The core adapter trait for choreographic protocol execution.
///
/// This trait abstracts the communication primitives needed to execute
/// a choreographic protocol. Implementations can provide different
/// transport mechanisms (channels, network, simulated, etc.).
///
/// # Type Parameters
///
/// The trait is generic over the error type, allowing implementations
/// to use their own error types.
///
/// # Async Safety
///
/// All methods are async and the trait requires `Send`, making it
/// compatible with multi-threaded runtimes.
#[async_trait]
pub trait ChoreographicAdapter: Send {
    /// The error type for this adapter.
    type Error: std::error::Error + Send + Sync + 'static;

    /// Send a message to a specific role.
    ///
    /// # Arguments
    ///
    /// * `to` - The recipient role
    /// * `msg` - The message to send
    ///
    /// # Errors
    ///
    /// Returns an error if the send fails (transport error, serialization, etc.)
    async fn send<M: Message>(&mut self, to: RoleId, msg: M) -> Result<(), Self::Error>;

    /// Receive a message from a specific role.
    ///
    /// # Arguments
    ///
    /// * `from` - The sender role
    ///
    /// # Returns
    ///
    /// The received message, or an error if receive fails.
    async fn recv<M: Message>(&mut self, from: RoleId) -> Result<M, Self::Error>;

    /// Broadcast a message to multiple roles.
    ///
    /// Default implementation sends sequentially. Override for parallel sending.
    ///
    /// # Arguments
    ///
    /// * `to` - The recipient roles
    /// * `msg` - The message to send (cloned for each recipient)
    async fn broadcast<M: Message + Clone>(
        &mut self,
        to: &[RoleId],
        msg: M,
    ) -> Result<(), Self::Error> {
        for role in to {
            self.send(role.clone(), msg.clone()).await?;
        }
        Ok(())
    }

    /// Collect messages from multiple roles.
    ///
    /// Default implementation receives sequentially. Override for parallel receiving.
    ///
    /// # Arguments
    ///
    /// * `from` - The sender roles
    ///
    /// # Returns
    ///
    /// A vector of messages in the order of the `from` roles.
    async fn collect<M: Message>(&mut self, from: &[RoleId]) -> Result<Vec<M>, Self::Error> {
        let mut messages = Vec::with_capacity(from.len());
        for role in from {
            let msg = self.recv::<M>(role.clone()).await?;
            messages.push(msg);
        }
        Ok(messages)
    }

    /// Send a choice label to a role.
    ///
    /// Used for internal choice (Select) - the choosing role broadcasts
    /// which branch was selected.
    ///
    /// # Arguments
    ///
    /// * `to` - The role to inform of the choice
    /// * `label` - The selected branch label
    async fn choose(&mut self, to: RoleId, label: &str) -> Result<(), Self::Error> {
        self.send(to, ChoiceLabel(label.to_string())).await
    }

    /// Receive a choice label from a role.
    ///
    /// Used for external choice (Branch) - receive which branch the
    /// choosing role selected.
    ///
    /// # Arguments
    ///
    /// * `from` - The role that made the choice
    ///
    /// # Returns
    ///
    /// The label of the selected branch.
    async fn offer(&mut self, from: RoleId) -> Result<String, Self::Error> {
        let choice: ChoiceLabel = self.recv(from).await?;
        Ok(choice.0)
    }
}

/// A choice label message for internal/external choice communication.
#[derive(Debug, Clone, Serialize, serde::Deserialize)]
pub struct ChoiceLabel(pub String);

/// Extension trait for adapters with lifecycle management.
#[async_trait]
pub trait ChoreographicAdapterExt: ChoreographicAdapter {
    /// Called before protocol execution starts.
    async fn setup(&mut self) -> Result<(), Self::Error>;

    /// Called after protocol execution completes.
    async fn teardown(&mut self) -> Result<(), Self::Error>;
}

/// Context information passed to generated runner functions.
///
/// Contains metadata about the protocol and role being executed.
#[derive(Debug, Clone)]
pub struct ProtocolContext {
    /// Name of the protocol being executed
    pub protocol: &'static str,
    /// Name of the role being executed
    pub role: &'static str,
    /// Optional role index for parameterized roles
    pub index: Option<u32>,
}

impl ProtocolContext {
    /// Create a new protocol context.
    #[must_use]
    pub const fn new(protocol: &'static str, role: &'static str) -> Self {
        Self {
            protocol,
            role,
            index: None,
        }
    }

    /// Create a new indexed protocol context.
    #[must_use]
    pub const fn indexed(protocol: &'static str, role: &'static str, index: u32) -> Self {
        Self {
            protocol,
            role,
            index: Some(index),
        }
    }
}

/// Output from protocol execution.
///
/// Wraps the return value with optional metadata.
#[derive(Debug)]
pub struct ProtocolOutput<T> {
    /// The result value from protocol execution
    pub value: T,
    /// Optional execution metadata
    pub metadata: Option<ExecutionMetadata>,
}

impl<T> ProtocolOutput<T> {
    /// Create a new protocol output with just a value.
    pub fn new(value: T) -> Self {
        Self {
            value,
            metadata: None,
        }
    }

    /// Create a new protocol output with metadata.
    pub fn with_metadata(value: T, metadata: ExecutionMetadata) -> Self {
        Self {
            value,
            metadata: Some(metadata),
        }
    }
}

/// Metadata about protocol execution.
#[derive(Debug, Default)]
pub struct ExecutionMetadata {
    /// Number of messages sent
    pub messages_sent: usize,
    /// Number of messages received
    pub messages_received: usize,
    /// Execution duration in milliseconds
    pub duration_ms: Option<u64>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_role_id_display() {
        let static_role = RoleId::new("Client");
        assert_eq!(static_role.to_string(), "Client");

        let indexed_role = RoleId::indexed("Witness", 2);
        assert_eq!(indexed_role.to_string(), "Witness[2]");
    }

    #[test]
    fn test_protocol_context() {
        let ctx = ProtocolContext::new("TwoBuyer", "Buyer1");
        assert_eq!(ctx.protocol, "TwoBuyer");
        assert_eq!(ctx.role, "Buyer1");
        assert!(ctx.index.is_none());

        let indexed_ctx = ProtocolContext::indexed("Broadcast", "Witness", 0);
        assert_eq!(indexed_ctx.index, Some(0));
    }
}
