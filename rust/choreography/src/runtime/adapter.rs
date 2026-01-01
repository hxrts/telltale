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
//!     type Role = MyRole;
//!
//!     async fn send<M: Message>(&mut self, to: MyRole, msg: M) -> Result<(), Self::Error> {
//!         // Send implementation
//!     }
//!
//!     async fn recv<M: Message>(&mut self, from: MyRole) -> Result<M, Self::Error> {
//!         // Receive implementation
//!     }
//! }
//! ```

use async_trait::async_trait;
use serde::{de::DeserializeOwned, Deserialize, Serialize};
use std::fmt::Debug;

use crate::effects::{LabelId, RoleId};
use crate::identifiers::RoleName;

/// Trait for message types that can be sent/received in a choreography.
///
/// Messages must be serializable, deserializable, sendable between threads,
/// and debuggable for tracing purposes.
pub trait Message: Serialize + DeserializeOwned + Send + Sync + Debug + 'static {}

/// Blanket implementation for all types satisfying the bounds.
impl<T: Serialize + DeserializeOwned + Send + Sync + Debug + 'static> Message for T {}

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
    /// The role identifier type for this adapter.
    type Role: RoleId;

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
    async fn send<M: Message>(&mut self, to: Self::Role, msg: M) -> Result<(), Self::Error>;

    /// Receive a message from a specific role.
    ///
    /// # Arguments
    ///
    /// * `from` - The sender role
    ///
    /// # Returns
    ///
    /// The received message, or an error if receive fails.
    async fn recv<M: Message>(&mut self, from: Self::Role) -> Result<M, Self::Error>;

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
        to: &[Self::Role],
        msg: M,
    ) -> Result<(), Self::Error> {
        for role in to {
            self.send(*role, msg.clone()).await?;
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
    async fn collect<M: Message>(&mut self, from: &[Self::Role]) -> Result<Vec<M>, Self::Error> {
        let mut messages = Vec::with_capacity(from.len());
        for role in from {
            let msg = self.recv::<M>(*role).await?;
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
    async fn choose(
        &mut self,
        to: Self::Role,
        label: <Self::Role as RoleId>::Label,
    ) -> Result<(), Self::Error> {
        self.send(to, ChoiceLabel(label)).await
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
    async fn offer(
        &mut self,
        from: Self::Role,
    ) -> Result<<Self::Role as RoleId>::Label, Self::Error> {
        let choice: ChoiceLabel<<Self::Role as RoleId>::Label> = self.recv(from).await?;
        Ok(choice.0)
    }
}

/// A choice label message for internal/external choice communication.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ChoiceLabel<L: LabelId>(pub L);

impl<L: LabelId> Serialize for ChoiceLabel<L> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_str(self.0.as_str())
    }
}

impl<'de, L: LabelId> Deserialize<'de> for ChoiceLabel<L> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let label = String::deserialize(deserializer)?;
        L::from_str(&label)
            .map(ChoiceLabel)
            .ok_or_else(|| serde::de::Error::custom("Unknown choice label"))
    }
}

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
    pub role: RoleName,
    /// Optional role index for parameterized roles
    pub index: Option<u32>,
}

impl ProtocolContext {
    /// Create a new protocol context.
    #[must_use]
    pub fn new(protocol: &'static str, role: RoleName) -> Self {
        Self {
            protocol,
            role,
            index: None,
        }
    }

    /// Create a new indexed protocol context.
    #[must_use]
    pub fn indexed(protocol: &'static str, role: RoleName, index: u32) -> Self {
        Self {
            protocol,
            role,
            index: Some(index),
        }
    }

    /// Create a context from a role identifier.
    #[must_use]
    pub fn for_role<R: RoleId>(protocol: &'static str, role: R) -> Self {
        Self {
            protocol,
            role: role.role_name(),
            index: role.role_index(),
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
        #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
        enum TestRole {
            Client,
            Witness(u32),
        }

        #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
        enum TestLabel {
            Ping,
        }

        impl LabelId for TestLabel {
            fn as_str(&self) -> &'static str {
                match self {
                    TestLabel::Ping => "Ping",
                }
            }

            fn from_str(label: &str) -> Option<Self> {
                match label {
                    "Ping" => Some(TestLabel::Ping),
                    _ => None,
                }
            }
        }

        impl RoleId for TestRole {
            type Label = TestLabel;

            fn role_name(&self) -> RoleName {
                match self {
                    TestRole::Client => RoleName::from_static("Client"),
                    TestRole::Witness(_) => RoleName::from_static("Witness"),
                }
            }

            fn role_index(&self) -> Option<u32> {
                match self {
                    TestRole::Witness(index) => Some(*index),
                    _ => None,
                }
            }
        }

        let static_role = TestRole::Client;
        assert_eq!(
            static_role.role_name().as_str(),
            "Client"
        );

        let indexed_role = TestRole::Witness(2);
        assert_eq!(indexed_role.role_name().as_str(), "Witness");
        assert_eq!(indexed_role.role_index(), Some(2));
    }

    #[test]
    fn test_protocol_context() {
        let ctx = ProtocolContext::new("TwoBuyer", RoleName::from_static("Buyer1"));
        assert_eq!(ctx.protocol, "TwoBuyer");
        assert_eq!(ctx.role.as_str(), "Buyer1");
        assert!(ctx.index.is_none());

        let indexed_ctx =
            ProtocolContext::indexed("Broadcast", RoleName::from_static("Witness"), 0);
        assert_eq!(indexed_ctx.index, Some(0));
    }
}
