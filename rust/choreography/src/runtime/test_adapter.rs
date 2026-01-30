//! Test Adapter for Choreographic Protocols
//!
//! This module provides a simple in-memory adapter for testing choreographic protocols,
//! with full support for role families (wildcards and ranges).
//!
//! # Example
//!
//! ```ignore
//! use telltale_choreography::runtime::TestAdapter;
//!
//! // Define role and label types
//! #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
//! enum Role {
//!     Coordinator,
//!     Witness(u32),
//! }
//!
//! // Create adapter with role family configuration
//! let adapter = TestAdapter::new(Role::Coordinator)
//!     .with_family("Witness", vec![Role::Witness(0), Role::Witness(1), Role::Witness(2)]);
//!
//! // Now resolve_family("Witness") returns the configured instances
//! ```

use async_trait::async_trait;
use std::collections::HashMap;
use std::sync::{Arc, Mutex};

use super::adapter::{ChoiceLabel, ChoreographicAdapter, Message};
use crate::effects::{ChoreographyError, RoleId};

/// Message queue type: maps (from_role, to_role) pairs to queues of serialized messages.
type MessageQueues = HashMap<(String, String), Vec<Vec<u8>>>;

/// A test adapter for choreographic protocols with role family support.
///
/// This adapter stores messages in memory and supports role family resolution
/// for testing protocols with wildcards and ranges.
pub struct TestAdapter<R: RoleId> {
    /// The role this adapter represents
    role: R,
    /// Role families: family name -> list of role instances
    families: HashMap<String, Vec<R>>,
    /// Sent messages: (from, to) -> queue of serialized messages
    sent: Arc<Mutex<MessageQueues>>,
    /// Received messages: (from, to) -> queue of serialized messages
    received: Arc<Mutex<MessageQueues>>,
}

impl<R: RoleId> TestAdapter<R> {
    /// Create a new test adapter for the given role.
    pub fn new(role: R) -> Self {
        Self {
            role,
            families: HashMap::new(),
            sent: Arc::new(Mutex::new(HashMap::new())),
            received: Arc::new(Mutex::new(HashMap::new())),
        }
    }

    /// Configure a role family with the given instances.
    ///
    /// # Arguments
    ///
    /// * `name` - The family name (e.g., "Witness" for `Witness[*]`)
    /// * `instances` - The role instances in this family
    pub fn with_family(mut self, name: &str, instances: Vec<R>) -> Self {
        self.families.insert(name.to_string(), instances);
        self
    }

    /// Add a role family.
    pub fn add_family(&mut self, name: &str, instances: Vec<R>) {
        self.families.insert(name.to_string(), instances);
    }

    /// Get the role this adapter represents.
    pub fn role(&self) -> R {
        self.role
    }

    /// Get sent messages for inspection in tests.
    pub fn sent_messages(&self) -> MessageQueues {
        self.sent.lock().unwrap().clone()
    }

    /// Queue a message to be received (for test setup).
    pub fn queue_message(&self, from: R, to: R, message: Vec<u8>) {
        let key = (from.role_name().to_string(), to.role_name().to_string());
        let mut received = self.received.lock().unwrap();
        received.entry(key).or_default().push(message);
    }

    /// Queue a typed message to be received (for test setup).
    pub fn queue_typed_message<M: Message>(&self, from: R, to: R, message: M) {
        let bytes = bincode::serialize(&message).expect("serialization should succeed");
        self.queue_message(from, to, bytes);
    }

    /// Create a linked pair of adapters for two-party testing.
    ///
    /// Messages sent by one adapter can be received by the other.
    pub fn linked_pair(role_a: R, role_b: R) -> (Self, Self) {
        let shared_a_to_b = Arc::new(Mutex::new(HashMap::new()));
        let shared_b_to_a = Arc::new(Mutex::new(HashMap::new()));

        let adapter_a = Self {
            role: role_a,
            families: HashMap::new(),
            sent: shared_a_to_b.clone(),
            received: shared_b_to_a.clone(),
        };

        let adapter_b = Self {
            role: role_b,
            families: HashMap::new(),
            sent: shared_b_to_a,
            received: shared_a_to_b,
        };

        (adapter_a, adapter_b)
    }
}

/// Error type for TestAdapter operations.
#[derive(Debug, thiserror::Error)]
pub enum TestAdapterError {
    #[error("role family '{0}' not configured")]
    FamilyNotConfigured(String),

    #[error("invalid role range for '{family}': [{start}, {end})")]
    InvalidRange {
        family: String,
        start: u32,
        end: u32,
    },

    #[error("no message available from {from} to {to}")]
    NoMessageAvailable { from: String, to: String },

    #[error("serialization error: {0}")]
    Serialization(String),

    #[error("role family '{0}' resolved to empty set")]
    EmptyFamily(String),
}

impl From<TestAdapterError> for ChoreographyError {
    fn from(err: TestAdapterError) -> Self {
        match err {
            TestAdapterError::FamilyNotConfigured(name) => {
                ChoreographyError::RoleFamilyNotFound(name)
            }
            TestAdapterError::InvalidRange { family, start, end } => {
                ChoreographyError::InvalidRoleRange { family, start, end }
            }
            TestAdapterError::NoMessageAvailable { from, to } => {
                ChoreographyError::Transport(format!("no message from {} to {}", from, to))
            }
            TestAdapterError::Serialization(msg) => ChoreographyError::Serialization(msg),
            TestAdapterError::EmptyFamily(name) => ChoreographyError::EmptyRoleFamily(name),
        }
    }
}

#[async_trait]
impl<R: RoleId + 'static> ChoreographicAdapter for TestAdapter<R> {
    type Error = ChoreographyError;
    type Role = R;

    async fn send<M: Message>(&mut self, to: Self::Role, msg: M) -> Result<(), Self::Error> {
        let bytes = bincode::serialize(&msg)
            .map_err(|e| ChoreographyError::Serialization(e.to_string()))?;

        let key = (
            self.role.role_name().to_string(),
            to.role_name().to_string(),
        );
        let mut sent = self.sent.lock().unwrap();
        sent.entry(key).or_default().push(bytes);

        Ok(())
    }

    async fn recv<M: Message>(&mut self, from: Self::Role) -> Result<M, Self::Error> {
        let key = (
            from.role_name().to_string(),
            self.role.role_name().to_string(),
        );

        let bytes = {
            let mut received = self.received.lock().unwrap();
            let queue = received.entry(key.clone()).or_default();
            if queue.is_empty() {
                return Err(TestAdapterError::NoMessageAvailable {
                    from: key.0,
                    to: key.1,
                }
                .into());
            }
            queue.remove(0)
        };

        bincode::deserialize(&bytes).map_err(|e| ChoreographyError::Serialization(e.to_string()))
    }

    async fn choose(
        &mut self,
        to: Self::Role,
        label: <Self::Role as RoleId>::Label,
    ) -> Result<(), Self::Error> {
        self.send(to, ChoiceLabel(label)).await
    }

    async fn offer(
        &mut self,
        from: Self::Role,
    ) -> Result<<Self::Role as RoleId>::Label, Self::Error> {
        let choice: ChoiceLabel<<Self::Role as RoleId>::Label> = self.recv(from).await?;
        Ok(choice.0)
    }

    fn resolve_family(&self, family: &str) -> Result<Vec<Self::Role>, Self::Error> {
        self.families
            .get(family)
            .cloned()
            .ok_or_else(|| ChoreographyError::RoleFamilyNotFound(family.to_string()))
    }

    fn resolve_range(
        &self,
        family: &str,
        start: u32,
        end: u32,
    ) -> Result<Vec<Self::Role>, Self::Error> {
        let instances = self.resolve_family(family)?;

        if start >= end {
            return Err(ChoreographyError::InvalidRoleRange {
                family: family.to_string(),
                start,
                end,
            });
        }

        let start_idx = start as usize;
        let end_idx = (end as usize).min(instances.len());

        if start_idx >= instances.len() {
            return Err(ChoreographyError::InvalidRoleRange {
                family: family.to_string(),
                start,
                end,
            });
        }

        Ok(instances[start_idx..end_idx].to_vec())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::effects::LabelId;
    use crate::identifiers::RoleName;

    #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
    enum TestRole {
        Coordinator,
        Witness(u32),
    }

    #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
    enum TestLabel {
        Commit,
        Abort,
    }

    impl LabelId for TestLabel {
        fn as_str(&self) -> &'static str {
            match self {
                TestLabel::Commit => "Commit",
                TestLabel::Abort => "Abort",
            }
        }

        fn from_str(label: &str) -> Option<Self> {
            match label {
                "Commit" => Some(TestLabel::Commit),
                "Abort" => Some(TestLabel::Abort),
                _ => None,
            }
        }
    }

    impl RoleId for TestRole {
        type Label = TestLabel;

        fn role_name(&self) -> RoleName {
            match self {
                TestRole::Coordinator => RoleName::from_static("Coordinator"),
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

    #[test]
    fn test_resolve_family() {
        let adapter = TestAdapter::new(TestRole::Coordinator).with_family(
            "Witness",
            vec![
                TestRole::Witness(0),
                TestRole::Witness(1),
                TestRole::Witness(2),
            ],
        );

        let witnesses = adapter.resolve_family("Witness").unwrap();
        assert_eq!(witnesses.len(), 3);
        assert_eq!(witnesses[0], TestRole::Witness(0));
        assert_eq!(witnesses[1], TestRole::Witness(1));
        assert_eq!(witnesses[2], TestRole::Witness(2));
    }

    #[test]
    fn test_resolve_family_not_found() {
        let adapter = TestAdapter::new(TestRole::Coordinator);
        let result = adapter.resolve_family("Unknown");
        assert!(result.is_err());
    }

    #[test]
    fn test_resolve_range() {
        let adapter = TestAdapter::new(TestRole::Coordinator).with_family(
            "Witness",
            vec![
                TestRole::Witness(0),
                TestRole::Witness(1),
                TestRole::Witness(2),
                TestRole::Witness(3),
                TestRole::Witness(4),
            ],
        );

        let witnesses = adapter.resolve_range("Witness", 1, 4).unwrap();
        assert_eq!(witnesses.len(), 3);
        assert_eq!(witnesses[0], TestRole::Witness(1));
        assert_eq!(witnesses[1], TestRole::Witness(2));
        assert_eq!(witnesses[2], TestRole::Witness(3));
    }

    #[test]
    fn test_resolve_range_clamps_to_bounds() {
        let adapter = TestAdapter::new(TestRole::Coordinator).with_family(
            "Witness",
            vec![
                TestRole::Witness(0),
                TestRole::Witness(1),
                TestRole::Witness(2),
            ],
        );

        // Request range [1, 10) but only 3 elements exist
        let witnesses = adapter.resolve_range("Witness", 1, 10).unwrap();
        assert_eq!(witnesses.len(), 2);
        assert_eq!(witnesses[0], TestRole::Witness(1));
        assert_eq!(witnesses[1], TestRole::Witness(2));
    }

    #[test]
    fn test_resolve_range_invalid() {
        let adapter = TestAdapter::new(TestRole::Coordinator)
            .with_family("Witness", vec![TestRole::Witness(0)]);

        // Invalid: start >= end
        let result = adapter.resolve_range("Witness", 5, 3);
        assert!(result.is_err());

        // Invalid: start beyond bounds
        let result = adapter.resolve_range("Witness", 10, 15);
        assert!(result.is_err());
    }

    #[test]
    fn test_family_size() {
        let adapter = TestAdapter::new(TestRole::Coordinator).with_family(
            "Witness",
            vec![
                TestRole::Witness(0),
                TestRole::Witness(1),
                TestRole::Witness(2),
            ],
        );

        assert_eq!(adapter.family_size("Witness").unwrap(), 3);
    }

    #[tokio::test]
    async fn test_send_recv() {
        let (mut coordinator, mut witness) =
            TestAdapter::linked_pair(TestRole::Coordinator, TestRole::Witness(0));

        // Coordinator sends to Witness
        coordinator
            .send(TestRole::Witness(0), "hello".to_string())
            .await
            .unwrap();

        // Witness receives from Coordinator
        let msg: String = witness.recv(TestRole::Coordinator).await.unwrap();
        assert_eq!(msg, "hello");
    }

    #[tokio::test]
    async fn test_broadcast() {
        let mut adapter = TestAdapter::new(TestRole::Coordinator).with_family(
            "Witness",
            vec![
                TestRole::Witness(0),
                TestRole::Witness(1),
                TestRole::Witness(2),
            ],
        );

        let witnesses = adapter.resolve_family("Witness").unwrap();
        adapter
            .broadcast(&witnesses, "broadcast message".to_string())
            .await
            .unwrap();

        // Check that messages were sent to all witnesses
        let sent = adapter.sent_messages();
        let key = ("Coordinator".to_string(), "Witness".to_string());
        let messages = sent.get(&key).unwrap();
        assert_eq!(messages.len(), 3);
    }
}
