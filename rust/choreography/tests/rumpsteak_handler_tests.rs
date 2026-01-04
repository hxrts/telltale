//! Tests for RumpsteakHandler and RumpsteakEndpoint correctness.
//!
//! Verifies:
//! - Session metadata progression (operation_count, state_description, is_complete)
//! - Channel registration and overwrite semantics
//! - SimpleChannel and dynamic session operation
//! - Missing channel error handling
//! - Drop cleanup behavior

#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

use rumpsteak_aura::Message;
use rumpsteak_aura_choreography::effects::{
    handlers::rumpsteak::{RumpsteakEndpoint, RumpsteakHandler, SimpleChannel},
    ChoreoHandler, LabelId, RoleId,
};
use rumpsteak_aura_choreography::RoleName;
use serde::{Deserialize, Serialize};
use std::fmt::Debug;
use std::hash::Hash;

// ============================================================================
// Test Role Setup
// ============================================================================

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum TestRole {
    Alice,
    Bob,
    Charlie,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum ChoiceLabel {
    Accept,
    Option1,
    Default,
}

impl LabelId for ChoiceLabel {
    fn as_str(&self) -> &'static str {
        match self {
            ChoiceLabel::Accept => "Accept",
            ChoiceLabel::Option1 => "Option1",
            ChoiceLabel::Default => "default",
        }
    }

    fn from_str(label: &str) -> Option<Self> {
        match label {
            "Accept" => Some(ChoiceLabel::Accept),
            "Option1" => Some(ChoiceLabel::Option1),
            "default" => Some(ChoiceLabel::Default),
            _ => None,
        }
    }
}

impl RoleId for TestRole {
    type Label = ChoiceLabel;

    fn role_name(&self) -> RoleName {
        match self {
            TestRole::Alice => RoleName::from_static("Alice"),
            TestRole::Bob => RoleName::from_static("Bob"),
            TestRole::Charlie => RoleName::from_static("Charlie"),
        }
    }
}

// Implement Role trait for TestRole
impl rumpsteak_aura::Role for TestRole {
    type Message = TestLabel;

    fn seal(&mut self) {
        // No-op for test role
    }

    fn is_sealed(&self) -> bool {
        false
    }
}

#[derive(Debug)]
enum TestLabel {
    Msg(TestMessage),
}

impl Message<Box<dyn std::any::Any + Send>> for TestLabel {
    fn upcast(msg: Box<dyn std::any::Any + Send>) -> Self {
        TestLabel::Msg(*msg.downcast::<TestMessage>().unwrap())
    }

    fn downcast(self) -> Result<Box<dyn std::any::Any + Send>, Self> {
        match self {
            TestLabel::Msg(m) => Ok(Box::new(m)),
        }
    }
}

// ============================================================================
// Test Message Types
// ============================================================================

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
struct TestMessage {
    value: i32,
}

// ============================================================================
// SimpleChannel Tests
// ============================================================================

#[tokio::test]
async fn test_simple_channel_pair_creation() {
    let (mut left, mut right) = SimpleChannel::pair();

    // Send from left to right
    left.send(vec![1, 2, 3]).await.expect("Send should succeed");

    let received = right.recv().await.expect("Recv should succeed");
    assert_eq!(received, vec![1, 2, 3]);
}

#[tokio::test]
async fn test_simple_channel_bidirectional() {
    let (mut left, mut right) = SimpleChannel::pair();

    // Left -> Right
    left.send(vec![1]).await.unwrap();
    assert_eq!(right.recv().await.unwrap(), vec![1]);

    // Right -> Left
    right.send(vec![2]).await.unwrap();
    assert_eq!(left.recv().await.unwrap(), vec![2]);
}

#[tokio::test]
async fn test_simple_channel_multiple_messages() {
    let (mut left, mut right) = SimpleChannel::pair();

    // Send multiple messages
    left.send(vec![1]).await.unwrap();
    left.send(vec![2]).await.unwrap();
    left.send(vec![3]).await.unwrap();

    // Receive in FIFO order
    assert_eq!(right.recv().await.unwrap(), vec![1]);
    assert_eq!(right.recv().await.unwrap(), vec![2]);
    assert_eq!(right.recv().await.unwrap(), vec![3]);
}

// ============================================================================
// RumpsteakEndpoint Tests
// ============================================================================

#[tokio::test]
async fn test_endpoint_creation() {
    let endpoint: RumpsteakEndpoint<TestRole> = RumpsteakEndpoint::new(TestRole::Alice);

    assert_eq!(*endpoint.local_role(), TestRole::Alice);
    assert!(endpoint.is_all_closed());
    assert_eq!(endpoint.active_channel_count(), 0);
}

#[tokio::test]
async fn test_endpoint_register_channel() {
    let mut endpoint = RumpsteakEndpoint::new(TestRole::Alice);
    let (channel, _other) = SimpleChannel::pair();

    endpoint.register_channel(TestRole::Bob, channel);

    assert!(endpoint.has_channel(&TestRole::Bob));
    assert!(!endpoint.has_channel(&TestRole::Charlie));
    assert_eq!(endpoint.active_channel_count(), 1);
}

#[tokio::test]
async fn test_endpoint_channel_overwrite() {
    let mut endpoint = RumpsteakEndpoint::new(TestRole::Alice);

    // Register first channel
    let (channel1, _) = SimpleChannel::pair();
    endpoint.register_channel(TestRole::Bob, channel1);

    // Register second channel (overwrites first)
    let (channel2, _) = SimpleChannel::pair();
    endpoint.register_channel(TestRole::Bob, channel2);

    // Still only one channel
    assert_eq!(endpoint.active_channel_count(), 1);
    assert!(endpoint.has_channel(&TestRole::Bob));
}

#[tokio::test]
async fn test_endpoint_close_channel() {
    let mut endpoint = RumpsteakEndpoint::new(TestRole::Alice);
    let (channel, _) = SimpleChannel::pair();

    endpoint.register_channel(TestRole::Bob, channel);
    assert!(endpoint.has_channel(&TestRole::Bob));

    let closed = endpoint.close_channel(&TestRole::Bob);
    assert!(closed);
    assert!(!endpoint.has_channel(&TestRole::Bob));

    // Closing non-existent channel returns false
    let closed_again = endpoint.close_channel(&TestRole::Bob);
    assert!(!closed_again);
}

#[tokio::test]
async fn test_endpoint_close_all_channels() {
    let mut endpoint = RumpsteakEndpoint::new(TestRole::Alice);

    let (channel1, _) = SimpleChannel::pair();
    let (channel2, _) = SimpleChannel::pair();

    endpoint.register_channel(TestRole::Bob, channel1);
    endpoint.register_channel(TestRole::Charlie, channel2);

    assert_eq!(endpoint.active_channel_count(), 2);

    let count = endpoint.close_all_channels();
    assert_eq!(count, 2);
    assert!(endpoint.is_all_closed());
}

#[tokio::test]
async fn test_endpoint_metadata_initial() {
    let mut endpoint = RumpsteakEndpoint::new(TestRole::Alice);
    let (channel, _) = SimpleChannel::pair();

    endpoint.register_channel(TestRole::Bob, channel);

    let metadata = endpoint.get_metadata(&TestRole::Bob).unwrap();
    assert_eq!(metadata.state_description, "Initial");
    assert!(!metadata.is_complete);
    assert_eq!(metadata.operation_count, 0);
}

#[tokio::test]
async fn test_endpoint_all_metadata() {
    let mut endpoint = RumpsteakEndpoint::new(TestRole::Alice);

    let (channel1, _) = SimpleChannel::pair();
    let (channel2, _) = SimpleChannel::pair();

    endpoint.register_channel(TestRole::Bob, channel1);
    endpoint.register_channel(TestRole::Charlie, channel2);

    let all = endpoint.all_metadata();
    assert_eq!(all.len(), 2);
}

// ============================================================================
// RumpsteakHandler Send/Recv Tests
// ============================================================================

#[tokio::test]
async fn test_handler_send_recv_with_simple_channel() {
    let mut handler: RumpsteakHandler<TestRole, TestLabel> = RumpsteakHandler::new();

    // Create endpoints with connected channels
    let mut alice_ep = RumpsteakEndpoint::new(TestRole::Alice);
    let mut bob_ep = RumpsteakEndpoint::new(TestRole::Bob);

    let (alice_to_bob, bob_from_alice) = SimpleChannel::pair();
    alice_ep.register_channel(TestRole::Bob, alice_to_bob);
    bob_ep.register_channel(TestRole::Alice, bob_from_alice);

    // Alice sends to Bob
    let msg = TestMessage { value: 42 };
    handler
        .send(&mut alice_ep, TestRole::Bob, &msg)
        .await
        .expect("Send should succeed");

    // Bob receives from Alice
    let received: TestMessage = handler
        .recv(&mut bob_ep, TestRole::Alice)
        .await
        .expect("Recv should succeed");

    assert_eq!(received, msg);
}

#[tokio::test]
async fn test_handler_metadata_updates_on_send() {
    let mut handler: RumpsteakHandler<TestRole, TestLabel> = RumpsteakHandler::new();
    let mut endpoint = RumpsteakEndpoint::new(TestRole::Alice);

    let (channel, mut other) = SimpleChannel::pair();
    endpoint.register_channel(TestRole::Bob, channel);

    // Initial state
    let meta = endpoint.get_metadata(&TestRole::Bob).unwrap();
    assert_eq!(meta.operation_count, 0);

    // Send a message
    handler
        .send(&mut endpoint, TestRole::Bob, &TestMessage { value: 1 })
        .await
        .unwrap();

    // Consume the message on the other end to avoid channel blocking
    let _ = other.recv().await;

    // Metadata should be updated
    let meta = endpoint.get_metadata(&TestRole::Bob).unwrap();
    assert_eq!(meta.operation_count, 1);
    assert_eq!(meta.state_description, "Send");
}

#[tokio::test]
async fn test_handler_metadata_updates_on_recv() {
    let mut handler: RumpsteakHandler<TestRole, TestLabel> = RumpsteakHandler::new();
    let mut endpoint = RumpsteakEndpoint::new(TestRole::Bob);

    let (channel, mut other) = SimpleChannel::pair();
    endpoint.register_channel(TestRole::Alice, channel);

    // Send a message from the other side
    let msg = TestMessage { value: 42 };
    let bytes = bincode::serialize(&msg).unwrap();
    other.send(bytes).await.unwrap();

    // Receive
    let _: TestMessage = handler
        .recv(&mut endpoint, TestRole::Alice)
        .await
        .unwrap();

    // Metadata should be updated
    let meta = endpoint.get_metadata(&TestRole::Alice).unwrap();
    assert_eq!(meta.operation_count, 1);
    assert_eq!(meta.state_description, "Recv");
}

#[tokio::test]
async fn test_handler_operation_count_increments() {
    let mut handler: RumpsteakHandler<TestRole, TestLabel> = RumpsteakHandler::new();

    // Set up bidirectional channels
    let mut alice_ep = RumpsteakEndpoint::new(TestRole::Alice);
    let mut bob_ep = RumpsteakEndpoint::new(TestRole::Bob);

    let (alice_to_bob, bob_from_alice) = SimpleChannel::pair();
    let (bob_to_alice, alice_from_bob) = SimpleChannel::pair();

    alice_ep.register_channel(TestRole::Bob, alice_to_bob);
    bob_ep.register_channel(TestRole::Alice, bob_from_alice);

    // Also register reverse channels for bidirectional
    let mut alice_ep2 = RumpsteakEndpoint::new(TestRole::Alice);
    alice_ep2.register_channel(TestRole::Bob, alice_from_bob);
    let mut bob_ep2 = RumpsteakEndpoint::new(TestRole::Bob);
    bob_ep2.register_channel(TestRole::Alice, bob_to_alice);

    // Perform multiple operations
    handler
        .send(&mut alice_ep, TestRole::Bob, &TestMessage { value: 1 })
        .await
        .unwrap();
    let _: TestMessage = handler.recv(&mut bob_ep, TestRole::Alice).await.unwrap();

    handler
        .send(&mut alice_ep, TestRole::Bob, &TestMessage { value: 2 })
        .await
        .unwrap();
    let _: TestMessage = handler.recv(&mut bob_ep, TestRole::Alice).await.unwrap();

    // Check operation counts
    let alice_meta = alice_ep.get_metadata(&TestRole::Bob).unwrap();
    assert_eq!(alice_meta.operation_count, 2);

    let bob_meta = bob_ep.get_metadata(&TestRole::Alice).unwrap();
    assert_eq!(bob_meta.operation_count, 2);
}

// ============================================================================
// Choose/Offer Tests
// ============================================================================

#[tokio::test]
async fn test_handler_choose_offer() {
    let mut handler: RumpsteakHandler<TestRole, TestLabel> = RumpsteakHandler::new();

    let mut alice_ep = RumpsteakEndpoint::new(TestRole::Alice);
    let mut bob_ep = RumpsteakEndpoint::new(TestRole::Bob);

    let (alice_to_bob, bob_from_alice) = SimpleChannel::pair();
    alice_ep.register_channel(TestRole::Bob, alice_to_bob);
    bob_ep.register_channel(TestRole::Alice, bob_from_alice);

    // Alice chooses
    handler
        .choose(&mut alice_ep, TestRole::Bob, ChoiceLabel::Accept)
        .await
        .expect("Choose should succeed");

    // Bob offers and receives the choice
    let label = handler
        .offer(&mut bob_ep, TestRole::Alice)
        .await
        .expect("Offer should succeed");

    assert_eq!(label, ChoiceLabel::Accept);
}

#[tokio::test]
async fn test_handler_choose_updates_metadata() {
    let mut handler: RumpsteakHandler<TestRole, TestLabel> = RumpsteakHandler::new();
    let mut endpoint = RumpsteakEndpoint::new(TestRole::Alice);

    let (channel, mut other) = SimpleChannel::pair();
    endpoint.register_channel(TestRole::Bob, channel);

    handler
        .choose(&mut endpoint, TestRole::Bob, ChoiceLabel::Option1)
        .await
        .unwrap();

    // Consume on the other end
    let _ = other.recv().await;

    let meta = endpoint.get_metadata(&TestRole::Bob).unwrap();
    assert_eq!(meta.operation_count, 1);
    assert_eq!(meta.state_description, "Choose");
}

// ============================================================================
// Error Handling Tests
// ============================================================================

#[tokio::test]
async fn test_handler_missing_channel_error() {
    let mut handler: RumpsteakHandler<TestRole, TestLabel> = RumpsteakHandler::new();
    let mut endpoint = RumpsteakEndpoint::new(TestRole::Alice);

    // Try to send without registering a channel
    let result = handler
        .send(&mut endpoint, TestRole::Bob, &TestMessage { value: 1 })
        .await;

    assert!(result.is_err());
    let err = result.unwrap_err();
    let msg = err.to_string();
    assert!(
        msg.contains("no channel registered"),
        "Error should mention missing channel: {}",
        msg
    );
}

#[tokio::test]
async fn test_handler_missing_channel_on_recv() {
    let mut handler: RumpsteakHandler<TestRole, TestLabel> = RumpsteakHandler::new();
    let mut endpoint = RumpsteakEndpoint::new(TestRole::Bob);

    let result: Result<TestMessage, _> = handler.recv(&mut endpoint, TestRole::Alice).await;

    assert!(result.is_err());
}

// ============================================================================
// Timeout Tests
// ============================================================================

#[tokio::test]
async fn test_handler_with_timeout_success() {
    use std::time::Duration;

    let mut handler: RumpsteakHandler<TestRole, TestLabel> = RumpsteakHandler::new();
    let mut endpoint = RumpsteakEndpoint::new(TestRole::Alice);

    let result = handler
        .with_timeout(&mut endpoint, TestRole::Alice, Duration::from_secs(1), async {
            Ok(42)
        })
        .await;

    assert_eq!(result.unwrap(), 42);
}

#[tokio::test]
async fn test_handler_with_timeout_expires() {
    use std::time::Duration;

    let mut handler: RumpsteakHandler<TestRole, TestLabel> = RumpsteakHandler::new();
    let mut endpoint = RumpsteakEndpoint::new(TestRole::Alice);

    let result: Result<i32, _> = handler
        .with_timeout(
            &mut endpoint,
            TestRole::Alice,
            Duration::from_millis(10),
            async {
                tokio::time::sleep(Duration::from_secs(10)).await;
                Ok(42)
            },
        )
        .await;

    assert!(result.is_err());
    let err = result.unwrap_err();
    let msg = format!("{:?}", err);
    assert!(msg.contains("Timeout"), "Should be a timeout error: {}", msg);
}

// ============================================================================
// Handler Default Implementation Test
// ============================================================================

#[tokio::test]
async fn test_handler_default() {
    let handler1: RumpsteakHandler<TestRole, TestLabel> = RumpsteakHandler::new();
    let handler2: RumpsteakHandler<TestRole, TestLabel> = RumpsteakHandler::default();

    // Both should work identically - just verify they can be created
    let _ = handler1;
    let _ = handler2;
}

// ============================================================================
// Multi-Peer Tests
// ============================================================================

#[tokio::test]
async fn test_endpoint_multiple_peers() {
    let mut handler: RumpsteakHandler<TestRole, TestLabel> = RumpsteakHandler::new();
    let mut alice_ep = RumpsteakEndpoint::new(TestRole::Alice);

    // Register channels to multiple peers
    let (to_bob, mut from_bob) = SimpleChannel::pair();
    let (to_charlie, mut from_charlie) = SimpleChannel::pair();

    alice_ep.register_channel(TestRole::Bob, to_bob);
    alice_ep.register_channel(TestRole::Charlie, to_charlie);

    // Send to both
    handler
        .send(&mut alice_ep, TestRole::Bob, &TestMessage { value: 1 })
        .await
        .unwrap();
    handler
        .send(&mut alice_ep, TestRole::Charlie, &TestMessage { value: 2 })
        .await
        .unwrap();

    // Receive on both
    let bob_bytes = from_bob.recv().await.unwrap();
    let charlie_bytes = from_charlie.recv().await.unwrap();

    let bob_msg: TestMessage = bincode::deserialize(&bob_bytes).unwrap();
    let charlie_msg: TestMessage = bincode::deserialize(&charlie_bytes).unwrap();

    assert_eq!(bob_msg.value, 1);
    assert_eq!(charlie_msg.value, 2);
}
