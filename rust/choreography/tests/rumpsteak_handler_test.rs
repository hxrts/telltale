#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

// Integration tests for RumpsteakHandler with SimpleChannel

use rumpsteak_aura_choreography::effects::{
    handlers::rumpsteak::{RumpsteakEndpoint, RumpsteakHandler, RumpsteakSession, SimpleChannel},
    ChoreoHandler, LabelId, RoleId,
};
use rumpsteak_aura_choreography::RoleName;
use serde::{Deserialize, Serialize};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum TestRole {
    Alice,
    Bob,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum TestLabel {
    OptionA,
    Buy,
    Sell,
    Hold,
    Cancel,
    Proceed,
    DynamicPath,
}

impl LabelId for TestLabel {
    fn as_str(&self) -> &'static str {
        match self {
            TestLabel::OptionA => "option_a",
            TestLabel::Buy => "buy",
            TestLabel::Sell => "sell",
            TestLabel::Hold => "hold",
            TestLabel::Cancel => "cancel",
            TestLabel::Proceed => "proceed",
            TestLabel::DynamicPath => "dynamic_path",
        }
    }

    fn from_str(label: &str) -> Option<Self> {
        match label {
            "option_a" => Some(TestLabel::OptionA),
            "buy" => Some(TestLabel::Buy),
            "sell" => Some(TestLabel::Sell),
            "hold" => Some(TestLabel::Hold),
            "cancel" => Some(TestLabel::Cancel),
            "proceed" => Some(TestLabel::Proceed),
            "dynamic_path" => Some(TestLabel::DynamicPath),
            _ => None,
        }
    }
}

impl RoleId for TestRole {
    type Label = TestLabel;

    fn role_name(&self) -> RoleName {
        match self {
            TestRole::Alice => RoleName::from_static("Alice"),
            TestRole::Bob => RoleName::from_static("Bob"),
        }
    }
}

impl rumpsteak_aura::Role for TestRole {
    type Message = TestMessage;

    fn seal(&mut self) {
        // No-op for test
    }

    fn is_sealed(&self) -> bool {
        false
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
struct TestMessage {
    content: String,
}

impl rumpsteak_aura::Message<Box<dyn std::any::Any + Send>> for TestMessage {
    fn upcast(msg: Box<dyn std::any::Any + Send>) -> Self {
        *msg.downcast::<TestMessage>().unwrap()
    }

    fn downcast(self) -> Result<Box<dyn std::any::Any + Send>, Self> {
        Ok(Box::new(self))
    }
}

#[tokio::test]
async fn test_simple_send_recv() {
    // Create two endpoints
    let mut alice_endpoint = RumpsteakEndpoint::new(TestRole::Alice);
    let mut bob_endpoint = RumpsteakEndpoint::new(TestRole::Bob);

    // Create a pair of channels
    let (alice_channel, bob_channel) = SimpleChannel::pair();

    // Register channels at each endpoint
    alice_endpoint.register_channel(TestRole::Bob, alice_channel);
    bob_endpoint.register_channel(TestRole::Alice, bob_channel);

    // Create handlers
    let mut alice_handler = RumpsteakHandler::<TestRole, TestMessage>::new();
    let mut bob_handler = RumpsteakHandler::<TestRole, TestMessage>::new();

    // Test message
    let test_msg = TestMessage {
        content: "Hello from Alice!".to_string(),
    };

    // Alice sends to Bob
    alice_handler
        .send(&mut alice_endpoint, TestRole::Bob, &test_msg)
        .await
        .expect("Alice should send successfully");

    // Bob receives from Alice
    let received: TestMessage = bob_handler
        .recv(&mut bob_endpoint, TestRole::Alice)
        .await
        .expect("Bob should receive successfully");

    assert_eq!(
        received, test_msg,
        "Bob should receive the same message Alice sent"
    );
}

#[tokio::test]
async fn test_bidirectional_communication() {
    // Create endpoints
    let mut alice_endpoint = RumpsteakEndpoint::new(TestRole::Alice);
    let mut bob_endpoint = RumpsteakEndpoint::new(TestRole::Bob);

    // Create channel pairs
    let (alice_channel, bob_channel) = SimpleChannel::pair();

    // Register channels
    alice_endpoint.register_channel(TestRole::Bob, alice_channel);
    bob_endpoint.register_channel(TestRole::Alice, bob_channel);

    // Create handlers
    let mut alice_handler = RumpsteakHandler::<TestRole, TestMessage>::new();
    let mut bob_handler = RumpsteakHandler::<TestRole, TestMessage>::new();

    // Alice sends to Bob
    let msg1 = TestMessage {
        content: "Ping".to_string(),
    };
    alice_handler
        .send(&mut alice_endpoint, TestRole::Bob, &msg1)
        .await
        .expect("Alice should send ping");

    // Bob receives from Alice
    let received1: TestMessage = bob_handler
        .recv(&mut bob_endpoint, TestRole::Alice)
        .await
        .expect("Bob should receive ping");

    assert_eq!(received1.content, "Ping");

    // Bob sends back to Alice
    let msg2 = TestMessage {
        content: "Pong".to_string(),
    };
    bob_handler
        .send(&mut bob_endpoint, TestRole::Alice, &msg2)
        .await
        .expect("Bob should send pong");

    // Alice receives from Bob
    let received2: TestMessage = alice_handler
        .recv(&mut alice_endpoint, TestRole::Bob)
        .await
        .expect("Alice should receive pong");

    assert_eq!(received2.content, "Pong");
}

#[tokio::test]
async fn test_multiple_messages() {
    // Create endpoints
    let mut alice_endpoint = RumpsteakEndpoint::new(TestRole::Alice);
    let mut bob_endpoint = RumpsteakEndpoint::new(TestRole::Bob);

    // Create channels
    let (alice_channel, bob_channel) = SimpleChannel::pair();
    alice_endpoint.register_channel(TestRole::Bob, alice_channel);
    bob_endpoint.register_channel(TestRole::Alice, bob_channel);

    // Create handlers
    let mut alice_handler = RumpsteakHandler::<TestRole, TestMessage>::new();
    let mut bob_handler = RumpsteakHandler::<TestRole, TestMessage>::new();

    // Send multiple messages
    for i in 0..5 {
        let msg = TestMessage {
            content: format!("Message {i}"),
        };

        alice_handler
            .send(&mut alice_endpoint, TestRole::Bob, &msg)
            .await
            .expect("Alice should send message");

        let received: TestMessage = bob_handler
            .recv(&mut bob_endpoint, TestRole::Alice)
            .await
            .expect("Bob should receive message");

        assert_eq!(received.content, format!("Message {i}"));
    }
}

#[tokio::test]
async fn test_no_channel_error() {
    // Create an endpoint without registering a channel
    let mut alice_endpoint = RumpsteakEndpoint::new(TestRole::Alice);
    let mut alice_handler = RumpsteakHandler::<TestRole, TestMessage>::new();

    let msg = TestMessage {
        content: "This should fail".to_string(),
    };

    // Try to send without a channel
    let result = alice_handler
        .send(&mut alice_endpoint, TestRole::Bob, &msg)
        .await;

    assert!(
        result.is_err(),
        "Send should fail when no channel is registered"
    );
    assert!(result
        .unwrap_err()
        .to_string()
        .contains("no channel registered"));
}

#[tokio::test]
async fn test_large_message() {
    // Create endpoints
    let mut alice_endpoint = RumpsteakEndpoint::new(TestRole::Alice);
    let mut bob_endpoint = RumpsteakEndpoint::new(TestRole::Bob);

    // Create channels
    let (alice_channel, bob_channel) = SimpleChannel::pair();
    alice_endpoint.register_channel(TestRole::Bob, alice_channel);
    bob_endpoint.register_channel(TestRole::Alice, bob_channel);

    // Create handlers
    let mut alice_handler = RumpsteakHandler::<TestRole, TestMessage>::new();
    let mut bob_handler = RumpsteakHandler::<TestRole, TestMessage>::new();

    // Create a large message (10MB string)
    let large_content = "x".repeat(10 * 1024 * 1024);
    let msg = TestMessage {
        content: large_content.clone(),
    };

    // Send large message
    alice_handler
        .send(&mut alice_endpoint, TestRole::Bob, &msg)
        .await
        .expect("Should send large message");

    // Receive large message
    let received: TestMessage = bob_handler
        .recv(&mut bob_endpoint, TestRole::Alice)
        .await
        .expect("Should receive large message");

    assert_eq!(received.content.len(), 10 * 1024 * 1024);
    assert_eq!(received.content, large_content);
}

#[tokio::test]
async fn test_choice_selection() {
    // Create endpoints
    let mut alice_endpoint = RumpsteakEndpoint::new(TestRole::Alice);
    let mut bob_endpoint = RumpsteakEndpoint::new(TestRole::Bob);

    // Create channels
    let (alice_channel, bob_channel) = SimpleChannel::pair();
    alice_endpoint.register_channel(TestRole::Bob, alice_channel);
    bob_endpoint.register_channel(TestRole::Alice, bob_channel);

    // Create handlers
    let mut alice_handler = RumpsteakHandler::<TestRole, TestMessage>::new();
    let mut bob_handler = RumpsteakHandler::<TestRole, TestMessage>::new();

    // Alice chooses "option_a"
    let choice_label = TestLabel::OptionA;
    alice_handler
        .choose(&mut alice_endpoint, TestRole::Bob, choice_label)
        .await
        .expect("Alice should choose successfully");

    // Bob receives the choice
    let received_label = bob_handler
        .offer(&mut bob_endpoint, TestRole::Alice)
        .await
        .expect("Bob should receive choice");

    assert_eq!(
        received_label,
        TestLabel::OptionA,
        "Bob should receive the same choice Alice made"
    );
}

#[tokio::test]
async fn test_multiple_choices() {
    // Create endpoints
    let mut alice_endpoint = RumpsteakEndpoint::new(TestRole::Alice);
    let mut bob_endpoint = RumpsteakEndpoint::new(TestRole::Bob);

    // Create channels
    let (alice_channel, bob_channel) = SimpleChannel::pair();
    alice_endpoint.register_channel(TestRole::Bob, alice_channel);
    bob_endpoint.register_channel(TestRole::Alice, bob_channel);

    // Create handlers
    let mut alice_handler = RumpsteakHandler::<TestRole, TestMessage>::new();
    let mut bob_handler = RumpsteakHandler::<TestRole, TestMessage>::new();

    // Test multiple choice sequences
    let choices = vec![
        TestLabel::Buy,
        TestLabel::Sell,
        TestLabel::Hold,
        TestLabel::Cancel,
    ];

    for choice_label in choices {
        alice_handler
            .choose(&mut alice_endpoint, TestRole::Bob, choice_label)
            .await
            .expect("Alice should choose successfully");

        let received_label = bob_handler
            .offer(&mut bob_endpoint, TestRole::Alice)
            .await
            .expect("Bob should receive choice");

        assert_eq!(
            received_label,
            choice_label,
            "Bob should receive choice: {}",
            choice_label.as_str()
        );
    }
}

#[tokio::test]
async fn test_choice_with_messages() {
    // Create endpoints
    let mut alice_endpoint = RumpsteakEndpoint::new(TestRole::Alice);
    let mut bob_endpoint = RumpsteakEndpoint::new(TestRole::Bob);

    // Create channels
    let (alice_channel, bob_channel) = SimpleChannel::pair();
    alice_endpoint.register_channel(TestRole::Bob, alice_channel);
    bob_endpoint.register_channel(TestRole::Alice, bob_channel);

    // Create handlers
    let mut alice_handler = RumpsteakHandler::<TestRole, TestMessage>::new();
    let mut bob_handler = RumpsteakHandler::<TestRole, TestMessage>::new();

    // Send a message
    let msg1 = TestMessage {
        content: "Hello".to_string(),
    };
    alice_handler
        .send(&mut alice_endpoint, TestRole::Bob, &msg1)
        .await
        .expect("Send should succeed");

    let received1: TestMessage = bob_handler
        .recv(&mut bob_endpoint, TestRole::Alice)
        .await
        .expect("Receive should succeed");

    assert_eq!(received1.content, "Hello");

    // Make a choice
    let choice_label = TestLabel::Proceed;
    bob_handler
        .choose(&mut bob_endpoint, TestRole::Alice, choice_label)
        .await
        .expect("Choice should succeed");

    let received_choice = alice_handler
        .offer(&mut alice_endpoint, TestRole::Bob)
        .await
        .expect("Offer should succeed");

    assert_eq!(received_choice, TestLabel::Proceed);

    // Send another message
    let msg2 = TestMessage {
        content: "Goodbye".to_string(),
    };
    bob_handler
        .send(&mut bob_endpoint, TestRole::Alice, &msg2)
        .await
        .expect("Send should succeed");

    let received2: TestMessage = alice_handler
        .recv(&mut alice_endpoint, TestRole::Bob)
        .await
        .expect("Receive should succeed");

    assert_eq!(received2.content, "Goodbye");
}

#[tokio::test]
async fn test_session_state_tracking() {
    // Create endpoints
    let mut alice_endpoint = RumpsteakEndpoint::new(TestRole::Alice);
    let mut bob_endpoint = RumpsteakEndpoint::new(TestRole::Bob);

    // Create channels
    let (alice_channel, bob_channel) = SimpleChannel::pair();
    alice_endpoint.register_channel(TestRole::Bob, alice_channel);
    bob_endpoint.register_channel(TestRole::Alice, bob_channel);

    // Verify initial metadata
    let alice_meta = alice_endpoint.get_metadata(&TestRole::Bob).unwrap();
    assert_eq!(alice_meta.operation_count, 0);
    assert_eq!(alice_meta.state_description, "Initial");
    assert!(!alice_meta.is_complete);

    // Create handlers
    let mut alice_handler = RumpsteakHandler::<TestRole, TestMessage>::new();
    let mut bob_handler = RumpsteakHandler::<TestRole, TestMessage>::new();

    // Perform send operation
    let msg1 = TestMessage {
        content: "Test".to_string(),
    };
    alice_handler
        .send(&mut alice_endpoint, TestRole::Bob, &msg1)
        .await
        .expect("Send should succeed");

    // Check that operation was tracked
    let alice_meta = alice_endpoint.get_metadata(&TestRole::Bob).unwrap();
    assert_eq!(alice_meta.operation_count, 1);
    assert_eq!(alice_meta.state_description, "Send");

    // Bob receives
    let _received: TestMessage = bob_handler
        .recv(&mut bob_endpoint, TestRole::Alice)
        .await
        .expect("Receive should succeed");

    // Check Bob's metadata
    let bob_meta = bob_endpoint.get_metadata(&TestRole::Alice).unwrap();
    assert_eq!(bob_meta.operation_count, 1);
    assert_eq!(bob_meta.state_description, "Recv");

    // Perform choice operation
    let choice_label = TestLabel::OptionA;
    alice_handler
        .choose(&mut alice_endpoint, TestRole::Bob, choice_label)
        .await
        .expect("Choose should succeed");

    // Check that operation was tracked
    let alice_meta = alice_endpoint.get_metadata(&TestRole::Bob).unwrap();
    assert_eq!(alice_meta.operation_count, 2); // Send + Choose
    assert_eq!(alice_meta.state_description, "Choose");

    // Bob offers
    let _label = bob_handler
        .offer(&mut bob_endpoint, TestRole::Alice)
        .await
        .expect("Offer should succeed");

    // Check Bob's metadata
    let bob_meta = bob_endpoint.get_metadata(&TestRole::Alice).unwrap();
    assert_eq!(bob_meta.operation_count, 2); // Recv + Offer
    assert_eq!(bob_meta.state_description, "Offer");

    // Get all metadata
    let all_alice_meta = alice_endpoint.all_metadata();
    assert_eq!(all_alice_meta.len(), 1);
    assert_eq!(all_alice_meta[0].1.operation_count, 2);
}

#[tokio::test]
async fn test_resource_cleanup() {
    // Create endpoint
    let mut alice_endpoint = RumpsteakEndpoint::new(TestRole::Alice);
    let mut bob_endpoint = RumpsteakEndpoint::new(TestRole::Bob);

    // Create channels
    let (alice_channel, bob_channel) = SimpleChannel::pair();
    alice_endpoint.register_channel(TestRole::Bob, alice_channel);
    bob_endpoint.register_channel(TestRole::Alice, bob_channel);

    // Verify channels are active
    assert_eq!(alice_endpoint.active_channel_count(), 1);
    assert!(!alice_endpoint.is_all_closed());
    assert!(alice_endpoint.has_channel(&TestRole::Bob));

    // Close specific channel
    let closed = alice_endpoint.close_channel(&TestRole::Bob);
    assert!(closed);

    // Verify channel is closed
    assert_eq!(alice_endpoint.active_channel_count(), 0);
    assert!(alice_endpoint.is_all_closed());
    assert!(!alice_endpoint.has_channel(&TestRole::Bob));
}

#[tokio::test]
async fn test_close_all_channels() {
    // Create endpoint with multiple channels
    let mut endpoint = RumpsteakEndpoint::new(TestRole::Alice);

    // Register channels for multiple peers
    let (ch1, _) = SimpleChannel::pair();
    let (ch2, _) = SimpleChannel::pair();
    endpoint.register_channel(TestRole::Bob, ch1);
    endpoint.register_channel(TestRole::Alice, ch2); // Alice can have channel to itself

    // Verify channels are active
    assert_eq!(endpoint.active_channel_count(), 2);

    // Close all
    let closed_count = endpoint.close_all_channels();
    assert_eq!(closed_count, 2);

    // Verify all are closed
    assert_eq!(endpoint.active_channel_count(), 0);
    assert!(endpoint.is_all_closed());
}

#[tokio::test]
async fn test_error_recovery() {
    // Create endpoints
    let mut alice_endpoint = RumpsteakEndpoint::new(TestRole::Alice);
    let mut bob_endpoint = RumpsteakEndpoint::new(TestRole::Bob);

    // Create channels
    let (alice_channel, bob_channel) = SimpleChannel::pair();
    alice_endpoint.register_channel(TestRole::Bob, alice_channel);
    bob_endpoint.register_channel(TestRole::Alice, bob_channel);

    // Create handlers
    let mut alice_handler = RumpsteakHandler::<TestRole, TestMessage>::new();

    // Send a message
    let msg = TestMessage {
        content: "Test".to_string(),
    };
    alice_handler
        .send(&mut alice_endpoint, TestRole::Bob, &msg)
        .await
        .expect("Send should succeed");

    // Simulate error by closing the channel
    alice_endpoint.close_channel(&TestRole::Bob);

    // Try to send again - should fail gracefully
    let result = alice_handler
        .send(&mut alice_endpoint, TestRole::Bob, &msg)
        .await;
    assert!(result.is_err());

    // Verify error message is informative
    let err = result.unwrap_err();
    assert!(err.to_string().contains("no channel registered"));
}

#[tokio::test]
async fn test_dynamic_session_flow() {
    let mut alice_endpoint = RumpsteakEndpoint::new(TestRole::Alice);
    let mut bob_endpoint = RumpsteakEndpoint::new(TestRole::Bob);

    let (alice_channel, bob_channel) = SimpleChannel::pair();
    alice_endpoint.register_session(
        TestRole::Bob,
        RumpsteakSession::from_simple_channel(alice_channel),
    );
    bob_endpoint.register_session(
        TestRole::Alice,
        RumpsteakSession::from_simple_channel(bob_channel),
    );

    let mut alice_handler = RumpsteakHandler::<TestRole, TestMessage>::new();
    let mut bob_handler = RumpsteakHandler::<TestRole, TestMessage>::new();

    let msg = TestMessage {
        content: "dynamic session".to_string(),
    };

    alice_handler
        .send(&mut alice_endpoint, TestRole::Bob, &msg)
        .await
        .expect("dynamic send should succeed");

    let received: TestMessage = bob_handler
        .recv(&mut bob_endpoint, TestRole::Alice)
        .await
        .expect("dynamic recv should succeed");

    assert_eq!(received.content, "dynamic session");

    let label = TestLabel::DynamicPath;
    bob_handler
        .choose(&mut bob_endpoint, TestRole::Alice, label)
        .await
        .expect("dynamic choose should succeed");

    let offered = alice_handler
        .offer(&mut alice_endpoint, TestRole::Bob)
        .await
        .expect("dynamic offer should succeed");

    assert_eq!(offered, TestLabel::DynamicPath);

    let alice_meta = alice_endpoint.get_metadata(&TestRole::Bob).unwrap();
    assert!(alice_meta.operation_count >= 2);
}

#[tokio::test]
async fn test_drop_cleanup() {
    // Create endpoint in a scope
    {
        let mut endpoint = RumpsteakEndpoint::new(TestRole::Alice);
        let (ch, _) = SimpleChannel::pair();
        endpoint.register_channel(TestRole::Bob, ch);

        assert_eq!(endpoint.active_channel_count(), 1);
        // Endpoint will be dropped here with active channels
    }
    // Drop implementation should have cleaned up
    // (verified by lack of panic and proper tracing output)
}
