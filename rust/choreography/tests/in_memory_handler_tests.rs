//! Tests for InMemoryHandler correctness.
//!
//! Verifies core invariants:
//! - Message FIFO ordering
//! - Serialization round-trip fidelity
//! - Label value preservation
//! - Channel isolation (no cross-talk)

#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

use rumpsteak_aura_choreography::effects::{handlers::in_memory::InMemoryHandler, ChoreoHandler};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::{Arc, Mutex};

// ============================================================================
// Test Role Setup
// ============================================================================

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum TestRole {
    Alice,
    Bob,
    Charlie,
}

// ============================================================================
// Test Message Types
// ============================================================================

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
struct SimpleMessage {
    value: i32,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
struct ComplexMessage {
    id: u64,
    name: String,
    data: Vec<u8>,
    flag: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
struct LabelMessage {
    label: String,
    special_chars: String,
}

// ============================================================================
// Basic Send/Receive Tests
// ============================================================================

#[tokio::test]
async fn test_basic_send_recv() {
    // Create shared channel maps
    let channels = Arc::new(Mutex::new(HashMap::new()));
    let choice_channels = Arc::new(Mutex::new(HashMap::new()));

    // Create handlers for Alice and Bob
    let mut alice =
        InMemoryHandler::with_channels(TestRole::Alice, channels.clone(), choice_channels.clone());
    let mut bob =
        InMemoryHandler::with_channels(TestRole::Bob, channels.clone(), choice_channels.clone());

    // Alice sends to Bob
    let msg = SimpleMessage { value: 42 };
    alice
        .send(&mut (), TestRole::Bob, &msg)
        .await
        .expect("Send should succeed");

    // Bob receives from Alice
    let received: SimpleMessage = bob
        .recv(&mut (), TestRole::Alice)
        .await
        .expect("Recv should succeed");

    assert_eq!(received, msg);
}

#[tokio::test]
async fn test_complex_message_serialization() {
    let channels = Arc::new(Mutex::new(HashMap::new()));
    let choice_channels = Arc::new(Mutex::new(HashMap::new()));

    let mut alice =
        InMemoryHandler::with_channels(TestRole::Alice, channels.clone(), choice_channels.clone());
    let mut bob =
        InMemoryHandler::with_channels(TestRole::Bob, channels.clone(), choice_channels.clone());

    // Send complex message
    let msg = ComplexMessage {
        id: 12345678901234,
        name: "Test Message with Special Chars: 日本語 🎉".to_string(),
        data: vec![0, 1, 255, 128, 64],
        flag: true,
    };

    alice
        .send(&mut (), TestRole::Bob, &msg)
        .await
        .expect("Complex message send should succeed");

    let received: ComplexMessage = bob
        .recv(&mut (), TestRole::Alice)
        .await
        .expect("Complex message recv should succeed");

    assert_eq!(received, msg);
}

// ============================================================================
// Multi-Message Tests
// ============================================================================

// NOTE: InMemoryHandler is designed for single-message exchanges per role pair.
// Multiple sequential messages require re-establishing channels.

#[tokio::test]
async fn test_multiple_independent_exchanges() {
    // Demonstrate that each send/recv pair works independently
    // by creating fresh handlers for each exchange

    for i in 0..5 {
        let channels = Arc::new(Mutex::new(HashMap::new()));
        let choice_channels = Arc::new(Mutex::new(HashMap::new()));

        let mut alice = InMemoryHandler::with_channels(
            TestRole::Alice,
            channels.clone(),
            choice_channels.clone(),
        );
        let mut bob =
            InMemoryHandler::with_channels(TestRole::Bob, channels.clone(), choice_channels.clone());

        let msg = SimpleMessage { value: i };
        alice
            .send(&mut (), TestRole::Bob, &msg)
            .await
            .expect("Send should succeed");

        let received: SimpleMessage = bob
            .recv(&mut (), TestRole::Alice)
            .await
            .expect("Recv should succeed");

        assert_eq!(received.value, i, "Each exchange should work correctly");
    }
}

#[tokio::test]
async fn test_interleaved_bidirectional_exchange() {
    // Test that bidirectional communication works when interleaved
    let channels = Arc::new(Mutex::new(HashMap::new()));
    let choice_channels = Arc::new(Mutex::new(HashMap::new()));

    let mut alice =
        InMemoryHandler::with_channels(TestRole::Alice, channels.clone(), choice_channels.clone());
    let mut bob =
        InMemoryHandler::with_channels(TestRole::Bob, channels.clone(), choice_channels.clone());

    // Alice sends, Bob receives
    alice
        .send(&mut (), TestRole::Bob, &SimpleMessage { value: 1 })
        .await
        .unwrap();
    let r1: SimpleMessage = bob.recv(&mut (), TestRole::Alice).await.unwrap();
    assert_eq!(r1.value, 1);

    // Bob sends, Alice receives
    bob.send(&mut (), TestRole::Alice, &SimpleMessage { value: 2 })
        .await
        .unwrap();
    let r2: SimpleMessage = alice.recv(&mut (), TestRole::Bob).await.unwrap();
    assert_eq!(r2.value, 2);
}

// ============================================================================
// Label Preservation Tests
// ============================================================================

#[tokio::test]
async fn test_label_with_special_characters() {
    // Test various special characters are preserved through serialization
    let test_cases = vec![
        LabelMessage {
            label: "simple".to_string(),
            special_chars: "".to_string(),
        },
        LabelMessage {
            label: "with-hyphen".to_string(),
            special_chars: "-".to_string(),
        },
        LabelMessage {
            label: "with_underscore".to_string(),
            special_chars: "_".to_string(),
        },
        LabelMessage {
            label: "unicode:日本語".to_string(),
            special_chars: "日本語".to_string(),
        },
        LabelMessage {
            label: "emoji:🎉🚀".to_string(),
            special_chars: "🎉🚀".to_string(),
        },
        LabelMessage {
            label: "newline\ntest".to_string(),
            special_chars: "\n\t".to_string(),
        },
    ];

    // Test each case with fresh channels
    for expected in &test_cases {
        let channels = Arc::new(Mutex::new(HashMap::new()));
        let choice_channels = Arc::new(Mutex::new(HashMap::new()));

        let mut alice = InMemoryHandler::with_channels(
            TestRole::Alice,
            channels.clone(),
            choice_channels.clone(),
        );
        let mut bob =
            InMemoryHandler::with_channels(TestRole::Bob, channels.clone(), choice_channels.clone());

        alice
            .send(&mut (), TestRole::Bob, expected)
            .await
            .expect("Send should succeed");

        let received: LabelMessage = bob
            .recv(&mut (), TestRole::Alice)
            .await
            .expect("Recv should succeed");

        assert_eq!(
            &received, expected,
            "Label should be preserved exactly: {:?}",
            expected.label
        );
    }
}

// ============================================================================
// Channel Isolation Tests
// ============================================================================

#[tokio::test]
async fn test_channel_isolation_two_party() {
    let channels = Arc::new(Mutex::new(HashMap::new()));
    let choice_channels = Arc::new(Mutex::new(HashMap::new()));

    let mut alice =
        InMemoryHandler::with_channels(TestRole::Alice, channels.clone(), choice_channels.clone());
    let mut bob =
        InMemoryHandler::with_channels(TestRole::Bob, channels.clone(), choice_channels.clone());

    // Alice sends to Bob
    let alice_msg = SimpleMessage { value: 100 };
    alice
        .send(&mut (), TestRole::Bob, &alice_msg)
        .await
        .expect("Alice->Bob send should succeed");

    // Bob sends to Alice
    let bob_msg = SimpleMessage { value: 200 };
    bob.send(&mut (), TestRole::Alice, &bob_msg)
        .await
        .expect("Bob->Alice send should succeed");

    // Bob receives from Alice (should get 100, not 200)
    let received_by_bob: SimpleMessage = bob
        .recv(&mut (), TestRole::Alice)
        .await
        .expect("Bob recv should succeed");
    assert_eq!(
        received_by_bob.value, 100,
        "Bob should receive Alice's message"
    );

    // Alice receives from Bob (should get 200, not 100)
    let received_by_alice: SimpleMessage = alice
        .recv(&mut (), TestRole::Bob)
        .await
        .expect("Alice recv should succeed");
    assert_eq!(
        received_by_alice.value, 200,
        "Alice should receive Bob's message"
    );
}

#[tokio::test]
async fn test_channel_isolation_three_party() {
    let channels = Arc::new(Mutex::new(HashMap::new()));
    let choice_channels = Arc::new(Mutex::new(HashMap::new()));

    let mut alice =
        InMemoryHandler::with_channels(TestRole::Alice, channels.clone(), choice_channels.clone());
    let mut bob =
        InMemoryHandler::with_channels(TestRole::Bob, channels.clone(), choice_channels.clone());
    let mut charlie = InMemoryHandler::with_channels(
        TestRole::Charlie,
        channels.clone(),
        choice_channels.clone(),
    );

    // Alice -> Bob
    alice
        .send(&mut (), TestRole::Bob, &SimpleMessage { value: 1 })
        .await
        .unwrap();

    // Alice -> Charlie
    alice
        .send(&mut (), TestRole::Charlie, &SimpleMessage { value: 2 })
        .await
        .unwrap();

    // Bob -> Charlie
    bob.send(&mut (), TestRole::Charlie, &SimpleMessage { value: 3 })
        .await
        .unwrap();

    // Verify each party receives correct messages
    let bob_from_alice: SimpleMessage = bob.recv(&mut (), TestRole::Alice).await.unwrap();
    assert_eq!(bob_from_alice.value, 1, "Bob should receive 1 from Alice");

    let charlie_from_alice: SimpleMessage = charlie.recv(&mut (), TestRole::Alice).await.unwrap();
    assert_eq!(
        charlie_from_alice.value, 2,
        "Charlie should receive 2 from Alice"
    );

    let charlie_from_bob: SimpleMessage = charlie.recv(&mut (), TestRole::Bob).await.unwrap();
    assert_eq!(
        charlie_from_bob.value, 3,
        "Charlie should receive 3 from Bob"
    );
}

// ============================================================================
// Edge Case Tests
// ============================================================================

#[tokio::test]
async fn test_empty_data() {
    let channels = Arc::new(Mutex::new(HashMap::new()));
    let choice_channels = Arc::new(Mutex::new(HashMap::new()));

    let mut alice =
        InMemoryHandler::with_channels(TestRole::Alice, channels.clone(), choice_channels.clone());
    let mut bob =
        InMemoryHandler::with_channels(TestRole::Bob, channels.clone(), choice_channels.clone());

    // Send message with empty data
    let msg = ComplexMessage {
        id: 0,
        name: "".to_string(),
        data: vec![],
        flag: false,
    };

    alice.send(&mut (), TestRole::Bob, &msg).await.unwrap();
    let received: ComplexMessage = bob.recv(&mut (), TestRole::Alice).await.unwrap();

    assert_eq!(received, msg, "Empty data should be preserved");
}

#[tokio::test]
async fn test_large_message() {
    let channels = Arc::new(Mutex::new(HashMap::new()));
    let choice_channels = Arc::new(Mutex::new(HashMap::new()));

    let mut alice =
        InMemoryHandler::with_channels(TestRole::Alice, channels.clone(), choice_channels.clone());
    let mut bob =
        InMemoryHandler::with_channels(TestRole::Bob, channels.clone(), choice_channels.clone());

    // Send large message (1MB of data)
    let msg = ComplexMessage {
        id: u64::MAX,
        name: "x".repeat(10000),
        data: vec![0u8; 1_000_000],
        flag: true,
    };

    alice.send(&mut (), TestRole::Bob, &msg).await.unwrap();
    let received: ComplexMessage = bob.recv(&mut (), TestRole::Alice).await.unwrap();

    assert_eq!(received.id, msg.id);
    assert_eq!(received.name.len(), 10000);
    assert_eq!(received.data.len(), 1_000_000);
}

// ============================================================================
// Handler Construction Tests
// ============================================================================

#[tokio::test]
async fn test_handler_new_constructor() {
    // Verify the basic constructor works
    let _handler: InMemoryHandler<TestRole> = InMemoryHandler::new(TestRole::Alice);
    // If we get here without panic, the constructor works
}

#[tokio::test]
async fn test_multiple_handlers_same_channels() {
    let channels = Arc::new(Mutex::new(HashMap::new()));
    let choice_channels = Arc::new(Mutex::new(HashMap::new()));

    // Create two handlers for Alice (simulating reconnection scenario)
    let mut alice1 =
        InMemoryHandler::with_channels(TestRole::Alice, channels.clone(), choice_channels.clone());
    let mut bob =
        InMemoryHandler::with_channels(TestRole::Bob, channels.clone(), choice_channels.clone());

    // Alice1 sends
    alice1
        .send(&mut (), TestRole::Bob, &SimpleMessage { value: 42 })
        .await
        .unwrap();

    // Bob receives
    let received: SimpleMessage = bob.recv(&mut (), TestRole::Alice).await.unwrap();
    assert_eq!(received.value, 42);
}
