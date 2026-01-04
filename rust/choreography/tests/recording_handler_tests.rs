//! Tests for RecordingHandler correctness.
//!
//! Verifies:
//! - All events captured in order
//! - Event types match operations
//! - recv()/offer() intentionally fail (by design)
//! - Thread-safe accumulation

#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

use rumpsteak_aura_choreography::effects::{
    handlers::recording::{RecordedEvent, RecordingHandler},
    ChoreoHandler, LabelId, RoleId,
};
use rumpsteak_aura_choreography::RoleName;
use serde::{Deserialize, Serialize};

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
enum TestLabel {
    Accept,
    Option1,
}

impl LabelId for TestLabel {
    fn as_str(&self) -> &'static str {
        match self {
            TestLabel::Accept => "Accept",
            TestLabel::Option1 => "Option1",
        }
    }

    fn from_str(label: &str) -> Option<Self> {
        match label {
            "Accept" => Some(TestLabel::Accept),
            "Option1" => Some(TestLabel::Option1),
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
            TestRole::Charlie => RoleName::from_static("Charlie"),
        }
    }
}

// ============================================================================
// Test Message Types
// ============================================================================

#[derive(Debug, Clone, Serialize, Deserialize)]
struct TestMessage {
    value: i32,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct AnotherMessage {
    data: String,
}

// ============================================================================
// Basic Recording Tests
// ============================================================================

#[tokio::test]
async fn test_recording_captures_send() {
    let mut handler = RecordingHandler::new(TestRole::Alice);

    let msg = TestMessage { value: 42 };
    handler
        .send(&mut (), TestRole::Bob, &msg)
        .await
        .expect("Send should succeed");

    let events = handler.events();
    assert_eq!(events.len(), 1);

    match &events[0] {
        RecordedEvent::Send { from, to, msg_type } => {
            assert_eq!(*from, TestRole::Alice);
            assert_eq!(*to, TestRole::Bob);
            assert!(msg_type.contains("TestMessage"));
        }
        _ => panic!("Expected Send event"),
    }
}

#[tokio::test]
async fn test_recording_captures_recv_then_fails() {
    let mut handler = RecordingHandler::new(TestRole::Bob);

    // recv() should record the event but return an error
    let result: Result<TestMessage, _> = handler.recv(&mut (), TestRole::Alice).await;

    assert!(result.is_err(), "recv() should return error by design");

    let events = handler.events();
    assert_eq!(events.len(), 1);

    match &events[0] {
        RecordedEvent::Recv { from, to, msg_type } => {
            assert_eq!(*from, TestRole::Alice);
            assert_eq!(*to, TestRole::Bob);
            assert!(msg_type.contains("TestMessage"));
        }
        _ => panic!("Expected Recv event"),
    }
}

#[tokio::test]
async fn test_recording_captures_choose() {
    let mut handler = RecordingHandler::new(TestRole::Alice);

    let label = TestLabel::Accept;
    handler
        .choose(&mut (), TestRole::Bob, label)
        .await
        .expect("Choose should succeed");

    let events = handler.events();
    assert_eq!(events.len(), 1);

    match &events[0] {
        RecordedEvent::Choose { at, label } => {
            assert_eq!(*at, TestRole::Bob);
            assert_eq!(*label, TestLabel::Accept);
        }
        _ => panic!("Expected Choose event"),
    }
}

#[tokio::test]
async fn test_recording_captures_offer_then_fails() {
    let mut handler = RecordingHandler::new(TestRole::Bob);

    // offer() should record the event but return an error
    let result = handler.offer(&mut (), TestRole::Alice).await;

    assert!(result.is_err(), "offer() should return error by design");

    let events = handler.events();
    assert_eq!(events.len(), 1);

    match &events[0] {
        RecordedEvent::Offer { from, to } => {
            assert_eq!(*from, TestRole::Alice);
            assert_eq!(*to, TestRole::Bob);
        }
        _ => panic!("Expected Offer event"),
    }
}

// ============================================================================
// Event Ordering Tests
// ============================================================================

#[tokio::test]
async fn test_recording_preserves_event_order() {
    let mut handler = RecordingHandler::new(TestRole::Alice);

    // Perform a sequence of operations
    handler
        .send(&mut (), TestRole::Bob, &TestMessage { value: 1 })
        .await
        .unwrap();
    handler
        .send(&mut (), TestRole::Charlie, &TestMessage { value: 2 })
        .await
        .unwrap();
    handler
        .choose(&mut (), TestRole::Bob, TestLabel::Option1)
        .await
        .unwrap();
    handler
        .send(&mut (), TestRole::Bob, &AnotherMessage {
            data: "test".to_string(),
        })
        .await
        .unwrap();

    let events = handler.events();
    assert_eq!(events.len(), 4);

    // Verify order
    match &events[0] {
        RecordedEvent::Send { to, .. } => assert_eq!(*to, TestRole::Bob),
        _ => panic!("Expected Send to Bob first"),
    }
    match &events[1] {
        RecordedEvent::Send { to, .. } => assert_eq!(*to, TestRole::Charlie),
        _ => panic!("Expected Send to Charlie second"),
    }
    match &events[2] {
        RecordedEvent::Choose { label, .. } => assert_eq!(*label, TestLabel::Option1),
        _ => panic!("Expected Choose third"),
    }
    match &events[3] {
        RecordedEvent::Send { to, msg_type, .. } => {
            assert_eq!(*to, TestRole::Bob);
            assert!(msg_type.contains("AnotherMessage"));
        }
        _ => panic!("Expected Send fourth"),
    }
}

// ============================================================================
// Clear and Events Access Tests
// ============================================================================

#[tokio::test]
async fn test_recording_clear() {
    let mut handler = RecordingHandler::new(TestRole::Alice);

    handler
        .send(&mut (), TestRole::Bob, &TestMessage { value: 1 })
        .await
        .unwrap();
    handler
        .send(&mut (), TestRole::Bob, &TestMessage { value: 2 })
        .await
        .unwrap();

    assert_eq!(handler.events().len(), 2);

    handler.clear();

    assert_eq!(handler.events().len(), 0);
}

#[tokio::test]
async fn test_recording_events_returns_clone() {
    let mut handler = RecordingHandler::new(TestRole::Alice);

    handler
        .send(&mut (), TestRole::Bob, &TestMessage { value: 1 })
        .await
        .unwrap();

    let events1 = handler.events();
    let events2 = handler.events();

    // Both calls should return the same events
    assert_eq!(events1.len(), events2.len());

    // Modifying handler doesn't affect already-returned events
    handler
        .send(&mut (), TestRole::Bob, &TestMessage { value: 2 })
        .await
        .unwrap();

    assert_eq!(events1.len(), 1); // Original clone unchanged
    assert_eq!(handler.events().len(), 2); // New call sees update
}

// ============================================================================
// Thread Safety Tests
// ============================================================================

#[tokio::test]
async fn test_recording_shared_across_clones() {
    let handler1 = RecordingHandler::new(TestRole::Alice);
    let mut handler2 = handler1.clone();

    // Send from cloned handler
    handler2
        .send(&mut (), TestRole::Bob, &TestMessage { value: 42 })
        .await
        .unwrap();

    // Original handler should see the event (shared Arc)
    let events = handler1.events();
    assert_eq!(events.len(), 1);
}

#[tokio::test]
async fn test_recording_concurrent_sends() {
    use std::sync::Arc;
    use tokio::sync::Barrier;

    let handler = RecordingHandler::new(TestRole::Alice);
    let barrier = Arc::new(Barrier::new(3));

    let mut handles = vec![];

    for i in 0..3 {
        let mut h = handler.clone();
        let b = barrier.clone();
        handles.push(tokio::spawn(async move {
            b.wait().await;
            h.send(&mut (), TestRole::Bob, &TestMessage { value: i })
                .await
                .unwrap();
        }));
    }

    for handle in handles {
        handle.await.unwrap();
    }

    let events = handler.events();
    assert_eq!(events.len(), 3, "All concurrent sends should be recorded");
}

// ============================================================================
// Error Message Tests
// ============================================================================

#[tokio::test]
async fn test_recv_error_message() {
    let mut handler = RecordingHandler::new(TestRole::Bob);

    let result: Result<TestMessage, _> = handler.recv(&mut (), TestRole::Alice).await;

    match result {
        Err(e) => {
            let msg = format!("{:?}", e);
            assert!(
                msg.contains("cannot produce values"),
                "Error should explain why recv fails"
            );
        }
        Ok(_) => panic!("Expected error"),
    }
}

#[tokio::test]
async fn test_offer_error_message() {
    let mut handler = RecordingHandler::new(TestRole::Bob);

    let result = handler.offer(&mut (), TestRole::Alice).await;

    match result {
        Err(e) => {
            let msg = format!("{:?}", e);
            assert!(
                msg.contains("cannot produce labels"),
                "Error should explain why offer fails"
            );
        }
        Ok(_) => panic!("Expected error"),
    }
}

// ============================================================================
// Message Type Tracking Tests
// ============================================================================

#[tokio::test]
async fn test_recording_tracks_message_types() {
    let mut handler = RecordingHandler::new(TestRole::Alice);

    handler
        .send(&mut (), TestRole::Bob, &TestMessage { value: 1 })
        .await
        .unwrap();
    handler
        .send(&mut (), TestRole::Bob, &AnotherMessage {
            data: "test".to_string(),
        })
        .await
        .unwrap();

    let events = handler.events();

    // First message type
    match &events[0] {
        RecordedEvent::Send { msg_type, .. } => {
            assert!(msg_type.contains("TestMessage"));
            assert!(!msg_type.contains("AnotherMessage"));
        }
        _ => panic!("Expected Send"),
    }

    // Second message type
    match &events[1] {
        RecordedEvent::Send { msg_type, .. } => {
            assert!(msg_type.contains("AnotherMessage"));
            assert!(!msg_type.contains("TestMessage"));
        }
        _ => panic!("Expected Send"),
    }
}

// ============================================================================
// Multiple Roles Tests
// ============================================================================

#[tokio::test]
async fn test_recording_different_roles() {
    // Create handlers for different roles
    let mut alice = RecordingHandler::new(TestRole::Alice);
    let mut bob = RecordingHandler::new(TestRole::Bob);

    // Alice sends to Bob
    alice
        .send(&mut (), TestRole::Bob, &TestMessage { value: 1 })
        .await
        .unwrap();

    // Bob sends to Charlie
    bob.send(&mut (), TestRole::Charlie, &TestMessage { value: 2 })
        .await
        .unwrap();

    // Each handler records its own events
    let alice_events = alice.events();
    let bob_events = bob.events();

    assert_eq!(alice_events.len(), 1);
    assert_eq!(bob_events.len(), 1);

    match &alice_events[0] {
        RecordedEvent::Send { from, to, .. } => {
            assert_eq!(*from, TestRole::Alice);
            assert_eq!(*to, TestRole::Bob);
        }
        _ => panic!("Expected Send"),
    }

    match &bob_events[0] {
        RecordedEvent::Send { from, to, .. } => {
            assert_eq!(*from, TestRole::Bob);
            assert_eq!(*to, TestRole::Charlie);
        }
        _ => panic!("Expected Send"),
    }
}

// ============================================================================
// Timeout Passthrough Test
// ============================================================================

#[tokio::test]
async fn test_recording_with_timeout_passthrough() {
    use std::time::Duration;

    let mut handler = RecordingHandler::new(TestRole::Alice);

    // with_timeout should just pass through to the body
    let result = handler
        .with_timeout(&mut (), TestRole::Alice, Duration::from_secs(1), async {
            Ok(42)
        })
        .await;

    assert_eq!(result.unwrap(), 42);
}
