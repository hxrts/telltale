//! Comprehensive tests for the Simulation Engine.
//!
//! Verifies:
//! - State machine transitions and BlockedOn states
//! - Checkpoint/restore roundtrip fidelity
//! - FaultyTransport chaos behavior with deterministic dropping
//! - MockClock determinism and reproducibility
//! - Observer event capture correctness

#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

use rumpsteak_aura_choreography::runtime::RoleId;
use rumpsteak_aura_choreography::simulation::{
    clock::{Clock, MockClock, Rng, SeededRng},
    envelope::ProtocolEnvelope,
    observer::{NullObserver, ProtocolEvent, ProtocolObserver, RecordingObserver},
    state_machine::{
        BlockedOn, Checkpoint, LinearStateMachine, ProtocolStateMachine, StepInput, StepOutput,
    },
    transport::{FaultyTransport, InMemoryTransport, SimulatedTransport, TransportError},
};
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::Duration;

// ============================================================================
// State Machine Transition Tests
// ============================================================================

#[test]
fn test_blocked_on_all_variants() {
    // Verify all BlockedOn variants exist and are distinguishable
    let send = BlockedOn::Send {
        to: RoleId::new("Bob"),
        message_type: "Request".to_string(),
    };
    let recv = BlockedOn::Recv {
        from: RoleId::new("Alice"),
        expected_types: vec!["Response".to_string()],
    };
    let choice = BlockedOn::Choice {
        branches: vec!["Accept".to_string(), "Reject".to_string()],
    };
    let offer = BlockedOn::Offer {
        from: RoleId::new("Alice"),
        branches: vec!["Accept".to_string(), "Reject".to_string()],
    };
    let complete = BlockedOn::Complete;
    let failed = BlockedOn::Failed("test failure".to_string());

    // Verify they're all distinct via Debug output
    assert!(format!("{:?}", send).contains("Send"));
    assert!(format!("{:?}", recv).contains("Recv"));
    assert!(format!("{:?}", choice).contains("Choice"));
    assert!(format!("{:?}", offer).contains("Offer"));
    assert!(format!("{:?}", complete).contains("Complete"));
    assert!(format!("{:?}", failed).contains("Failed"));
}

#[test]
fn test_blocked_on_is_terminal() {
    // Complete and Failed are terminal states
    assert!(BlockedOn::Complete.is_terminal());
    assert!(BlockedOn::Failed("error".to_string()).is_terminal());

    // Others are not terminal
    assert!(!BlockedOn::Send {
        to: RoleId::new("Bob"),
        message_type: "Msg".to_string()
    }
    .is_terminal());
    assert!(!BlockedOn::Recv {
        from: RoleId::new("Alice"),
        expected_types: vec!["Msg".to_string()]
    }
    .is_terminal());
    assert!(!BlockedOn::Choice {
        branches: vec![]
    }
    .is_terminal());
    assert!(!BlockedOn::Offer {
        from: RoleId::new("Alice"),
        branches: vec![]
    }
    .is_terminal());
}

#[test]
fn test_blocked_on_is_send() {
    assert!(BlockedOn::Send {
        to: RoleId::new("Bob"),
        message_type: "Msg".to_string()
    }
    .is_send());
    assert!(!BlockedOn::Recv {
        from: RoleId::new("Alice"),
        expected_types: vec![]
    }
    .is_send());
    assert!(!BlockedOn::Complete.is_send());
}

#[test]
fn test_blocked_on_is_recv() {
    assert!(BlockedOn::Recv {
        from: RoleId::new("Alice"),
        expected_types: vec!["Msg".to_string()]
    }
    .is_recv());
    assert!(!BlockedOn::Send {
        to: RoleId::new("Bob"),
        message_type: "Msg".to_string()
    }
    .is_recv());
    assert!(!BlockedOn::Complete.is_recv());
}

#[test]
fn test_blocked_on_is_choice() {
    // Both Choice and Offer count as choice states
    assert!(BlockedOn::Choice {
        branches: vec![]
    }
    .is_choice());
    assert!(BlockedOn::Offer {
        from: RoleId::new("Alice"),
        branches: vec![]
    }
    .is_choice());
    assert!(!BlockedOn::Send {
        to: RoleId::new("Bob"),
        message_type: "Msg".to_string()
    }
    .is_choice());
    assert!(!BlockedOn::Complete.is_choice());
}

#[test]
fn test_linear_state_machine_creation() {
    let states = vec![
        BlockedOn::Send {
            to: RoleId::new("Bob"),
            message_type: "Request".to_string(),
        },
        BlockedOn::Recv {
            from: RoleId::new("Bob"),
            expected_types: vec!["Response".to_string()],
        },
        BlockedOn::Complete,
    ];

    let sm = LinearStateMachine::new("TestProtocol", RoleId::new("Alice"), states.clone());

    assert_eq!(sm.protocol_name(), "TestProtocol");
    assert_eq!(sm.role().name, "Alice");
    assert!(matches!(sm.blocked_on(), BlockedOn::Send { .. }));
    assert_eq!(sm.sequence(), 0);
}

#[test]
fn test_linear_state_machine_step_sequence() {
    let states = vec![
        BlockedOn::Send {
            to: RoleId::new("Bob"),
            message_type: "Request".to_string(),
        },
        BlockedOn::Recv {
            from: RoleId::new("Bob"),
            expected_types: vec!["Response".to_string()],
        },
        BlockedOn::Complete,
    ];

    let mut sm = LinearStateMachine::new("TestProtocol", RoleId::new("Alice"), states);

    // Create envelopes for testing
    let send_env = ProtocolEnvelope::builder()
        .protocol("TestProtocol")
        .sender("Alice")
        .recipient("Bob")
        .message_type("Request")
        .payload(vec![1, 2, 3])
        .build()
        .unwrap();

    let recv_env = ProtocolEnvelope::builder()
        .protocol("TestProtocol")
        .sender("Bob")
        .recipient("Alice")
        .message_type("Response")
        .payload(vec![4, 5, 6])
        .build()
        .unwrap();

    // Step 1: Send
    assert!(sm.blocked_on().is_send());
    let output = sm.step(StepInput::send(send_env));
    assert!(output.is_ok());
    assert!(matches!(output.unwrap(), StepOutput::Sent(_)));
    assert_eq!(sm.sequence(), 1);

    // Step 2: Recv
    assert!(sm.blocked_on().is_recv());
    let output = sm.step(StepInput::recv(recv_env));
    assert!(output.is_ok());
    assert!(matches!(output.unwrap(), StepOutput::Received { .. }));
    assert_eq!(sm.sequence(), 2);

    // Step 3: Complete
    assert!(sm.blocked_on().is_terminal());
    assert!(sm.is_complete());
}

#[test]
fn test_linear_state_machine_wrong_input_type() {
    let states = vec![
        BlockedOn::Send {
            to: RoleId::new("Bob"),
            message_type: "Request".to_string(),
        },
        BlockedOn::Complete,
    ];

    let mut sm = LinearStateMachine::new("TestProtocol", RoleId::new("Alice"), states);

    // Create a recv envelope when expecting send
    let recv_env = ProtocolEnvelope::builder()
        .protocol("TestProtocol")
        .sender("Bob")
        .recipient("Alice")
        .message_type("Response")
        .payload(vec![])
        .build()
        .unwrap();

    // Try to receive when expecting send - should return NoProgress
    let result = sm.step(StepInput::recv(recv_env));
    assert!(result.is_ok());
    assert!(matches!(result.unwrap(), StepOutput::NoProgress));
}

#[test]
fn test_linear_state_machine_choice_step() {
    let states = vec![
        BlockedOn::Choice {
            branches: vec!["Accept".to_string(), "Reject".to_string()],
        },
        BlockedOn::Complete,
    ];

    let mut sm = LinearStateMachine::new("ChoiceProtocol", RoleId::new("Alice"), states);

    // Make a choice
    let result = sm.step(StepInput::choice("Accept"));
    assert!(result.is_ok());
    assert!(matches!(result.unwrap(), StepOutput::ChoiceMade(_)));
    assert_eq!(sm.sequence(), 1);
}

#[test]
fn test_linear_state_machine_invalid_choice_label() {
    let states = vec![
        BlockedOn::Choice {
            branches: vec!["Accept".to_string(), "Reject".to_string()],
        },
        BlockedOn::Complete,
    ];

    let mut sm = LinearStateMachine::new("ChoiceProtocol", RoleId::new("Alice"), states);

    // Invalid label should fail
    let result = sm.step(StepInput::choice("Invalid"));
    assert!(result.is_err());
}

#[test]
fn test_linear_state_machine_offer_step() {
    let states = vec![
        BlockedOn::Offer {
            from: RoleId::new("Alice"),
            branches: vec!["Accept".to_string(), "Reject".to_string()],
        },
        BlockedOn::Complete,
    ];

    let mut sm = LinearStateMachine::new("OfferProtocol", RoleId::new("Bob"), states);

    // Receive an offer
    let result = sm.step(StepInput::offer("Accept"));
    assert!(result.is_ok());
    assert!(matches!(result.unwrap(), StepOutput::OfferReceived(_)));
    assert_eq!(sm.sequence(), 1);
}

#[test]
fn test_linear_state_machine_invalid_offer_label() {
    let states = vec![
        BlockedOn::Offer {
            from: RoleId::new("Alice"),
            branches: vec!["Accept".to_string(), "Reject".to_string()],
        },
        BlockedOn::Complete,
    ];

    let mut sm = LinearStateMachine::new("OfferProtocol", RoleId::new("Bob"), states);

    // Invalid label should fail
    let result = sm.step(StepInput::offer("Invalid"));
    assert!(result.is_err());
}

#[test]
fn test_linear_state_machine_complete_returns_completed() {
    let states = vec![BlockedOn::Complete];

    let mut sm = LinearStateMachine::new("CompleteProto", RoleId::new("Alice"), states);

    assert!(sm.is_complete());

    // Any input should return Completed
    let result = sm.step(StepInput::choice("anything"));
    assert!(result.is_ok());
    assert!(matches!(result.unwrap(), StepOutput::Completed));
}

#[test]
fn test_linear_state_machine_failed_returns_error() {
    let states = vec![BlockedOn::Failed("Protocol error".to_string())];

    let mut sm = LinearStateMachine::new("FailedProto", RoleId::new("Alice"), states);

    assert!(sm.is_complete()); // Failed is terminal

    // Any input should return error
    let result = sm.step(StepInput::choice("anything"));
    assert!(result.is_err());
}

// ============================================================================
// Checkpoint/Restore Tests
// ============================================================================

#[test]
fn test_checkpoint_creation() {
    let states = vec![
        BlockedOn::Send {
            to: RoleId::new("Bob"),
            message_type: "Request".to_string(),
        },
        BlockedOn::Recv {
            from: RoleId::new("Bob"),
            expected_types: vec!["Response".to_string()],
        },
        BlockedOn::Complete,
    ];

    let sm = LinearStateMachine::new("TestProtocol", RoleId::new("Alice"), states);
    let checkpoint = sm.checkpoint().unwrap();

    assert_eq!(checkpoint.protocol, "TestProtocol");
    assert_eq!(checkpoint.role, "Alice");
    assert_eq!(checkpoint.sequence, 0);
}

#[test]
fn test_checkpoint_roundtrip() {
    let states = vec![
        BlockedOn::Send {
            to: RoleId::new("Bob"),
            message_type: "Request".to_string(),
        },
        BlockedOn::Recv {
            from: RoleId::new("Bob"),
            expected_types: vec!["Response".to_string()],
        },
        BlockedOn::Complete,
    ];

    let mut sm = LinearStateMachine::new("TestProtocol", RoleId::new("Alice"), states.clone());

    // Advance state machine
    let send_env = ProtocolEnvelope::builder()
        .protocol("TestProtocol")
        .sender("Alice")
        .recipient("Bob")
        .message_type("Request")
        .payload(vec![])
        .build()
        .unwrap();

    sm.step(StepInput::send(send_env)).unwrap();
    assert_eq!(sm.sequence(), 1);

    // Take checkpoint
    let checkpoint = sm.checkpoint().unwrap();
    assert_eq!(checkpoint.sequence, 1);

    // Create new state machine and restore
    let mut sm2 = LinearStateMachine::new("TestProtocol", RoleId::new("Alice"), states);
    sm2.restore(&checkpoint).unwrap();

    // Verify restored state
    assert_eq!(sm2.sequence(), 1);
    assert!(sm2.blocked_on().is_recv());
}

#[test]
fn test_checkpoint_serialization() {
    let checkpoint = Checkpoint::new("TestProtocol", "Alice", "state_0")
        .with_data(vec![1, 2, 3, 4, 5])
        .with_sequence(5)
        .with_metadata("key", "value");

    // Serialize with bincode via to_bytes
    let bytes = checkpoint.to_bytes().expect("Serialize should succeed");

    // Deserialize
    let restored = Checkpoint::from_bytes(&bytes).expect("Deserialize should succeed");

    assert_eq!(restored.protocol, checkpoint.protocol);
    assert_eq!(restored.role, checkpoint.role);
    assert_eq!(restored.sequence, checkpoint.sequence);
    assert_eq!(restored.state_data, checkpoint.state_data);
    assert_eq!(restored.metadata.get("key"), Some(&"value".to_string()));
}

#[test]
fn test_checkpoint_protocol_mismatch() {
    let states = vec![BlockedOn::Complete];

    let mut sm = LinearStateMachine::new("ProtocolA", RoleId::new("Alice"), states);

    let wrong_checkpoint = Checkpoint::new("ProtocolB", "Alice", "state_0");

    // Restore should fail for mismatched protocol
    let result = sm.restore(&wrong_checkpoint);
    assert!(result.is_err());
}

// ============================================================================
// MockClock Determinism Tests
// ============================================================================

#[test]
fn test_mock_clock_initial_state() {
    let clock = MockClock::new();
    let offset = clock.offset();

    // Clock should start at zero offset
    assert_eq!(offset.as_nanos(), 0);
}

#[test]
fn test_mock_clock_advance() {
    let clock = MockClock::new();

    clock.advance(Duration::from_secs(10));
    assert_eq!(clock.offset().as_secs(), 10);

    clock.advance(Duration::from_millis(500));
    assert_eq!(clock.offset().as_millis(), 10500);
}

#[test]
fn test_mock_clock_set_offset() {
    let clock = MockClock::new();

    clock.set_offset(Duration::from_secs(100));
    assert_eq!(clock.offset().as_secs(), 100);

    // Can go backwards
    clock.set_offset(Duration::from_secs(50));
    assert_eq!(clock.offset().as_secs(), 50);
}

#[test]
fn test_mock_clock_determinism_across_instances() {
    // Two mock clocks with same operations should have same offset
    let clock1 = MockClock::new();
    let clock2 = MockClock::new();

    clock1.advance(Duration::from_secs(100));
    clock2.advance(Duration::from_secs(100));

    assert_eq!(clock1.offset(), clock2.offset());
}

#[test]
fn test_mock_clock_thread_safe() {
    use std::thread;

    let clock = Arc::new(MockClock::new());
    let mut handles = vec![];

    // Advance from multiple threads
    for i in 0..10 {
        let c = clock.clone();
        handles.push(thread::spawn(move || {
            c.advance(Duration::from_millis(i * 10));
        }));
    }

    for h in handles {
        h.join().unwrap();
    }

    // Total should be 0+10+20+...+90 = 450ms
    assert_eq!(clock.offset().as_millis(), 450);
}

#[test]
fn test_mock_clock_elapsed() {
    let clock = MockClock::new();
    let start = clock.now();

    clock.advance(Duration::from_secs(5));
    let elapsed = clock.elapsed(start);

    assert!(elapsed >= Duration::from_secs(5));
}

// ============================================================================
// SeededRng Determinism Tests
// ============================================================================

#[test]
fn test_seeded_rng_reproducible() {
    let mut rng1 = SeededRng::new(12345);
    let mut rng2 = SeededRng::new(12345);

    // Same seed should produce same sequence
    for _ in 0..100 {
        assert_eq!(rng1.next_u64(), rng2.next_u64());
    }
}

#[test]
fn test_seeded_rng_different_seeds() {
    let mut rng1 = SeededRng::new(12345);
    let mut rng2 = SeededRng::new(54321);

    // Different seeds should produce different sequences
    let mut same_count = 0;
    for _ in 0..100 {
        if rng1.next_u64() == rng2.next_u64() {
            same_count += 1;
        }
    }

    // Extremely unlikely to have more than a few matches
    assert!(same_count < 5);
}

#[test]
fn test_seeded_rng_choose() {
    let mut rng = SeededRng::new(42);

    let options = vec!["a", "b", "c", "d"];

    // Should choose valid options
    for _ in 0..100 {
        let choice = rng.choose(&options);
        assert!(choice.is_some());
        assert!(options.contains(choice.unwrap()));
    }
}

#[test]
fn test_seeded_rng_choose_deterministic() {
    let options = vec!["a", "b", "c", "d"];

    let mut rng1 = SeededRng::new(999);
    let mut rng2 = SeededRng::new(999);

    // Same seed should make same choices
    for _ in 0..50 {
        assert_eq!(rng1.choose(&options), rng2.choose(&options));
    }
}

#[test]
fn test_seeded_rng_choose_empty() {
    let mut rng = SeededRng::new(42);
    let empty: Vec<i32> = vec![];

    assert!(rng.choose(&empty).is_none());
}

#[test]
fn test_seeded_rng_next_bool() {
    let mut rng = SeededRng::new(42);

    // Over many iterations, should get both true and false
    let mut trues = 0;
    let mut falses = 0;
    for _ in 0..1000 {
        if rng.next_bool() {
            trues += 1;
        } else {
            falses += 1;
        }
    }

    // Should have a reasonable distribution (not all one value)
    assert!(trues > 100);
    assert!(falses > 100);
}

#[test]
fn test_seeded_rng_next_f64_range() {
    let mut rng = SeededRng::new(42);

    for _ in 0..1000 {
        let f = rng.next_f64();
        assert!(f >= 0.0 && f < 1.0, "f64 should be in [0, 1), got {}", f);
    }
}

#[test]
fn test_seeded_rng_duration_between() {
    let mut rng = SeededRng::new(42);

    let min = Duration::from_millis(100);
    let max = Duration::from_millis(200);

    for _ in 0..100 {
        let d = rng.duration_between(min, max);
        assert!(d >= min && d < max);
    }
}

#[test]
fn test_seeded_rng_duration_between_same() {
    let mut rng = SeededRng::new(42);

    let same = Duration::from_millis(100);

    // When min == max, should return min
    let d = rng.duration_between(same, same);
    assert_eq!(d, same);
}

#[test]
fn test_seeded_rng_state_save_restore() {
    let mut rng = SeededRng::new(12345);

    // Generate some values
    for _ in 0..10 {
        rng.next_u64();
    }

    // Save state
    let saved_state = rng.state();

    // Generate more values and record them
    let mut expected = vec![];
    for _ in 0..10 {
        expected.push(rng.next_u64());
    }

    // Restore state
    rng.restore(saved_state);

    // Should get same values
    for exp in expected {
        assert_eq!(rng.next_u64(), exp);
    }
}

// ============================================================================
// InMemoryTransport Tests
// ============================================================================

fn make_envelope(from: &str, to: &str, msg_type: &str) -> ProtocolEnvelope {
    ProtocolEnvelope::builder()
        .protocol("Test")
        .sender(from)
        .recipient(to)
        .message_type(msg_type)
        .payload(vec![1, 2, 3])
        .build()
        .unwrap()
}

#[test]
fn test_in_memory_transport_send_recv() {
    let queues = Arc::new(Mutex::new(HashMap::new()));

    let mut client = InMemoryTransport::with_shared_queues(Arc::clone(&queues));
    client.set_role(RoleId::new("Client"));

    let mut server = InMemoryTransport::with_shared_queues(Arc::clone(&queues));
    server.set_role(RoleId::new("Server"));

    let envelope = make_envelope("Client", "Server", "Request");
    SimulatedTransport::send(&mut client, RoleId::new("Server"), envelope).unwrap();

    let received = SimulatedTransport::recv(&mut server, RoleId::new("Client")).unwrap();
    assert_eq!(received.from_role, "Client");
    assert_eq!(received.to_role, "Server");
    assert_eq!(received.payload, vec![1, 2, 3]);
}

#[test]
fn test_in_memory_transport_fifo_ordering() {
    let queues = Arc::new(Mutex::new(HashMap::new()));

    let mut client = InMemoryTransport::with_shared_queues(Arc::clone(&queues));
    client.set_role(RoleId::new("Client"));

    let mut server = InMemoryTransport::with_shared_queues(Arc::clone(&queues));
    server.set_role(RoleId::new("Server"));

    // Send multiple messages
    for i in 0..5 {
        let envelope = ProtocolEnvelope::builder()
            .protocol("Test")
            .sender("Client")
            .recipient("Server")
            .message_type("Msg")
            .sequence(i)
            .payload(vec![i as u8])
            .build()
            .unwrap();
        SimulatedTransport::send(&mut client, RoleId::new("Server"), envelope).unwrap();
    }

    // Receive in FIFO order
    for i in 0..5 {
        let received = SimulatedTransport::recv(&mut server, RoleId::new("Client")).unwrap();
        assert_eq!(received.sequence, i);
        assert_eq!(received.payload, vec![i as u8]);
    }
}

#[test]
fn test_in_memory_transport_no_message() {
    let mut transport = InMemoryTransport::new();
    transport.set_role(RoleId::new("Client"));

    // No messages for Client
    let result = SimulatedTransport::recv(&mut transport, RoleId::new("Server"));
    assert!(matches!(result, Err(TransportError::NoMessage(_))));
}

#[test]
fn test_in_memory_transport_peek() {
    let queues = Arc::new(Mutex::new(HashMap::new()));

    let mut client = InMemoryTransport::with_shared_queues(Arc::clone(&queues));
    client.set_role(RoleId::new("Client"));

    let mut server = InMemoryTransport::with_shared_queues(Arc::clone(&queues));
    server.set_role(RoleId::new("Server"));

    // No messages yet
    assert!(!server.peek(RoleId::new("Client")));

    // Send a message
    let envelope = make_envelope("Client", "Server", "Request");
    SimulatedTransport::send(&mut client, RoleId::new("Server"), envelope).unwrap();

    // Now there's a message
    assert!(server.peek(RoleId::new("Client")));

    // Consume it
    let _ = SimulatedTransport::recv(&mut server, RoleId::new("Client")).unwrap();

    // No more messages
    assert!(!server.peek(RoleId::new("Client")));
}

#[test]
fn test_in_memory_transport_multiple_recipients() {
    let queues = Arc::new(Mutex::new(HashMap::new()));

    let mut alice = InMemoryTransport::with_shared_queues(Arc::clone(&queues));
    alice.set_role(RoleId::new("Alice"));

    let mut bob = InMemoryTransport::with_shared_queues(Arc::clone(&queues));
    bob.set_role(RoleId::new("Bob"));

    let mut charlie = InMemoryTransport::with_shared_queues(Arc::clone(&queues));
    charlie.set_role(RoleId::new("Charlie"));

    // Alice sends to Bob and Charlie
    let env_bob = ProtocolEnvelope::builder()
        .protocol("Test")
        .sender("Alice")
        .recipient("Bob")
        .message_type("Msg")
        .payload(vec![1])
        .build()
        .unwrap();

    let env_charlie = ProtocolEnvelope::builder()
        .protocol("Test")
        .sender("Alice")
        .recipient("Charlie")
        .message_type("Msg")
        .payload(vec![2])
        .build()
        .unwrap();

    SimulatedTransport::send(&mut alice, RoleId::new("Bob"), env_bob).unwrap();
    SimulatedTransport::send(&mut alice, RoleId::new("Charlie"), env_charlie).unwrap();

    // Bob gets his message
    let bob_msg = SimulatedTransport::recv(&mut bob, RoleId::new("Alice")).unwrap();
    assert_eq!(bob_msg.payload, vec![1]);

    // Charlie gets his message
    let charlie_msg = SimulatedTransport::recv(&mut charlie, RoleId::new("Alice")).unwrap();
    assert_eq!(charlie_msg.payload, vec![2]);
}

#[test]
fn test_in_memory_transport_pending_count() {
    let queues = Arc::new(Mutex::new(HashMap::new()));

    let mut client = InMemoryTransport::with_shared_queues(Arc::clone(&queues));
    client.set_role(RoleId::new("Client"));

    assert_eq!(client.pending_count(), 0);

    // Send some messages
    for _ in 0..3 {
        let envelope = make_envelope("Client", "Server", "Msg");
        SimulatedTransport::send(&mut client, RoleId::new("Server"), envelope).unwrap();
    }

    assert_eq!(client.pending_count(), 3);

    // Clear
    client.clear();
    assert_eq!(client.pending_count(), 0);
}

#[test]
fn test_in_memory_transport_thread_safe() {
    use std::thread;

    let queues = Arc::new(Mutex::new(HashMap::new()));

    let mut handles = vec![];

    for i in 0..10 {
        let q = Arc::clone(&queues);
        handles.push(thread::spawn(move || {
            let mut transport = InMemoryTransport::with_shared_queues(q);
            transport.set_role(RoleId::new("Client"));

            let envelope = ProtocolEnvelope::builder()
                .protocol("Test")
                .sender("Client")
                .recipient("Server")
                .message_type("Msg")
                .payload(vec![i])
                .build()
                .unwrap();
            SimulatedTransport::send(&mut transport, RoleId::new("Server"), envelope).unwrap();
        }));
    }

    for h in handles {
        h.join().unwrap();
    }

    // All 10 messages should be there
    let mut server = InMemoryTransport::with_shared_queues(queues);
    server.set_role(RoleId::new("Server"));

    let mut received = vec![];
    while let Ok(env) = SimulatedTransport::recv(&mut server, RoleId::new("Client")) {
        received.push(env.payload[0]);
    }
    received.sort();
    assert_eq!(received, (0..10).collect::<Vec<_>>());
}

// ============================================================================
// FaultyTransport Chaos Tests
// ============================================================================

#[test]
fn test_faulty_transport_zero_drop_rate() {
    let queues = Arc::new(Mutex::new(HashMap::new()));
    let mut inner = InMemoryTransport::with_shared_queues(Arc::clone(&queues));
    inner.set_role(RoleId::new("Client"));

    let mut faulty = FaultyTransport::new(inner).with_drop_rate(0.0).with_seed(12345);

    // 0% drop rate should deliver all messages
    for i in 0u8..10 {
        let envelope = ProtocolEnvelope::builder()
            .protocol("Test")
            .sender("Client")
            .recipient("Server")
            .message_type("Msg")
            .payload(vec![i])
            .build()
            .unwrap();
        faulty.send(RoleId::new("Server"), envelope).unwrap();
    }

    // All should be received
    let mut server = InMemoryTransport::with_shared_queues(queues);
    server.set_role(RoleId::new("Server"));

    for i in 0u8..10 {
        let received = SimulatedTransport::recv(&mut server, RoleId::new("Client")).unwrap();
        assert_eq!(received.payload, vec![i]);
    }
}

#[test]
fn test_faulty_transport_full_drop_rate() {
    let queues = Arc::new(Mutex::new(HashMap::new()));
    let mut inner = InMemoryTransport::with_shared_queues(Arc::clone(&queues));
    inner.set_role(RoleId::new("Client"));

    let mut faulty = FaultyTransport::new(inner).with_drop_rate(1.0).with_seed(12345);

    // 100% drop rate should drop all messages
    for i in 0u8..10 {
        let envelope = ProtocolEnvelope::builder()
            .protocol("Test")
            .sender("Client")
            .recipient("Server")
            .message_type("Msg")
            .payload(vec![i])
            .build()
            .unwrap();
        faulty.send(RoleId::new("Server"), envelope).unwrap(); // Still "succeeds" but message is dropped
    }

    // None should be received - check via server transport
    let mut server = InMemoryTransport::with_shared_queues(queues);
    server.set_role(RoleId::new("Server"));
    assert!(SimulatedTransport::recv(&mut server, RoleId::new("Client")).is_err());
}

#[test]
fn test_faulty_transport_deterministic_dropping() {
    // Same seed should produce same drop pattern
    let queues1 = Arc::new(Mutex::new(HashMap::new()));
    let queues2 = Arc::new(Mutex::new(HashMap::new()));

    let mut inner1 = InMemoryTransport::with_shared_queues(Arc::clone(&queues1));
    inner1.set_role(RoleId::new("Client"));
    let mut inner2 = InMemoryTransport::with_shared_queues(Arc::clone(&queues2));
    inner2.set_role(RoleId::new("Client"));

    let mut faulty1 = FaultyTransport::new(inner1).with_drop_rate(0.5).with_seed(42);
    let mut faulty2 = FaultyTransport::new(inner2).with_drop_rate(0.5).with_seed(42);

    for i in 0u8..100 {
        let envelope = ProtocolEnvelope::builder()
            .protocol("Test")
            .sender("Client")
            .recipient("Server")
            .message_type("Msg")
            .payload(vec![i])
            .build()
            .unwrap();
        faulty1.send(RoleId::new("Server"), envelope.clone()).unwrap();
        faulty2.send(RoleId::new("Server"), envelope).unwrap();
    }

    // Both should have same messages (same drop pattern)
    let mut server1 = InMemoryTransport::with_shared_queues(queues1);
    server1.set_role(RoleId::new("Server"));
    let mut server2 = InMemoryTransport::with_shared_queues(queues2);
    server2.set_role(RoleId::new("Server"));

    let mut received1 = vec![];
    let mut received2 = vec![];

    while let Ok(env) = SimulatedTransport::recv(&mut server1, RoleId::new("Client")) {
        received1.push(env.payload[0]);
    }
    while let Ok(env) = SimulatedTransport::recv(&mut server2, RoleId::new("Client")) {
        received2.push(env.payload[0]);
    }

    assert_eq!(received1, received2);
}

#[test]
fn test_faulty_transport_different_seeds_different_drops() {
    let queues1 = Arc::new(Mutex::new(HashMap::new()));
    let queues2 = Arc::new(Mutex::new(HashMap::new()));

    let mut inner1 = InMemoryTransport::with_shared_queues(Arc::clone(&queues1));
    inner1.set_role(RoleId::new("Client"));
    let mut inner2 = InMemoryTransport::with_shared_queues(Arc::clone(&queues2));
    inner2.set_role(RoleId::new("Client"));

    let mut faulty1 = FaultyTransport::new(inner1).with_drop_rate(0.5).with_seed(111);
    let mut faulty2 = FaultyTransport::new(inner2).with_drop_rate(0.5).with_seed(222);

    for i in 0u8..100 {
        let envelope = ProtocolEnvelope::builder()
            .protocol("Test")
            .sender("Client")
            .recipient("Server")
            .message_type("Msg")
            .payload(vec![i])
            .build()
            .unwrap();
        faulty1.send(RoleId::new("Server"), envelope.clone()).unwrap();
        faulty2.send(RoleId::new("Server"), envelope).unwrap();
    }

    let mut server1 = InMemoryTransport::with_shared_queues(queues1);
    server1.set_role(RoleId::new("Server"));
    let mut server2 = InMemoryTransport::with_shared_queues(queues2);
    server2.set_role(RoleId::new("Server"));

    let mut received1 = vec![];
    let mut received2 = vec![];

    while let Ok(env) = SimulatedTransport::recv(&mut server1, RoleId::new("Client")) {
        received1.push(env.payload[0]);
    }
    while let Ok(env) = SimulatedTransport::recv(&mut server2, RoleId::new("Client")) {
        received2.push(env.payload[0]);
    }

    // Different seeds should (very likely) produce different patterns
    assert_ne!(received1, received2);
}

#[test]
fn test_faulty_transport_partial_drop_rate() {
    let queues = Arc::new(Mutex::new(HashMap::new()));
    let mut inner = InMemoryTransport::with_shared_queues(Arc::clone(&queues));
    inner.set_role(RoleId::new("Client"));

    let mut faulty = FaultyTransport::new(inner).with_drop_rate(0.3).with_seed(12345);

    let send_count = 1000;
    for i in 0..send_count {
        let envelope = ProtocolEnvelope::builder()
            .protocol("Test")
            .sender("Client")
            .recipient("Server")
            .message_type("Msg")
            .payload(vec![(i % 256) as u8])
            .build()
            .unwrap();
        faulty.send(RoleId::new("Server"), envelope).unwrap();
    }

    let mut server = InMemoryTransport::with_shared_queues(queues);
    server.set_role(RoleId::new("Server"));

    let mut recv_count = 0;
    while SimulatedTransport::recv(&mut server, RoleId::new("Client")).is_ok() {
        recv_count += 1;
    }

    // With 30% drop rate, expect roughly 70% to arrive
    // Allow for statistical variation (60-80% range)
    let expected_min = (send_count as f64 * 0.6) as i32;
    let expected_max = (send_count as f64 * 0.8) as i32;
    assert!(
        recv_count >= expected_min && recv_count <= expected_max,
        "Expected {}-{} messages, got {}",
        expected_min,
        expected_max,
        recv_count
    );
}

// ============================================================================
// Envelope Tests
// ============================================================================

#[test]
fn test_envelope_builder_complete() {
    let envelope = ProtocolEnvelope::builder()
        .protocol("TestProtocol")
        .sender("Alice")
        .recipient("Bob")
        .message_type("Request")
        .payload(vec![1, 2, 3])
        .sequence(42)
        .correlation_id("corr-123")
        .build()
        .unwrap();

    assert_eq!(envelope.protocol, "TestProtocol");
    assert_eq!(envelope.from_role, "Alice");
    assert_eq!(envelope.to_role, "Bob");
    assert_eq!(envelope.message_type, "Request");
    assert_eq!(envelope.payload, vec![1, 2, 3]);
    assert_eq!(envelope.sequence, 42);
    assert_eq!(envelope.correlation_id, Some("corr-123".to_string()));
}

#[test]
fn test_envelope_builder_with_indices() {
    let envelope = ProtocolEnvelope::builder()
        .protocol("TestProtocol")
        .sender("Worker")
        .sender_index(3)
        .recipient("Manager")
        .recipient_index(0)
        .message_type("Status")
        .payload(vec![])
        .build()
        .unwrap();

    assert_eq!(envelope.from_index, Some(3));
    assert_eq!(envelope.to_index, Some(0));
}

#[test]
fn test_envelope_builder_missing_protocol() {
    let result = ProtocolEnvelope::builder()
        .sender("Alice")
        .recipient("Bob")
        .message_type("Request")
        .payload(vec![])
        .build();

    assert!(result.is_err());
}

#[test]
fn test_envelope_builder_missing_sender() {
    let result = ProtocolEnvelope::builder()
        .protocol("Test")
        .recipient("Bob")
        .message_type("Request")
        .payload(vec![])
        .build();

    assert!(result.is_err());
}

#[test]
fn test_envelope_builder_missing_recipient() {
    let result = ProtocolEnvelope::builder()
        .protocol("Test")
        .sender("Alice")
        .message_type("Request")
        .payload(vec![])
        .build();

    assert!(result.is_err());
}

#[test]
fn test_envelope_routing_key() {
    let simple = ProtocolEnvelope::builder()
        .protocol("Proto")
        .sender("A")
        .recipient("B")
        .message_type("Msg")
        .payload(vec![])
        .build()
        .unwrap();

    assert_eq!(simple.routing_key(), "Proto.A.B");

    let indexed_sender = ProtocolEnvelope::builder()
        .protocol("Proto")
        .sender("Worker")
        .sender_index(0)
        .recipient("Manager")
        .message_type("Msg")
        .payload(vec![])
        .build()
        .unwrap();

    assert_eq!(indexed_sender.routing_key(), "Proto.Worker[0].Manager");
}

#[test]
fn test_envelope_serialization_roundtrip() {
    let envelope = ProtocolEnvelope::builder()
        .protocol("Test")
        .sender("Alice")
        .recipient("Bob")
        .message_type("Request")
        .payload(vec![1, 2, 3, 4, 5])
        .sequence(99)
        .correlation_id("test-corr")
        .build()
        .unwrap();

    let bytes = envelope.to_bytes().expect("Serialize should succeed");
    let restored = ProtocolEnvelope::from_bytes(&bytes).expect("Deserialize should succeed");

    assert_eq!(restored.protocol, envelope.protocol);
    assert_eq!(restored.from_role, envelope.from_role);
    assert_eq!(restored.to_role, envelope.to_role);
    assert_eq!(restored.message_type, envelope.message_type);
    assert_eq!(restored.payload, envelope.payload);
    assert_eq!(restored.sequence, envelope.sequence);
    assert_eq!(restored.correlation_id, envelope.correlation_id);
}

#[test]
fn test_envelope_predicates() {
    let envelope = ProtocolEnvelope::builder()
        .protocol("TestProtocol")
        .sender("Alice")
        .recipient("Bob")
        .message_type("Request")
        .payload(vec![])
        .build()
        .unwrap();

    assert!(envelope.is_protocol("TestProtocol"));
    assert!(!envelope.is_protocol("OtherProtocol"));

    assert!(envelope.is_from("Alice"));
    assert!(!envelope.is_from("Bob"));

    assert!(envelope.is_to("Bob"));
    assert!(!envelope.is_to("Alice"));
}

#[test]
fn test_envelope_payload_size() {
    let envelope = ProtocolEnvelope::builder()
        .protocol("Test")
        .sender("A")
        .recipient("B")
        .message_type("Msg")
        .payload(vec![0u8; 100])
        .build()
        .unwrap();

    assert_eq!(envelope.payload_size(), 100);
}

// ============================================================================
// Observer Tests
// ============================================================================

#[test]
fn test_null_observer_accepts_all() {
    let mut observer = NullObserver;

    // NullObserver should accept all events silently
    observer.on_send("Alice", "Bob", "Request", 100);
    observer.on_recv("Bob", "Alice", "Response", 50);
    observer.on_choice("Alice", "Accept");
    observer.on_offer("Alice", "Accept");
    observer.on_phase_start("TestProtocol", "Alice", "handshake");
    observer.on_phase_end("TestProtocol", "Alice", "handshake");
    observer.on_complete("TestProtocol", "Alice");

    // No assertions - just verify it doesn't panic
}

#[test]
fn test_recording_observer_captures_events() {
    let mut observer = RecordingObserver::new();

    observer.on_send("Alice", "Bob", "Request", 100);
    observer.on_recv("Bob", "Alice", "Response", 50);
    observer.on_choice("Alice", "Accept");

    assert_eq!(observer.len(), 3);
}

#[test]
fn test_recording_observer_event_order() {
    let mut observer = RecordingObserver::new();

    observer.on_phase_start("TestProtocol", "Alice", "handshake");
    observer.on_send("Alice", "Bob", "Request", 100);
    observer.on_recv("Alice", "Bob", "Response", 50);
    observer.on_phase_end("TestProtocol", "Alice", "handshake");

    let events = observer.events();
    assert_eq!(events.len(), 4);

    // Verify order by checking event types
    assert!(matches!(events[0], ProtocolEvent::PhaseStart { .. }));
    assert!(matches!(events[1], ProtocolEvent::Send { .. }));
    assert!(matches!(events[2], ProtocolEvent::Recv { .. }));
    assert!(matches!(events[3], ProtocolEvent::PhaseEnd { .. }));
}

#[test]
fn test_recording_observer_take_clears() {
    let mut observer = RecordingObserver::new();

    observer.on_send("Alice", "Bob", "Request", 10);
    observer.on_send("Alice", "Bob", "Request", 20);

    let events = observer.take_events();
    assert_eq!(events.len(), 2);

    // After take, observer should be empty
    assert!(observer.is_empty());
}

#[test]
fn test_recording_observer_clear() {
    let mut observer = RecordingObserver::new();

    observer.on_send("Alice", "Bob", "Request", 10);
    observer.on_send("Alice", "Bob", "Request", 20);
    assert_eq!(observer.len(), 2);

    observer.clear();
    assert_eq!(observer.len(), 0);
    assert!(observer.is_empty());
}

#[test]
fn test_recording_observer_sends_filter() {
    let mut observer = RecordingObserver::new();

    observer.on_send("Alice", "Bob", "Request", 10);
    observer.on_recv("Bob", "Alice", "Response", 20);
    observer.on_send("Alice", "Charlie", "Request", 30);
    observer.on_choice("Alice", "Accept");

    // Should only count sends
    assert_eq!(observer.sends().count(), 2);
}

#[test]
fn test_recording_observer_recvs_filter() {
    let mut observer = RecordingObserver::new();

    observer.on_send("Alice", "Bob", "Request", 10);
    observer.on_recv("Bob", "Alice", "Response", 20);
    observer.on_recv("Charlie", "Alice", "Response", 30);
    observer.on_choice("Alice", "Accept");

    // Should only count recvs
    assert_eq!(observer.recvs().count(), 2);
}

#[test]
fn test_recording_observer_errors_filter() {
    use rumpsteak_aura_choreography::effects::ChoreographyError;

    let mut observer = RecordingObserver::new();

    observer.on_send("Alice", "Bob", "Request", 10);
    observer.on_error(
        "TestProto",
        "Alice",
        &ChoreographyError::ExecutionError("test error".to_string()),
    );
    observer.on_complete("TestProto", "Alice");

    assert_eq!(observer.errors().count(), 1);
}

#[test]
fn test_recording_observer_captures_complete() {
    let mut observer = RecordingObserver::new();

    observer.on_phase_start("TestProtocol", "Alice", "main");
    observer.on_complete("TestProtocol", "Alice");

    let events = observer.events();
    assert_eq!(events.len(), 2);

    match &events[1] {
        ProtocolEvent::Complete { protocol, role } => {
            assert_eq!(protocol, "TestProtocol");
            assert_eq!(role, "Alice");
        }
        _ => panic!("Expected Complete event"),
    }
}
