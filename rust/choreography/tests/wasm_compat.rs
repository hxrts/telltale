#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]
// WASM compatibility tests for choreography system
//
// These tests verify that core choreographic programming features
// work correctly when compiled to WASM.
#![cfg(target_arch = "wasm32")]

use rumpsteak_aura_choreography::{
    interpret, Effect, InMemoryHandler, InterpretResult, InterpreterState, Label, Program, RoleId,
};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::Duration;
use wasm_bindgen_test::*;

wasm_bindgen_test_configure!(run_in_browser);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
enum TestRole {
    Alice,
    Bob,
}

// RoleId is automatically implemented via blanket impl

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
enum TestMessage {
    Hello(String),
    Goodbye,
    Number(i32),
}

#[wasm_bindgen_test]
fn test_role_id_trait() {
    let alice = TestRole::Alice;
    let bob = TestRole::Bob;

    // RoleId is automatically implemented for types with the required bounds
    assert_ne!(alice, bob);
}

#[wasm_bindgen_test]
fn test_message_types() {
    let hello = TestMessage::Hello("world".to_string());
    let goodbye = TestMessage::Goodbye;
    let num = TestMessage::Number(42);

    match hello {
        TestMessage::Hello(s) => assert_eq!(s, "world"),
        _ => panic!("Wrong variant"),
    }

    match goodbye {
        TestMessage::Goodbye => {}
        _ => panic!("Wrong variant"),
    }

    match num {
        TestMessage::Number(n) => assert_eq!(n, 42),
        _ => panic!("Wrong variant"),
    }
}

#[wasm_bindgen_test]
fn test_handler_creation() {
    let channels = Arc::new(Mutex::new(HashMap::new()));
    let choice_channels = Arc::new(Mutex::new(HashMap::new()));

    let handler = InMemoryHandler::with_channels(TestRole::Alice, channels, choice_channels);

    // Handler should be created successfully
    drop(handler);
}

#[wasm_bindgen_test]
fn test_program_builder() {
    // Test that programs can be constructed
    let program = Program::new()
        .send(TestRole::Bob, TestMessage::Hello("test".to_string()))
        .recv::<TestMessage>(TestRole::Bob)
        .end();

    // Verify program structure
    assert_eq!(program.effects.len(), 2); // send + recv
    assert_eq!(program.send_count(), 1);
    assert_eq!(program.recv_count(), 1);
}

#[wasm_bindgen_test]
fn test_program_with_choice() {
    let program = Program::new()
        .choose(TestRole::Bob, Label("branch1"))
        .offer(TestRole::Alice)
        .end();

    assert_eq!(program.effects.len(), 2);
}

#[wasm_bindgen_test]
fn test_program_with_timeout() {
    let inner_program = Program::new()
        .send(TestRole::Bob, TestMessage::Number(1))
        .end();

    let program = Program::new()
        .with_timeout(TestRole::Alice, Duration::from_millis(100), inner_program)
        .end();

    assert!(program.has_timeouts());
}

#[wasm_bindgen_test]
fn test_program_parallel() {
    let p1 = Program::new()
        .send(TestRole::Bob, TestMessage::Number(1))
        .end();

    let p2 = Program::new()
        .send(TestRole::Bob, TestMessage::Number(2))
        .end();

    let program = Program::new().parallel(vec![p1, p2]).end();

    assert!(program.has_parallel());
}

#[wasm_bindgen_test]
async fn test_simple_send_recv() {
    // Create shared channels for Alice and Bob
    let channels = Arc::new(Mutex::new(HashMap::new()));
    let choice_channels = Arc::new(Mutex::new(HashMap::new()));

    // Alice's handler
    let mut alice_handler =
        InMemoryHandler::with_channels(TestRole::Alice, channels.clone(), choice_channels.clone());

    // Alice sends to Bob
    let alice_program = Program::new()
        .send(TestRole::Bob, TestMessage::Hello("from Alice".to_string()))
        .end();

    let mut endpoint = ();
    let result = interpret(&mut alice_handler, &mut endpoint, alice_program).await;

    assert!(result.is_ok());
    let result = result.unwrap();
    assert_eq!(result.final_state, InterpreterState::Completed);
}

#[wasm_bindgen_test]
async fn test_message_serialization() {
    let msg = TestMessage::Hello("test".to_string());
    let serialized = bincode::serialize(&msg).unwrap();
    let deserialized: TestMessage = bincode::deserialize(&serialized).unwrap();

    assert_eq!(msg, deserialized);
}

#[wasm_bindgen_test]
async fn test_label_operations() {
    let label1 = Label("option1");
    let label2 = Label("option2");

    assert_eq!(label1.0, "option1");
    assert_eq!(label2.0, "option2");
    assert_ne!(label1, label2);

    // Test cloning
    let label_clone = label1.clone();
    assert_eq!(label1, label_clone);
}

#[wasm_bindgen_test]
async fn test_effect_types() {
    // Verify all effect variants can be created
    let _send = Effect::Send {
        to: TestRole::Bob,
        msg: TestMessage::Number(42),
    };

    let _recv = Effect::<TestRole, TestMessage>::Recv {
        from: TestRole::Alice,
    };

    let _choose = Effect::<TestRole, TestMessage>::Choose {
        who: TestRole::Alice,
        label: Label("test"),
    };

    let _offer = Effect::<TestRole, TestMessage>::Offer {
        from: TestRole::Bob,
    };

    let _timeout = Effect::WithTimeout {
        at: TestRole::Alice,
        dur: Duration::from_millis(100),
        body: Box::new(Program::new().end()),
    };

    let _parallel = Effect::<TestRole, TestMessage>::Parallel {
        programs: vec![Program::new().end()],
    };

    let _end = Effect::<TestRole, TestMessage>::End;
}

#[wasm_bindgen_test]
async fn test_program_analysis() {
    let program = Program::new()
        .send(TestRole::Bob, TestMessage::Number(1))
        .send(TestRole::Bob, TestMessage::Number(2))
        .recv::<TestMessage>(TestRole::Bob)
        .choose(TestRole::Alice, Label("opt1"))
        .with_timeout(
            TestRole::Alice,
            Duration::from_millis(50),
            Program::new().end(),
        )
        .parallel(vec![Program::new().end()])
        .end();

    // Verify program analysis methods work
    assert_eq!(program.send_count(), 2);
    assert_eq!(program.recv_count(), 1);
    assert_eq!(program.effects.len(), 6);
    assert!(program.has_timeouts());
    assert!(program.has_parallel());
}

#[wasm_bindgen_test]
fn test_handler_with_new() {
    // Test the simpler constructor
    let handler = InMemoryHandler::new(TestRole::Alice);

    // Should be created successfully
    drop(handler);
}

#[wasm_bindgen_test]
async fn test_empty_program() {
    let mut handler = InMemoryHandler::new(TestRole::Alice);
    let program = Program::new().end();

    let mut endpoint = ();
    let result = interpret(&mut handler, &mut endpoint, program).await;

    assert!(result.is_ok());
    let result = result.unwrap();
    assert_eq!(result.final_state, InterpreterState::Completed);
    assert_eq!(result.received_values.len(), 0);
}

#[wasm_bindgen_test]
async fn test_futures_channel_compatibility() {
    use futures::channel::mpsc::{unbounded, UnboundedReceiver, UnboundedSender};
    use futures::StreamExt;

    let (mut tx, mut rx): (UnboundedSender<i32>, UnboundedReceiver<i32>) = unbounded();

    // Test send
    tx.unbounded_send(42).unwrap();

    // Test receive
    let value = rx.next().await;
    assert_eq!(value, Some(42));
}
