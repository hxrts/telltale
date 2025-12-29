#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]
// WASM integration test - Full protocol execution
//
// This test demonstrates a complete two-party protocol executing in WASM,
// including message exchange, timeouts, and error handling.
#![cfg(target_arch = "wasm32")]

use rumpsteak_aura_choreography::{
    interpret, InMemoryHandler, InterpretResult, InterpreterState, Label, Program, RoleId,
};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::Duration;
use wasm_bindgen_test::*;

wasm_bindgen_test_configure!(run_in_browser);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
enum Role {
    Client,
    Server,
}

impl RoleId for Role {
    fn name(&self) -> String {
        match self {
            Role::Client => "Client".to_string(),
            Role::Server => "Server".to_string(),
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
enum Message {
    Request { id: u32, data: String },
    Response { id: u32, result: String },
    Error { code: u32, message: String },
}

/// Test a complete request-response protocol
#[wasm_bindgen_test]
async fn test_full_request_response_protocol() {
    // Setup shared channels
    let channels = Arc::new(Mutex::new(HashMap::new()));
    let choice_channels = Arc::new(Mutex::new(HashMap::new()));

    // Client side
    let mut client_handler =
        InMemoryHandler::with_channels(Role::Client, channels.clone(), choice_channels.clone());

    let client_program = Program::new()
        .send(
            Role::Server,
            Message::Request {
                id: 1,
                data: "Hello Server".to_string(),
            },
        )
        .recv::<Message>(Role::Server)
        .end();

    // Execute client side
    let mut client_endpoint = ();
    let client_result = interpret(&mut client_handler, &mut client_endpoint, client_program).await;

    assert!(client_result.is_ok());
    let result = client_result.unwrap();
    assert_eq!(result.final_state, InterpreterState::Completed);

    // Server side
    let mut server_handler =
        InMemoryHandler::with_channels(Role::Server, channels.clone(), choice_channels.clone());

    let server_program = Program::new()
        .recv::<Message>(Role::Client)
        .send(
            Role::Client,
            Message::Response {
                id: 1,
                result: "Hello Client".to_string(),
            },
        )
        .end();

    // Execute server side
    let mut server_endpoint = ();
    let server_result = interpret(&mut server_handler, &mut server_endpoint, server_program).await;

    assert!(server_result.is_ok());
    let result = server_result.unwrap();
    assert_eq!(result.final_state, InterpreterState::Completed);

    // Verify messages were received
    assert_eq!(result.received_values.len(), 1);
    match &result.received_values[0] {
        Message::Request { id, data } => {
            assert_eq!(*id, 1);
            assert_eq!(data, "Hello Server");
        }
        _ => panic!("Expected Request message"),
    }
}

/// Test protocol with multiple message exchanges
#[wasm_bindgen_test]
async fn test_multi_message_protocol() {
    let channels = Arc::new(Mutex::new(HashMap::new()));
    let choice_channels = Arc::new(Mutex::new(HashMap::new()));

    // Client sends multiple requests
    let mut client =
        InMemoryHandler::with_channels(Role::Client, channels.clone(), choice_channels.clone());

    let client_program = Program::new()
        .send(
            Role::Server,
            Message::Request {
                id: 1,
                data: "req1".to_string(),
            },
        )
        .recv::<Message>(Role::Server)
        .send(
            Role::Server,
            Message::Request {
                id: 2,
                data: "req2".to_string(),
            },
        )
        .recv::<Message>(Role::Server)
        .end();

    let mut endpoint = ();
    let client_result = interpret(&mut client, &mut endpoint, client_program).await;

    assert!(client_result.is_ok());
    let result = client_result.unwrap();
    assert_eq!(result.final_state, InterpreterState::Completed);
    assert_eq!(result.received_values.len(), 2);
}

/// Test protocol with choice/offer
#[wasm_bindgen_test]
async fn test_protocol_with_branching() {
    let channels = Arc::new(Mutex::new(HashMap::new()));
    let choice_channels = Arc::new(Mutex::new(HashMap::new()));

    let mut sender =
        InMemoryHandler::with_channels(Role::Client, channels.clone(), choice_channels.clone());

    let program = Program::new()
        .choose(Role::Server, Label("success"))
        .send(
            Role::Server,
            Message::Response {
                id: 1,
                result: "OK".to_string(),
            },
        )
        .end();

    let mut endpoint = ();
    let result = interpret(&mut sender, &mut endpoint, program).await;

    assert!(result.is_ok());
}

/// Test protocol timeout behavior
#[wasm_bindgen_test]
async fn test_protocol_with_timeout() {
    let mut handler = InMemoryHandler::new(Role::Client);

    let inner = Program::new()
        .send(
            Role::Server,
            Message::Request {
                id: 1,
                data: "test".to_string(),
            },
        )
        .end();

    let program = Program::new()
        .with_timeout(Role::Client, Duration::from_millis(100), inner)
        .end();

    let mut endpoint = ();
    let result = interpret(&mut handler, &mut endpoint, program).await;

    // Should complete (not timeout) since send is immediate
    assert!(result.is_ok());
}

/// Test error message handling
#[wasm_bindgen_test]
async fn test_error_message_protocol() {
    let channels = Arc::new(Mutex::new(HashMap::new()));
    let choice_channels = Arc::new(Mutex::new(HashMap::new()));

    let mut sender =
        InMemoryHandler::with_channels(Role::Server, channels.clone(), choice_channels.clone());

    let program = Program::new()
        .send(
            Role::Client,
            Message::Error {
                code: 404,
                message: "Not Found".to_string(),
            },
        )
        .end();

    let mut endpoint = ();
    let result = interpret(&mut sender, &mut endpoint, program).await;

    assert!(result.is_ok());
    let result = result.unwrap();
    assert_eq!(result.final_state, InterpreterState::Completed);
}

/// Test complex message serialization
#[wasm_bindgen_test]
async fn test_complex_message_serialization() {
    let request = Message::Request {
        id: 12345,
        data: "Complex data with unicode: Rust 测试".to_string(),
    };

    let serialized = bincode::serialize(&request).unwrap();
    let deserialized: Message = bincode::deserialize(&serialized).unwrap();

    assert_eq!(request, deserialized);

    match deserialized {
        Message::Request { id, data } => {
            assert_eq!(id, 12345);
            // Unicode test data still present
            assert!(data.contains("测试"));
        }
        _ => panic!("Wrong message type"),
    }
}

/// Test program composition
#[wasm_bindgen_test]
fn test_program_composition() {
    // Build a program from smaller pieces
    let handshake = Program::new()
        .send(
            Role::Server,
            Message::Request {
                id: 0,
                data: "HELLO".to_string(),
            },
        )
        .recv::<Message>(Role::Server);

    let main_exchange = handshake
        .send(
            Role::Server,
            Message::Request {
                id: 1,
                data: "DATA".to_string(),
            },
        )
        .recv::<Message>(Role::Server);

    let complete = main_exchange.end();

    assert_eq!(complete.send_count(), 2);
    assert_eq!(complete.recv_count(), 2);
    assert_eq!(complete.effects.len(), 4);
}

/// Test parallel program execution structure
#[wasm_bindgen_test]
fn test_parallel_program_structure() {
    let p1 = Program::new()
        .send(
            Role::Server,
            Message::Request {
                id: 1,
                data: "A".to_string(),
            },
        )
        .end();

    let p2 = Program::new()
        .send(
            Role::Server,
            Message::Request {
                id: 2,
                data: "B".to_string(),
            },
        )
        .end();

    let parallel_program = Program::new().parallel(vec![p1, p2]).end();

    assert!(parallel_program.has_parallel());
    assert_eq!(parallel_program.effects.len(), 1); // The parallel effect itself
}

/// Test handler state independence
#[wasm_bindgen_test]
fn test_handler_independence() {
    let channels1 = Arc::new(Mutex::new(HashMap::new()));
    let choice1 = Arc::new(Mutex::new(HashMap::new()));

    let channels2 = Arc::new(Mutex::new(HashMap::new()));
    let choice2 = Arc::new(Mutex::new(HashMap::new()));

    let handler1 = InMemoryHandler::with_channels(Role::Client, channels1.clone(), choice1.clone());

    let handler2 = InMemoryHandler::with_channels(Role::Client, channels2.clone(), choice2.clone());

    // Handlers should be independent
    drop(handler1);
    drop(handler2);

    // Channels should also be independent
    assert!(!Arc::ptr_eq(&channels1, &channels2));
}

/// Test role name functionality
#[wasm_bindgen_test]
fn test_role_names() {
    assert_eq!(Role::Client.name(), "Client");
    assert_eq!(Role::Server.name(), "Server");
    assert_ne!(Role::Client.name(), Role::Server.name());
}

/// Test message variant construction
#[wasm_bindgen_test]
fn test_all_message_variants() {
    let request = Message::Request {
        id: 1,
        data: String::from("test"),
    };

    let response = Message::Response {
        id: 1,
        result: String::from("success"),
    };

    let error = Message::Error {
        code: 500,
        message: String::from("Internal Error"),
    };

    // All variants should be constructible
    assert!(matches!(request, Message::Request { .. }));
    assert!(matches!(response, Message::Response { .. }));
    assert!(matches!(error, Message::Error { .. }));
}
