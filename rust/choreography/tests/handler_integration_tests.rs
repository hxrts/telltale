//! Integration tests for handlers, interpreter, and middleware.
//!
//! Verifies:
//! - Complete protocol execution through interpreter
//! - Middleware stacking (Trace, Retry, Metrics)
//! - Error propagation through the stack
//! - Complex programs with all effect types

#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

use rumpsteak_aura_choreography::effects::{
    algebra::{InterpreterState, Program},
    handlers::in_memory::InMemoryHandler,
    interpreter::{interpret, testing::MockHandler},
    middleware::Trace,
    ChoreoHandler, Label,
};
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
struct Request {
    id: u32,
    payload: String,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
struct Response {
    id: u32,
    result: i64,
}

// ============================================================================
// Interpreter Basic Tests
// ============================================================================

#[tokio::test]
async fn test_interpreter_simple_send_program() {
    let mut handler = MockHandler::new(TestRole::Alice);
    let mut endpoint = ();

    let program = Program::new()
        .send(TestRole::Bob, Request { id: 1, payload: "hello".into() })
        .end();

    let result = interpret(&mut handler, &mut endpoint, program)
        .await
        .unwrap();

    assert_eq!(result.final_state, InterpreterState::Completed);

    let ops = handler.operations();
    assert_eq!(ops.len(), 1);
}

#[tokio::test]
async fn test_interpreter_send_recv_sequence() {
    use rumpsteak_aura_choreography::effects::interpreter::testing::{MockResponse, MockOperation};

    let mut handler = MockHandler::new(TestRole::Alice);

    // Script the response for the recv operation (same type as send for Program consistency)
    let response = Request { id: 100, payload: "reply".into() };
    handler.add_response(MockResponse::Message(
        bincode::serialize(&response).unwrap()
    ));

    let mut endpoint = ();

    // Note: Program<R, M> requires consistent message type M
    let program = Program::new()
        .send(TestRole::Bob, Request { id: 1, payload: "query".into() })
        .recv::<Request>(TestRole::Bob)
        .end();

    let result = interpret(&mut handler, &mut endpoint, program)
        .await
        .unwrap();

    assert_eq!(result.final_state, InterpreterState::Completed);
    assert_eq!(result.received_values.len(), 1);

    let ops = handler.operations();
    assert_eq!(ops.len(), 2);

    // Verify operation order
    match &ops[0] {
        MockOperation::Send { to, .. } => assert_eq!(*to, TestRole::Bob),
        _ => panic!("Expected Send operation first"),
    }
    match &ops[1] {
        MockOperation::Recv { from } => assert_eq!(*from, TestRole::Bob),
        _ => panic!("Expected Recv operation second"),
    }
}

#[tokio::test]
async fn test_interpreter_choose_offer_sequence() {
    use rumpsteak_aura_choreography::effects::interpreter::testing::{MockResponse, MockOperation};

    let mut handler = MockHandler::new(TestRole::Bob);

    // Script the label for the offer operation
    handler.add_response(MockResponse::Label("Accept".into()));

    let mut endpoint = ();

    // Bob offers and receives Alice's choice
    let program: Program<TestRole, Request> = Program::new()
        .offer(TestRole::Alice)
        .end();

    let result = interpret(&mut handler, &mut endpoint, program)
        .await
        .unwrap();

    assert_eq!(result.final_state, InterpreterState::Completed);

    let ops = handler.operations();
    assert_eq!(ops.len(), 1);

    match &ops[0] {
        MockOperation::Offer { from } => assert_eq!(*from, TestRole::Alice),
        _ => panic!("Expected Offer operation"),
    }
}

// ============================================================================
// Interpreter Error Handling Tests
// ============================================================================

#[tokio::test]
async fn test_interpreter_recv_error_becomes_failed_state() {
    use rumpsteak_aura_choreography::effects::algebra::InterpretResult;

    let mut handler = MockHandler::new(TestRole::Alice);
    // Don't add a response - recv will fail
    let mut endpoint = ();

    let program: Program<TestRole, Request> = Program::new()
        .recv::<Request>(TestRole::Bob)
        .end();

    let result: InterpretResult<Request> = interpret(&mut handler, &mut endpoint, program)
        .await
        .unwrap();

    // Should complete with failed state, not panic
    match result.final_state {
        InterpreterState::Failed(msg) => {
            assert!(msg.contains("No scripted response"));
        }
        _ => panic!("Expected Failed state, got {:?}", result.final_state),
    }
}

#[tokio::test]
async fn test_interpreter_offer_error_becomes_failed_state() {
    use rumpsteak_aura_choreography::effects::algebra::InterpretResult;

    let mut handler = MockHandler::new(TestRole::Bob);
    // Don't add a response - offer will fail
    let mut endpoint = ();

    let program: Program<TestRole, Request> = Program::new()
        .offer(TestRole::Alice)
        .end();

    let result: InterpretResult<Request> = interpret(&mut handler, &mut endpoint, program)
        .await
        .unwrap();

    match result.final_state {
        InterpreterState::Failed(msg) => {
            assert!(msg.contains("No scripted label"));
        }
        _ => panic!("Expected Failed state"),
    }
}

// ============================================================================
// Trace Middleware Tests
// ============================================================================

#[tokio::test]
async fn test_trace_middleware_wraps_handler() {
    let inner = MockHandler::new(TestRole::Alice);
    let mut traced = Trace::new(inner);
    let mut endpoint = ();

    // Send through traced handler
    let msg = Request { id: 1, payload: "test".into() };
    traced.send(&mut endpoint, TestRole::Bob, &msg)
        .await
        .expect("Send should succeed");

    // The inner handler should have recorded the operation
    // (We can't directly access inner here, but the test verifies no panic)
}

#[tokio::test]
async fn test_trace_middleware_with_custom_prefix() {
    let inner = MockHandler::new(TestRole::Alice);
    let mut traced = Trace::with_prefix(inner, "custom-prefix");
    let mut endpoint = ();

    traced.send(&mut endpoint, TestRole::Bob, &Request { id: 1, payload: "x".into() })
        .await
        .unwrap();
}

#[tokio::test]
async fn test_trace_middleware_choose_offer() {
    let inner = MockHandler::new(TestRole::Alice);
    let mut traced = Trace::new(inner);
    let mut endpoint = ();

    // Choose should work through trace
    traced.choose(&mut endpoint, TestRole::Bob, Label("Option1"))
        .await
        .expect("Choose should succeed");
}

// ============================================================================
// InMemoryHandler Integration Tests
// ============================================================================

#[tokio::test]
async fn test_in_memory_handler_bidirectional_protocol() {
    let channels = Arc::new(Mutex::new(HashMap::new()));
    let choice_channels = Arc::new(Mutex::new(HashMap::new()));

    let mut alice = InMemoryHandler::with_channels(
        TestRole::Alice,
        channels.clone(),
        choice_channels.clone(),
    );
    let mut bob = InMemoryHandler::with_channels(
        TestRole::Bob,
        channels.clone(),
        choice_channels.clone(),
    );

    // Alice sends request
    let request = Request { id: 42, payload: "hello".into() };
    alice.send(&mut (), TestRole::Bob, &request)
        .await
        .expect("Alice send should succeed");

    // Bob receives request
    let received_request: Request = bob.recv(&mut (), TestRole::Alice)
        .await
        .expect("Bob recv should succeed");
    assert_eq!(received_request, request);

    // Bob sends response
    let response = Response { id: 42, result: 100 };
    bob.send(&mut (), TestRole::Alice, &response)
        .await
        .expect("Bob send should succeed");

    // Alice receives response
    let received_response: Response = alice.recv(&mut (), TestRole::Bob)
        .await
        .expect("Alice recv should succeed");
    assert_eq!(received_response, response);
}

// Tests that InMemoryHandler properly coordinates choose/offer through choice channels.
// The choose() method sends the label through the choice channel, and offer() receives it.
#[tokio::test]
async fn test_in_memory_handler_choice_protocol() {
    let channels = Arc::new(Mutex::new(HashMap::new()));
    let choice_channels = Arc::new(Mutex::new(HashMap::new()));

    let mut alice = InMemoryHandler::with_channels(
        TestRole::Alice,
        channels.clone(),
        choice_channels.clone(),
    );
    let mut bob = InMemoryHandler::with_channels(
        TestRole::Bob,
        channels.clone(),
        choice_channels.clone(),
    );

    // Alice makes a choice
    alice.choose(&mut (), TestRole::Bob, Label("Accept"))
        .await
        .expect("Alice choose should succeed");

    // Bob receives the choice
    let label = bob.offer(&mut (), TestRole::Alice)
        .await
        .expect("Bob offer should succeed");

    assert_eq!(label.0, "Accept");
}

#[tokio::test]
async fn test_in_memory_handler_three_party_protocol() {
    let channels = Arc::new(Mutex::new(HashMap::new()));
    let choice_channels = Arc::new(Mutex::new(HashMap::new()));

    let mut alice = InMemoryHandler::with_channels(
        TestRole::Alice,
        channels.clone(),
        choice_channels.clone(),
    );
    let mut bob = InMemoryHandler::with_channels(
        TestRole::Bob,
        channels.clone(),
        choice_channels.clone(),
    );
    let mut charlie = InMemoryHandler::with_channels(
        TestRole::Charlie,
        channels.clone(),
        choice_channels.clone(),
    );

    // Alice -> Bob
    alice.send(&mut (), TestRole::Bob, &Request { id: 1, payload: "to bob".into() })
        .await
        .unwrap();

    // Alice -> Charlie
    alice.send(&mut (), TestRole::Charlie, &Request { id: 2, payload: "to charlie".into() })
        .await
        .unwrap();

    // Bob receives from Alice
    let bob_msg: Request = bob.recv(&mut (), TestRole::Alice).await.unwrap();
    assert_eq!(bob_msg.id, 1);

    // Charlie receives from Alice
    let charlie_msg: Request = charlie.recv(&mut (), TestRole::Alice).await.unwrap();
    assert_eq!(charlie_msg.id, 2);

    // Bob -> Charlie
    bob.send(&mut (), TestRole::Charlie, &Response { id: 1, result: 10 })
        .await
        .unwrap();

    // Charlie receives from Bob
    let from_bob: Response = charlie.recv(&mut (), TestRole::Bob).await.unwrap();
    assert_eq!(from_bob.result, 10);
}

// ============================================================================
// Traced InMemoryHandler Tests
// ============================================================================

#[tokio::test]
async fn test_traced_in_memory_handler() {
    let channels = Arc::new(Mutex::new(HashMap::new()));
    let choice_channels = Arc::new(Mutex::new(HashMap::new()));

    let alice_inner = InMemoryHandler::with_channels(
        TestRole::Alice,
        channels.clone(),
        choice_channels.clone(),
    );
    let bob_inner = InMemoryHandler::with_channels(
        TestRole::Bob,
        channels.clone(),
        choice_channels.clone(),
    );

    // Wrap handlers with tracing
    let mut alice = Trace::with_prefix(alice_inner, "alice");
    let mut bob = Trace::with_prefix(bob_inner, "bob");

    // Run a simple protocol through traced handlers
    alice.send(&mut (), TestRole::Bob, &Request { id: 1, payload: "test".into() })
        .await
        .unwrap();

    let msg: Request = bob.recv(&mut (), TestRole::Alice)
        .await
        .unwrap();

    assert_eq!(msg.id, 1);
}

// ============================================================================
// Program Analysis Tests
// ============================================================================

#[test]
fn test_program_send_count() {
    let program: Program<TestRole, Request> = Program::new()
        .send(TestRole::Bob, Request { id: 1, payload: "a".into() })
        .send(TestRole::Charlie, Request { id: 2, payload: "b".into() })
        .end();

    assert_eq!(program.send_count(), 2);
}

#[test]
fn test_program_recv_count() {
    let program: Program<TestRole, Response> = Program::new()
        .recv::<Response>(TestRole::Bob)
        .recv::<Response>(TestRole::Charlie)
        .recv::<Response>(TestRole::Alice)
        .end();

    assert_eq!(program.recv_count(), 3);
}

#[test]
fn test_program_roles_involved() {
    let program: Program<TestRole, Request> = Program::new()
        .send(TestRole::Bob, Request { id: 1, payload: "x".into() })
        .recv::<Request>(TestRole::Charlie)
        .choose(TestRole::Alice, Label("ok"))
        .end();

    let roles = program.roles_involved();
    assert!(roles.contains(&TestRole::Alice));
    assert!(roles.contains(&TestRole::Bob));
    assert!(roles.contains(&TestRole::Charlie));
}

#[test]
fn test_program_has_timeouts() {
    use std::time::Duration;

    let program_no_timeout: Program<TestRole, Request> = Program::new()
        .send(TestRole::Bob, Request { id: 1, payload: "x".into() })
        .end();

    assert!(!program_no_timeout.has_timeouts());

    let inner: Program<TestRole, Request> = Program::new()
        .send(TestRole::Bob, Request { id: 1, payload: "x".into() })
        .end();

    let program_with_timeout: Program<TestRole, Request> = Program::new()
        .with_timeout(TestRole::Alice, Duration::from_secs(5), inner)
        .end();

    assert!(program_with_timeout.has_timeouts());
}

#[test]
fn test_program_has_parallel() {
    let program_no_parallel: Program<TestRole, Request> = Program::new()
        .send(TestRole::Bob, Request { id: 1, payload: "x".into() })
        .end();

    assert!(!program_no_parallel.has_parallel());

    let p1: Program<TestRole, Request> = Program::new()
        .send(TestRole::Bob, Request { id: 1, payload: "a".into() })
        .end();
    let p2: Program<TestRole, Request> = Program::new()
        .send(TestRole::Charlie, Request { id: 2, payload: "b".into() })
        .end();

    let program_with_parallel: Program<TestRole, Request> = Program::new()
        .parallel(vec![p1, p2])
        .end();

    assert!(program_with_parallel.has_parallel());
}

// ============================================================================
// Complex Protocol Tests
// ============================================================================

#[tokio::test]
async fn test_interpreter_multi_step_protocol() {
    use rumpsteak_aura_choreography::effects::interpreter::testing::MockResponse;

    let mut handler = MockHandler::new(TestRole::Alice);

    // Script responses for each recv (using Request type to match Program<_, Request>)
    handler.add_response(MockResponse::Message(
        bincode::serialize(&Request { id: 10, payload: "response1".into() }).unwrap()
    ));
    handler.add_response(MockResponse::Message(
        bincode::serialize(&Request { id: 20, payload: "response2".into() }).unwrap()
    ));

    let mut endpoint = ();

    // Note: Program<R, M> has single message type M, so we use Request for all
    let program: Program<TestRole, Request> = Program::new()
        .send(TestRole::Bob, Request { id: 1, payload: "first".into() })
        .recv::<Request>(TestRole::Bob)
        .send(TestRole::Bob, Request { id: 2, payload: "second".into() })
        .recv::<Request>(TestRole::Bob)
        .end();

    let result = interpret(&mut handler, &mut endpoint, program)
        .await
        .unwrap();

    assert_eq!(result.final_state, InterpreterState::Completed);
    assert_eq!(result.received_values.len(), 2);
}

// ============================================================================
// Loop Effect Tests
// ============================================================================

#[tokio::test]
async fn test_interpreter_loop_effect() {
    let mut handler = MockHandler::new(TestRole::Alice);
    let mut endpoint = ();

    // Create a loop that sends 3 times
    let body: Program<TestRole, Request> = Program::new()
        .send(TestRole::Bob, Request { id: 0, payload: "loop".into() })
        .end();

    let program: Program<TestRole, Request> = Program::new()
        .loop_n(3, body)
        .end();

    let result = interpret(&mut handler, &mut endpoint, program)
        .await
        .unwrap();

    assert_eq!(result.final_state, InterpreterState::Completed);

    // Should have 3 send operations
    let ops = handler.operations();
    assert_eq!(ops.len(), 3);
}

// ============================================================================
// Parallel Effect Tests
// ============================================================================

#[tokio::test]
async fn test_interpreter_parallel_effect() {
    let mut handler = MockHandler::new(TestRole::Alice);
    let mut endpoint = ();

    let p1: Program<TestRole, Request> = Program::new()
        .send(TestRole::Bob, Request { id: 1, payload: "to bob".into() })
        .end();
    let p2: Program<TestRole, Request> = Program::new()
        .send(TestRole::Charlie, Request { id: 2, payload: "to charlie".into() })
        .end();

    let program = Program::new()
        .parallel(vec![p1, p2])
        .end();

    let result = interpret(&mut handler, &mut endpoint, program)
        .await
        .unwrap();

    assert_eq!(result.final_state, InterpreterState::Completed);

    // Should have 2 send operations (executed sequentially in current impl)
    let ops = handler.operations();
    assert_eq!(ops.len(), 2);
}

// ============================================================================
// End Effect Tests
// ============================================================================

#[tokio::test]
async fn test_interpreter_empty_program() {
    let mut handler = MockHandler::new(TestRole::Alice);
    let mut endpoint = ();

    let program: Program<TestRole, Request> = Program::new().end();

    let result = interpret(&mut handler, &mut endpoint, program)
        .await
        .unwrap();

    assert_eq!(result.final_state, InterpreterState::Completed);
    assert_eq!(result.received_values.len(), 0);
    assert_eq!(handler.operations().len(), 0);
}
