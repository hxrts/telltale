//! Integration tests for runner function code generation.
//!
//! These tests verify that the `run_{role}` functions and `execute_as` dispatch
//! are generated correctly from choreographic specifications.

use quote::format_ident;
use rumpsteak_aura_choreography::ast::{LocalType, MessageType, Role};
use rumpsteak_aura_choreography::compiler::runner::{
    generate_all_runners, generate_execute_as, generate_output_types, generate_runner_fn,
};

/// Helper to create a simple role
fn make_role(name: &str) -> Role {
    Role::new(format_ident!("{}", name))
}

/// Helper to create a message type
fn make_message(name: &str) -> MessageType {
    MessageType {
        name: format_ident!("{}", name),
        type_annotation: None,
        payload: None,
    }
}

#[test]
fn test_generate_output_types() {
    let roles = vec![make_role("Client"), make_role("Server")];
    let tokens = generate_output_types(&roles);
    let output = tokens.to_string();

    // Should generate output structs for each role
    assert!(
        output.contains("ClientOutput"),
        "Should contain ClientOutput"
    );
    assert!(
        output.contains("ServerOutput"),
        "Should contain ServerOutput"
    );
    // Check for derives (formatting may vary)
    assert!(output.contains("derive"), "Should have derive attribute");
    assert!(output.contains("Debug"), "Should derive Debug");
    assert!(output.contains("Default"), "Should derive Default");
}

#[test]
fn test_generate_runner_fn_simple_end() {
    let role = make_role("Client");
    let local_type = LocalType::End;

    let tokens = generate_runner_fn("TestProtocol", &role, &local_type);
    let output = tokens.to_string();

    // Should generate async function with correct name
    assert!(
        output.contains("run_client"),
        "Should contain run_client function"
    );
    assert!(output.contains("async fn"), "Should be async function");
    assert!(
        output.contains("ChoreographicAdapter"),
        "Should use ChoreographicAdapter trait"
    );
    assert!(
        output.contains("ClientOutput"),
        "Should return ClientOutput"
    );
}

#[test]
fn test_generate_runner_fn_send_recv() {
    let role = make_role("Client");
    let server = make_role("Server");
    let request_msg = make_message("Request");
    let response_msg = make_message("Response");

    // Client sends Request, then receives Response
    let local_type = LocalType::Send {
        to: server.clone(),
        message: request_msg,
        continuation: Box::new(LocalType::Receive {
            from: server,
            message: response_msg,
            continuation: Box::new(LocalType::End),
        }),
    };

    let tokens = generate_runner_fn("TestProtocol", &role, &local_type);
    let output = tokens.to_string();

    // Should generate send and recv calls (spacing may vary in token stream)
    assert!(
        output.contains("adapter . send") || output.contains("adapter.send"),
        "Should contain send call: {}",
        output
    );
    assert!(
        output.contains("adapter . recv") || output.contains("adapter.recv"),
        "Should contain recv call: {}",
        output
    );
}

#[test]
fn test_generate_runner_fn_branch() {
    let role = make_role("Server");
    let client = make_role("Client");

    // Server branches on choice from Client
    let local_type = LocalType::Branch {
        from: client,
        branches: vec![
            (format_ident!("Accept"), LocalType::End),
            (format_ident!("Reject"), LocalType::End),
        ],
    };

    let tokens = generate_runner_fn("TestProtocol", &role, &local_type);
    let output = tokens.to_string();

    // Should generate offer and match (spacing may vary)
    assert!(
        output.contains("adapter . offer") || output.contains("adapter.offer"),
        "Should contain offer call: {}",
        output
    );
    assert!(
        output.contains("match label"),
        "Should contain match on label: {}",
        output
    );
    assert!(
        output.contains("Accept"),
        "Should match on Accept label: {}",
        output
    );
    assert!(
        output.contains("Reject"),
        "Should match on Reject label: {}",
        output
    );
}

#[test]
fn test_generate_execute_as() {
    let roles = vec![make_role("Client"), make_role("Server")];
    let local_types: Vec<(Role, LocalType)> =
        roles.iter().map(|r| (r.clone(), LocalType::End)).collect();

    let tokens = generate_execute_as("TestProtocol", &roles, &local_types);
    let output = tokens.to_string();

    // Should generate role enum
    assert!(
        output.contains("TestProtocolRole"),
        "Should contain role enum: {}",
        output
    );
    assert!(
        output.contains("Client"),
        "Should contain Client variant: {}",
        output
    );
    assert!(
        output.contains("Server"),
        "Should contain Server variant: {}",
        output
    );

    // Should generate execute_as function
    assert!(
        output.contains("execute_as"),
        "Should contain execute_as function: {}",
        output
    );
    assert!(
        output.contains("run_client"),
        "Should dispatch to run_client: {}",
        output
    );
    assert!(
        output.contains("run_server"),
        "Should dispatch to run_server: {}",
        output
    );
}

#[test]
fn test_generate_all_runners() {
    let roles = vec![make_role("Buyer"), make_role("Seller")];
    let local_types: Vec<(Role, LocalType)> =
        roles.iter().map(|r| (r.clone(), LocalType::End)).collect();

    let tokens = generate_all_runners("TwoBuyer", &roles, &local_types);
    let output = tokens.to_string();

    // Should generate runners module
    assert!(
        output.contains("mod runners"),
        "Should contain runners module: {}",
        output
    );

    // Should contain all expected functions
    assert!(
        output.contains("run_buyer"),
        "Should contain run_buyer: {}",
        output
    );
    assert!(
        output.contains("run_seller"),
        "Should contain run_seller: {}",
        output
    );
    assert!(
        output.contains("execute_as"),
        "Should contain execute_as: {}",
        output
    );
    assert!(
        output.contains("BuyerOutput"),
        "Should contain BuyerOutput: {}",
        output
    );
    assert!(
        output.contains("SellerOutput"),
        "Should contain SellerOutput: {}",
        output
    );
}

#[test]
fn test_generate_runner_fn_recursive() {
    let role = make_role("Worker");
    let manager = make_role("Manager");
    let task_msg = make_message("Task");
    let result_msg = make_message("TaskResult");

    // Worker receives tasks in a loop: rec X. Recv Task. Send Result. X
    let local_type = LocalType::Rec {
        label: format_ident!("Loop"),
        body: Box::new(LocalType::Receive {
            from: manager.clone(),
            message: task_msg,
            continuation: Box::new(LocalType::Send {
                to: manager,
                message: result_msg,
                continuation: Box::new(LocalType::Var(format_ident!("Loop"))),
            }),
        }),
    };

    let tokens = generate_runner_fn("WorkerProtocol", &role, &local_type);
    let output = tokens.to_string();

    // Should generate loop with label
    assert!(
        output.contains("'rec_Loop"),
        "Should contain rec loop label: {}",
        output
    );
    assert!(
        output.contains("continue 'rec_Loop"),
        "Should contain continue statement: {}",
        output
    );
}

#[test]
fn test_generate_runner_fn_select() {
    let role = make_role("Client");
    let server = make_role("Server");

    // Client selects between two choices to send to Server
    let local_type = LocalType::Select {
        to: server,
        branches: vec![
            (format_ident!("Query"), LocalType::End),
            (format_ident!("Update"), LocalType::End),
        ],
    };

    let tokens = generate_runner_fn("TestProtocol", &role, &local_type);
    let output = tokens.to_string();

    // Should generate choose and match (spacing may vary)
    assert!(
        output.contains("adapter . choose") || output.contains("adapter.choose"),
        "Should contain choose call: {}",
        output
    );
    assert!(
        output.contains("enum Choice"),
        "Should contain Choice enum: {}",
        output
    );
    assert!(
        output.contains("Query"),
        "Should contain Query variant: {}",
        output
    );
    assert!(
        output.contains("Update"),
        "Should contain Update variant: {}",
        output
    );
}
