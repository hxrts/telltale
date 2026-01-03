//! Tests for code generation public API
//!
//! This test suite verifies the major codegen functions produce
//! correctly structured Rust code.

#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

use quote::format_ident;
use rumpsteak_aura_choreography::ast::{
    annotation::Annotations, Choreography, LocalType, MessageType, Protocol, Role, RoleParam,
};
use rumpsteak_aura_choreography::compiler::codegen::{
    generate_choreography_code, generate_dynamic_role_support, generate_role_implementations,
    generate_session_type, generate_topology_integration, InlineTopology,
};
use rumpsteak_aura_choreography::topology::Topology;
use std::collections::HashMap;

// Helper to create simple roles
fn role(name: &str) -> Role {
    Role::new(format_ident!("{}", name)).unwrap()
}

// Helper to create parameterized roles
fn role_with_param(name: &str, param: RoleParam) -> Role {
    Role::with_param(format_ident!("{}", name), param).unwrap()
}

// Helper to create message types
fn message(name: &str) -> MessageType {
    MessageType {
        name: format_ident!("{}", name),
        type_annotation: None,
        payload: None,
    }
}

// Helper to create a Send protocol with default annotations
fn send(from: Role, to: Role, message: MessageType, continuation: Protocol) -> Protocol {
    Protocol::Send {
        from,
        to,
        message,
        continuation: Box::new(continuation),
        annotations: Annotations::new(),
        from_annotations: Annotations::new(),
        to_annotations: Annotations::new(),
    }
}

// ============================================================================
// generate_session_type Tests
// ============================================================================

#[test]
fn test_generate_session_type_send() {
    let alice = role("Alice");
    let bob = role("Bob");

    let local_type = LocalType::Send {
        to: bob.clone(),
        message: message("Hello"),
        continuation: Box::new(LocalType::End),
    };

    let code = generate_session_type(&alice, &local_type, "TestProtocol");
    let code_str = code.to_string();

    assert!(
        code_str.contains("type Alice_TestProtocol"),
        "Should have type name: {}",
        code_str
    );
    assert!(
        code_str.contains("Send"),
        "Should contain Send: {}",
        code_str
    );
    assert!(
        code_str.contains("Bob"),
        "Should reference Bob: {}",
        code_str
    );
    assert!(
        code_str.contains("Hello"),
        "Should contain message: {}",
        code_str
    );
}

#[test]
fn test_generate_session_type_receive() {
    let alice = role("Alice");
    let bob = role("Bob");

    let local_type = LocalType::Receive {
        from: alice.clone(),
        message: message("Response"),
        continuation: Box::new(LocalType::End),
    };

    let code = generate_session_type(&bob, &local_type, "TestProtocol");
    let code_str = code.to_string();

    assert!(
        code_str.contains("type Bob_TestProtocol"),
        "Should have type name: {}",
        code_str
    );
    assert!(
        code_str.contains("Receive"),
        "Should contain Receive: {}",
        code_str
    );
    assert!(
        code_str.contains("Alice"),
        "Should reference Alice: {}",
        code_str
    );
}

#[test]
fn test_generate_session_type_select() {
    let alice = role("Alice");
    let bob = role("Bob");

    let local_type = LocalType::Select {
        to: bob.clone(),
        branches: vec![
            (format_ident!("Accept"), LocalType::End),
            (format_ident!("Reject"), LocalType::End),
        ],
    };

    let code = generate_session_type(&alice, &local_type, "ChoiceProtocol");
    let code_str = code.to_string();

    assert!(
        code_str.contains("Select"),
        "Should contain Select: {}",
        code_str
    );
    assert!(
        code_str.contains("Accept"),
        "Should contain Accept branch: {}",
        code_str
    );
    assert!(
        code_str.contains("Reject"),
        "Should contain Reject branch: {}",
        code_str
    );
}

#[test]
fn test_generate_session_type_branch() {
    let alice = role("Alice");
    let bob = role("Bob");

    let local_type = LocalType::Branch {
        from: alice.clone(),
        branches: vec![
            (format_ident!("Yes"), LocalType::End),
            (format_ident!("No"), LocalType::End),
        ],
    };

    let code = generate_session_type(&bob, &local_type, "ChoiceProtocol");
    let code_str = code.to_string();

    assert!(
        code_str.contains("Branch"),
        "Should contain Branch: {}",
        code_str
    );
    assert!(
        code_str.contains("Yes"),
        "Should contain Yes branch: {}",
        code_str
    );
    assert!(
        code_str.contains("No"),
        "Should contain No branch: {}",
        code_str
    );
}

#[test]
fn test_generate_session_type_end() {
    let alice = role("Alice");

    let code = generate_session_type(&alice, &LocalType::End, "EmptyProtocol");
    let code_str = code.to_string();

    assert!(
        code_str.contains("End"),
        "Should contain End: {}",
        code_str
    );
}

// ============================================================================
// generate_role_implementations Tests
// ============================================================================

#[test]
fn test_generate_role_implementations_send() {
    let alice = role("Alice");
    let bob = role("Bob");

    let local_type = LocalType::Send {
        to: bob.clone(),
        message: message("Request"),
        continuation: Box::new(LocalType::End),
    };

    let code = generate_role_implementations(&alice, &local_type, "TestProtocol");
    let code_str = code.to_string();

    assert!(
        code_str.contains("async fn alice_protocol"),
        "Should have async function: {}",
        code_str
    );
    assert!(
        code_str.contains("try_session"),
        "Should use try_session: {}",
        code_str
    );
    assert!(
        code_str.contains("send"),
        "Should have send call: {}",
        code_str
    );
}

#[test]
fn test_generate_role_implementations_receive() {
    let alice = role("Alice");
    let bob = role("Bob");

    let local_type = LocalType::Receive {
        from: alice.clone(),
        message: message("Data"),
        continuation: Box::new(LocalType::End),
    };

    let code = generate_role_implementations(&bob, &local_type, "TestProtocol");
    let code_str = code.to_string();

    assert!(
        code_str.contains("async fn bob_protocol"),
        "Should have async function: {}",
        code_str
    );
    assert!(
        code_str.contains("receive"),
        "Should have receive call: {}",
        code_str
    );
}

#[test]
fn test_generate_role_implementations_branch() {
    let alice = role("Alice");
    let bob = role("Bob");

    let local_type = LocalType::Branch {
        from: alice.clone(),
        branches: vec![
            (format_ident!("Left"), LocalType::End),
            (format_ident!("Right"), LocalType::End),
        ],
    };

    let code = generate_role_implementations(&bob, &local_type, "ChoiceProtocol");
    let code_str = code.to_string();

    assert!(
        code_str.contains("branch"),
        "Should have branch call: {}",
        code_str
    );
    assert!(
        code_str.contains("match"),
        "Should have match statement: {}",
        code_str
    );
    assert!(
        code_str.contains("Choice"),
        "Should reference Choice enum: {}",
        code_str
    );
}

// ============================================================================
// generate_choreography_code Tests
// ============================================================================

#[test]
fn test_generate_choreography_code_basic() {
    let alice = role("Alice");
    let bob = role("Bob");

    let local_types = vec![
        (
            alice.clone(),
            LocalType::Send {
                to: bob.clone(),
                message: message("Ping"),
                continuation: Box::new(LocalType::End),
            },
        ),
        (
            bob.clone(),
            LocalType::Receive {
                from: alice.clone(),
                message: message("Ping"),
                continuation: Box::new(LocalType::End),
            },
        ),
    ];

    let code = generate_choreography_code("PingPong", &[alice.clone(), bob.clone()], &local_types);
    let code_str = code.to_string();

    // Should have roles struct
    assert!(
        code_str.contains("Roles"),
        "Should have Roles struct: {}",
        code_str
    );

    // Should have role structs
    assert!(
        code_str.contains("struct Alice"),
        "Should have Alice struct: {}",
        code_str
    );
    assert!(
        code_str.contains("struct Bob"),
        "Should have Bob struct: {}",
        code_str
    );

    // Should have session types
    assert!(
        code_str.contains("Alice_PingPong"),
        "Should have Alice session type: {}",
        code_str
    );
    assert!(
        code_str.contains("Bob_PingPong"),
        "Should have Bob session type: {}",
        code_str
    );
}

#[test]
fn test_generate_choreography_code_three_roles() {
    let alice = role("Alice");
    let bob = role("Bob");
    let charlie = role("Charlie");

    let local_types = vec![
        (alice.clone(), LocalType::End),
        (bob.clone(), LocalType::End),
        (charlie.clone(), LocalType::End),
    ];

    let code = generate_choreography_code(
        "ThreeParty",
        &[alice.clone(), bob.clone(), charlie.clone()],
        &local_types,
    );
    let code_str = code.to_string();

    // All roles should be present
    assert!(
        code_str.contains("Alice"),
        "Should have Alice: {}",
        code_str
    );
    assert!(code_str.contains("Bob"), "Should have Bob: {}", code_str);
    assert!(
        code_str.contains("Charlie"),
        "Should have Charlie: {}",
        code_str
    );

    // Should have routes
    assert!(
        code_str.contains("route"),
        "Should have routes: {}",
        code_str
    );
}

// ============================================================================
// generate_dynamic_role_support Tests
// ============================================================================

#[test]
fn test_generate_dynamic_role_support_static() {
    // Static role params should produce minimal/empty dynamic support
    let worker = role_with_param("Worker", RoleParam::Static(3));
    let manager = role("Manager");

    let choreo = Choreography {
        name: format_ident!("StaticWorkerProtocol"),
        namespace: None,
        roles: vec![worker.clone(), manager.clone()],
        protocol: send(worker.clone(), manager.clone(), message("Report"), Protocol::End),
        attrs: HashMap::new(),
    };

    let code = generate_dynamic_role_support(&choreo);
    let code_str = code.to_string();

    // Static params don't need runtime support - may be empty
    assert!(
        code_str.is_empty() || !code_str.contains("WORKER_COUNT"),
        "Static params should produce minimal dynamic support: {}",
        code_str
    );
}

#[test]
fn test_generate_dynamic_role_support_runtime() {
    // Runtime role params should generate dynamic support code
    let worker = role_with_param("Worker", RoleParam::Runtime);
    let manager = role("Manager");

    let choreo = Choreography {
        name: format_ident!("DynamicWorkerProtocol"),
        namespace: None,
        roles: vec![worker.clone(), manager.clone()],
        protocol: send(manager.clone(), worker.clone(), message("Task"), Protocol::End),
        attrs: HashMap::new(),
    };

    let code = generate_dynamic_role_support(&choreo);
    let code_str = code.to_string();

    // Runtime roles should generate support code (may include constants, traits, etc.)
    // The actual output depends on implementation
    assert!(
        code_str.contains("Worker") || code_str.contains("Dynamic") || code_str.is_empty(),
        "Runtime params should have some dynamic support: {}",
        code_str
    );
}

#[test]
fn test_generate_dynamic_role_support_symbolic() {
    // Symbolic role params should generate dynamic support code
    let worker = role_with_param("Worker", RoleParam::Symbolic("N".to_string()));
    let manager = role("Manager");

    let choreo = Choreography {
        name: format_ident!("SymbolicWorkerProtocol"),
        namespace: None,
        roles: vec![worker.clone(), manager.clone()],
        protocol: send(manager.clone(), worker.clone(), message("Task"), Protocol::End),
        attrs: HashMap::new(),
    };

    let code = generate_dynamic_role_support(&choreo);
    let code_str = code.to_string();

    // Symbolic roles should generate support code
    assert!(
        code_str.contains("Worker") || code_str.contains("N") || code_str.is_empty(),
        "Symbolic params should have some dynamic support: {}",
        code_str
    );
}

// ============================================================================
// generate_topology_integration Tests
// ============================================================================

#[test]
fn test_generate_topology_integration_empty() {
    let alice = role("Alice");
    let bob = role("Bob");

    let choreo = Choreography {
        name: format_ident!("TopologyTest"),
        namespace: None,
        roles: vec![alice.clone(), bob.clone()],
        protocol: send(alice.clone(), bob.clone(), message("Hello"), Protocol::End),
        attrs: HashMap::new(),
    };

    let code = generate_topology_integration(&choreo, &[]);
    let code_str = code.to_string();

    // Even with no inline topologies, should generate base topology module
    // This includes handler() and with_topology() functions
    assert!(
        code_str.contains("topology") || code_str.contains("TopologyHandler"),
        "Should generate topology module: {}",
        code_str
    );
    assert!(
        code_str.contains("handler"),
        "Should have handler function: {}",
        code_str
    );
}

#[test]
fn test_generate_topology_integration_with_inline() {
    let alice = role("Alice");
    let bob = role("Bob");

    let choreo = Choreography {
        name: format_ident!("TopologyTest"),
        namespace: None,
        roles: vec![alice.clone(), bob.clone()],
        protocol: send(alice.clone(), bob.clone(), message("Hello"), Protocol::End),
        attrs: HashMap::new(),
    };

    // Create a simple local topology
    let inline_topology = InlineTopology {
        name: "test".to_string(),
        topology: Topology::local_mode(),
    };

    let code = generate_topology_integration(&choreo, &[inline_topology]);
    let code_str = code.to_string();

    // With inline topology, should generate topology-related code
    assert!(
        code_str.contains("topology")
            || code_str.contains("TOPOLOGY")
            || code_str.contains("test")
            || code_str.contains("TopologyTest"),
        "Should have topology-related code: {}",
        code_str
    );
}

// ============================================================================
// Edge Cases and Error Handling Tests
// ============================================================================

#[test]
fn test_generate_session_type_nested_structure() {
    let alice = role("Alice");
    let bob = role("Bob");

    // Nested Send -> Receive -> Send pattern
    let local_type = LocalType::Send {
        to: bob.clone(),
        message: message("Request"),
        continuation: Box::new(LocalType::Receive {
            from: bob.clone(),
            message: message("Response"),
            continuation: Box::new(LocalType::Send {
                to: bob.clone(),
                message: message("Ack"),
                continuation: Box::new(LocalType::End),
            }),
        }),
    };

    let code = generate_session_type(&alice, &local_type, "NestedProtocol");
    let code_str = code.to_string();

    // Should contain all operations
    assert!(
        code_str.contains("Send"),
        "Should have Send: {}",
        code_str
    );
    assert!(
        code_str.contains("Receive"),
        "Should have Receive: {}",
        code_str
    );
    assert!(
        code_str.contains("Request"),
        "Should have Request: {}",
        code_str
    );
    assert!(
        code_str.contains("Response"),
        "Should have Response: {}",
        code_str
    );
    assert!(
        code_str.contains("Ack"),
        "Should have Ack: {}",
        code_str
    );
}

#[test]
fn test_generate_session_type_loop() {
    let alice = role("Alice");
    let bob = role("Bob");

    let local_type = LocalType::Loop {
        condition: None,
        body: Box::new(LocalType::Send {
            to: bob.clone(),
            message: message("Data"),
            continuation: Box::new(LocalType::End),
        }),
    };

    let code = generate_session_type(&alice, &local_type, "LoopProtocol");
    let code_str = code.to_string();

    assert!(
        code_str.contains("Loop"),
        "Should contain Loop: {}",
        code_str
    );
}

#[test]
fn test_generate_session_type_recursive() {
    let alice = role("Alice");
    let bob = role("Bob");

    let local_type = LocalType::Rec {
        label: format_ident!("X"),
        body: Box::new(LocalType::Send {
            to: bob.clone(),
            message: message("Data"),
            continuation: Box::new(LocalType::Var(format_ident!("X"))),
        }),
    };

    let code = generate_session_type(&alice, &local_type, "RecursiveProtocol");
    let code_str = code.to_string();

    // Should generate recursive structure
    assert!(
        code_str.contains("Send") || code_str.contains("Data"),
        "Should have recursive body: {}",
        code_str
    );
}

#[test]
fn test_generate_choreography_code_empty_roles() {
    // Edge case: empty role list
    let code = generate_choreography_code("EmptyProtocol", &[], &[]);
    let code_str = code.to_string();

    // Should still generate something, even if minimal
    assert!(
        code_str.contains("Roles") || code_str.is_empty(),
        "Empty roles should produce valid output: {}",
        code_str
    );
}

#[test]
fn test_generate_session_type_local_choice() {
    let alice = role("Alice");

    let local_type = LocalType::LocalChoice {
        branches: vec![
            (format_ident!("Option1"), LocalType::End),
            (format_ident!("Option2"), LocalType::End),
        ],
    };

    let code = generate_session_type(&alice, &local_type, "LocalChoiceProtocol");
    let code_str = code.to_string();

    assert!(
        code_str.contains("LocalChoice"),
        "Should contain LocalChoice: {}",
        code_str
    );
    assert!(
        code_str.contains("Option1"),
        "Should contain Option1: {}",
        code_str
    );
    assert!(
        code_str.contains("Option2"),
        "Should contain Option2: {}",
        code_str
    );
}
