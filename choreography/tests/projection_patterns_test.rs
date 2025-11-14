#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

// Tests for enhanced projection patterns
//
// This test suite verifies the 3 new projection patterns:
// 1. Choice branches without initial Send (local choices)
// 2. Loop conditions preserved in projections
// 3. Improved parallel branch merging with conflict detection

use quote::{format_ident, quote};
use rumpsteak_aura_choreography::ast::{
    protocol::Condition, Branch, Choreography, LocalType, MessageType, Protocol, Role,
};
use rumpsteak_aura_choreography::compiler::projection::project;
use std::collections::HashMap;

#[test]
fn test_local_choice_without_send() {
    // Test: Choice branch that doesn't start with Send
    // Should project to LocalChoice for the chooser
    let alice = Role::new(format_ident!("Alice"));

    let choreo = Choreography {
        name: format_ident!("LocalChoiceTest"),
        namespace: None,
        roles: vec![alice.clone()],
        protocol: Protocol::Choice {
            role: alice.clone(),
            branches: vec![
                Branch {
                    label: format_ident!("option1"),
                    guard: None,
                    protocol: Protocol::End, // No Send - local decision
                },
                Branch {
                    label: format_ident!("option2"),
                    guard: None,
                    protocol: Protocol::End,
                },
            ],
            annotations: HashMap::new(),
        },
        attrs: HashMap::new(),
    };

    let projected = project(&choreo, &alice).unwrap();

    // Alice should get a LocalChoice (not Select)
    match projected {
        LocalType::LocalChoice { branches } => {
            assert_eq!(branches.len(), 2, "Should have both branches");
            assert_eq!(branches[0].0.to_string(), "option1");
            assert_eq!(branches[1].0.to_string(), "option2");
        }
        _ => panic!("Expected LocalChoice, got: {projected:?}"),
    }
}

#[test]
fn test_loop_with_condition() {
    // Test: Loop with a count condition
    // Should preserve condition in projected local type
    let alice = Role::new(format_ident!("Alice"));
    let bob = Role::new(format_ident!("Bob"));

    let choreo = Choreography {
        name: format_ident!("LoopConditionTest"),
        namespace: None,
        roles: vec![alice.clone(), bob.clone()],
        protocol: Protocol::Loop {
            condition: Some(Condition::Count(5)),
            body: Box::new(Protocol::Send {
                from: alice.clone(),
                to: bob.clone(),
                message: MessageType {
                    name: format_ident!("Data"),

                    type_annotation: None,
                    payload: Some(quote! { String }),
                },
                continuation: Box::new(Protocol::End),
                annotations: HashMap::new(),
                from_annotations: HashMap::new(),
                to_annotations: HashMap::new(),
            }),
        },
        attrs: HashMap::new(),
    };

    let alice_proj = project(&choreo, &alice).unwrap();

    // Alice should get a Loop with the condition
    match alice_proj {
        LocalType::Loop { condition, body } => {
            assert!(condition.is_some(), "Condition should be preserved");
            if let Some(Condition::Count(n)) = condition {
                assert_eq!(n, 5, "Count should be 5");
            } else {
                panic!("Expected Count condition");
            }
            // Body should be a Send
            assert!(matches!(*body, LocalType::Send { .. }));
        }
        _ => panic!("Expected Loop, got: {alice_proj:?}"),
    }
}

#[test]
fn test_parallel_no_conflict() {
    // Test: Parallel branches with different recipients (no conflict)
    // Should merge successfully
    let alice = Role::new(format_ident!("Alice"));
    let bob = Role::new(format_ident!("Bob"));
    let charlie = Role::new(format_ident!("Charlie"));

    let choreo = Choreography {
        name: format_ident!("ParallelNoConflict"),
        namespace: None,
        roles: vec![alice.clone(), bob.clone(), charlie.clone()],
        protocol: Protocol::Parallel {
            protocols: vec![
                Protocol::Send {
                    from: alice.clone(),
                    to: bob.clone(),
                    message: MessageType {
                        name: format_ident!("Msg1"),

                        type_annotation: None,
                        payload: Some(quote! { String }),
                    },
                    continuation: Box::new(Protocol::End),
                    annotations: HashMap::new(),
                    from_annotations: HashMap::new(),
                    to_annotations: HashMap::new(),
                },
                Protocol::Send {
                    from: alice.clone(),
                    to: charlie.clone(),
                    message: MessageType {
                        name: format_ident!("Msg2"),

                        type_annotation: None,
                        payload: Some(quote! { i32 }),
                    },
                    continuation: Box::new(Protocol::End),
                    annotations: HashMap::new(),
                    from_annotations: HashMap::new(),
                    to_annotations: HashMap::new(),
                },
            ],
        },
        attrs: HashMap::new(),
    };

    // Alice's projection should succeed (no conflict - different recipients)
    let alice_proj = project(&choreo, &alice);
    assert!(alice_proj.is_ok(), "Parallel merge should succeed");

    // Should merge into sequential sends
    match alice_proj.unwrap() {
        LocalType::Send { to, .. } => {
            // First send (order is implementation-dependent)
            assert!(to == bob || to == charlie);
        }
        _ => panic!("Expected Send"),
    }
}

#[test]
fn test_parallel_with_conflict() {
    // Test: Parallel branches with same recipient (conflict)
    // Should detect conflict and return error
    let alice = Role::new(format_ident!("Alice"));
    let bob = Role::new(format_ident!("Bob"));

    let choreo = Choreography {
        name: format_ident!("ParallelConflict"),
        namespace: None,
        roles: vec![alice.clone(), bob.clone()],
        protocol: Protocol::Parallel {
            protocols: vec![
                Protocol::Send {
                    from: alice.clone(),
                    to: bob.clone(),
                    message: MessageType {
                        name: format_ident!("Msg1"),

                        type_annotation: None,
                        payload: Some(quote! { String }),
                    },
                    continuation: Box::new(Protocol::End),
                    annotations: HashMap::new(),
                    from_annotations: HashMap::new(),
                    to_annotations: HashMap::new(),
                },
                Protocol::Send {
                    from: alice.clone(),
                    to: bob.clone(), // Same recipient - conflict!
                    message: MessageType {
                        name: format_ident!("Msg2"),

                        type_annotation: None,
                        payload: Some(quote! { i32 }),
                    },
                    continuation: Box::new(Protocol::End),
                    annotations: HashMap::new(),
                    from_annotations: HashMap::new(),
                    to_annotations: HashMap::new(),
                },
            ],
        },
        attrs: HashMap::new(),
    };

    // Alice's projection should fail (conflict detected)
    let alice_proj = project(&choreo, &alice);
    assert!(alice_proj.is_err(), "Should detect parallel conflict");
}

#[test]
fn test_mixed_choice_communicated_vs_local() {
    // Test: Verify that communicated choice (with Send) still works
    let alice = Role::new(format_ident!("Alice"));
    let bob = Role::new(format_ident!("Bob"));

    let choreo = Choreography {
        name: format_ident!("CommunicatedChoice"),
        namespace: None,
        roles: vec![alice.clone(), bob.clone()],
        protocol: Protocol::Choice {
            role: alice.clone(),
            branches: vec![
                Branch {
                    label: format_ident!("yes"),
                    guard: None,
                    protocol: Protocol::Send {
                        from: alice.clone(),
                        to: bob.clone(),
                        message: MessageType {
                            name: format_ident!("Data"),

                            type_annotation: None,
                            payload: Some(quote! { String }),
                        },
                        continuation: Box::new(Protocol::End),
                        annotations: HashMap::new(),
                        from_annotations: HashMap::new(),
                        to_annotations: HashMap::new(),
                    },
                },
                Branch {
                    label: format_ident!("no"),
                    guard: None,
                    protocol: Protocol::Send {
                        from: alice.clone(),
                        to: bob.clone(),
                        message: MessageType {
                            name: format_ident!("NoData"),

                            type_annotation: None,
                            payload: Some(quote! { () }),
                        },
                        continuation: Box::new(Protocol::End),
                        annotations: HashMap::new(),
                        from_annotations: HashMap::new(),
                        to_annotations: HashMap::new(),
                    },
                },
            ],
            annotations: HashMap::new(),
        },
        attrs: HashMap::new(),
    };

    // Alice should get Select (communicated choice)
    let alice_proj = project(&choreo, &alice).unwrap();
    match alice_proj {
        LocalType::Select { to, branches } => {
            assert_eq!(to, bob, "Select should be to Bob");
            assert_eq!(branches.len(), 2, "Should have both branches");
        }
        _ => panic!("Expected Select, got: {alice_proj:?}"),
    }

    // Bob should get Branch (receives choice)
    let bob_proj = project(&choreo, &bob).unwrap();
    match bob_proj {
        LocalType::Branch { from, branches } => {
            assert_eq!(from, alice, "Branch should be from Alice");
            assert_eq!(branches.len(), 2, "Should have both branches");
        }
        _ => panic!("Expected Branch, got: {bob_proj:?}"),
    }
}

#[test]
fn test_loop_without_condition() {
    // Test: Loop without explicit condition
    // Should project to Loop with None condition
    let alice = Role::new(format_ident!("Alice"));

    let choreo = Choreography {
        name: format_ident!("LoopNoCondition"),
        namespace: None,
        roles: vec![alice.clone()],
        protocol: Protocol::Loop {
            condition: None,
            body: Box::new(Protocol::End),
        },
        attrs: HashMap::new(),
    };

    let projected = project(&choreo, &alice).unwrap();

    // Since body is End and Alice doesn't participate, should project to End
    assert_eq!(projected, LocalType::End);
}
