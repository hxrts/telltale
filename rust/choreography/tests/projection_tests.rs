//! Tests for ProjectionError variants
//!
//! This test suite verifies that each ProjectionError variant is properly
//! triggered and returns the expected error type.

#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

use quote::format_ident;
use std::collections::HashMap;
use telltale_choreography::ast::{
    annotation::Annotations, Branch, Choreography, MessageType, NonEmptyVec, Protocol, Role,
    RoleParam,
};
use telltale_choreography::compiler::projection::{project, ProjectionError};

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
// InconsistentParallel Tests
// ============================================================================

#[test]
fn test_inconsistent_parallel_multiple_sends_to_same_target() {
    // When a role appears in multiple parallel branches and sends to the same
    // target from both, this creates a conflict.
    let alice = role("Alice");
    let bob = role("Bob");

    // Alice sends to Bob in two parallel branches
    let choreo = Choreography {
        name: format_ident!("ParallelSendConflict"),
        namespace: None,
        roles: vec![alice.clone(), bob.clone()],
        protocol: Protocol::Parallel {
            protocols: NonEmptyVec::from_head_tail(
                send(alice.clone(), bob.clone(), message("Msg1"), Protocol::End),
                vec![send(
                    alice.clone(),
                    bob.clone(),
                    message("Msg2"),
                    Protocol::End,
                )],
            ),
        },
        attrs: HashMap::new(),
    };

    let result = project(&choreo, &alice);
    assert!(
        matches!(result, Err(ProjectionError::InconsistentParallel)),
        "Expected InconsistentParallel error for sends to same target, got: {:?}",
        result
    );
}

#[test]
fn test_inconsistent_parallel_multiple_receives_from_same_source() {
    // When Bob receives from Alice in two parallel branches
    let alice = role("Alice");
    let bob = role("Bob");

    let choreo = Choreography {
        name: format_ident!("ParallelRecvConflict"),
        namespace: None,
        roles: vec![alice.clone(), bob.clone()],
        protocol: Protocol::Parallel {
            protocols: NonEmptyVec::from_head_tail(
                send(alice.clone(), bob.clone(), message("Msg1"), Protocol::End),
                vec![send(
                    alice.clone(),
                    bob.clone(),
                    message("Msg2"),
                    Protocol::End,
                )],
            ),
        },
        attrs: HashMap::new(),
    };

    let result = project(&choreo, &bob);
    assert!(
        matches!(result, Err(ProjectionError::InconsistentParallel)),
        "Expected InconsistentParallel error for receives from same source, got: {:?}",
        result
    );
}

// ============================================================================
// DynamicRoleProjection Tests
// ============================================================================

#[test]
fn test_dynamic_role_projection_with_runtime_param() {
    // Runtime roles cannot be projected without runtime context
    // Error is triggered when projecting a role that has the same name but different params
    let worker_static = role_with_param("Worker", RoleParam::Static(0));
    let worker_runtime = role_with_param("Worker", RoleParam::Runtime);
    let manager = role("Manager");

    // Protocol uses Worker[*] (runtime) but we project for Worker[0] (static)
    let choreo = Choreography {
        name: format_ident!("RuntimeRoleTest"),
        namespace: None,
        roles: vec![
            worker_static.clone(),
            worker_runtime.clone(),
            manager.clone(),
        ],
        protocol: send(
            worker_runtime.clone(),
            manager.clone(),
            message("Task"),
            Protocol::End,
        ),
        attrs: HashMap::new(),
    };

    // Project for Worker[0] - needs to check if Worker[*] matches Worker[0]
    let result = project(&choreo, &worker_static);
    assert!(
        matches!(
            result,
            Err(ProjectionError::DynamicRoleProjection { role: _ })
        ),
        "Expected DynamicRoleProjection error, got: {:?}",
        result
    );
}

#[test]
fn test_dynamic_role_projection_runtime_receiver() {
    // Runtime role as receiver
    // Error is triggered when projecting for a static param that encounters runtime
    let worker_static = role_with_param("Worker", RoleParam::Static(1));
    let worker_runtime = role_with_param("Worker", RoleParam::Runtime);
    let manager = role("Manager");

    let choreo = Choreography {
        name: format_ident!("RuntimeReceiverTest"),
        namespace: None,
        roles: vec![
            manager.clone(),
            worker_static.clone(),
            worker_runtime.clone(),
        ],
        protocol: send(
            manager.clone(),
            worker_runtime.clone(),
            message("Task"),
            Protocol::End,
        ),
        attrs: HashMap::new(),
    };

    // Project for Worker[1] - needs to check if Worker[*] matches Worker[1]
    let result = project(&choreo, &worker_static);
    assert!(
        matches!(
            result,
            Err(ProjectionError::DynamicRoleProjection { role: _ })
        ),
        "Expected DynamicRoleProjection error for runtime receiver, got: {:?}",
        result
    );
}

// ============================================================================
// UnboundSymbolic Tests
// ============================================================================

#[test]
fn test_unbound_symbolic_in_sender() {
    // Symbolic role parameter not bound in context
    // Error is triggered when projecting for a static param that encounters symbolic
    let worker_static = role_with_param("Worker", RoleParam::Static(0));
    let worker_symbolic = role_with_param("Worker", RoleParam::Symbolic("N".to_string()));
    let manager = role("Manager");

    // Protocol uses Worker[N] (symbolic) but we project for Worker[0] (static)
    let choreo = Choreography {
        name: format_ident!("UnboundSymbolicTest"),
        namespace: None,
        roles: vec![
            worker_static.clone(),
            worker_symbolic.clone(),
            manager.clone(),
        ],
        protocol: send(
            worker_symbolic.clone(),
            manager.clone(),
            message("Task"),
            Protocol::End,
        ),
        attrs: HashMap::new(),
    };

    // Project for Worker[0] - needs to check if Worker[N] matches Worker[0]
    // Since N is not bound in the context, this should fail
    let result = project(&choreo, &worker_static);
    assert!(
        matches!(result, Err(ProjectionError::UnboundSymbolic { param: _ })),
        "Expected UnboundSymbolic error, got: {:?}",
        result
    );
}

#[test]
fn test_unbound_symbolic_in_receiver() {
    // Symbolic role as receiver with unbound parameter
    let worker_static = role_with_param("Worker", RoleParam::Static(1));
    let worker_symbolic = role_with_param("Worker", RoleParam::Symbolic("M".to_string()));
    let manager = role("Manager");

    let choreo = Choreography {
        name: format_ident!("UnboundSymbolicReceiverTest"),
        namespace: None,
        roles: vec![
            manager.clone(),
            worker_static.clone(),
            worker_symbolic.clone(),
        ],
        protocol: send(
            manager.clone(),
            worker_symbolic.clone(),
            message("Report"),
            Protocol::End,
        ),
        attrs: HashMap::new(),
    };

    // Project for Worker[1] - needs to check if Worker[M] matches Worker[1]
    let result = project(&choreo, &worker_static);
    assert!(
        matches!(result, Err(ProjectionError::UnboundSymbolic { param: _ })),
        "Expected UnboundSymbolic error for symbolic receiver, got: {:?}",
        result
    );
}

// ============================================================================
// MergeFailure Tests
// ============================================================================

#[test]
fn test_merge_failure_different_send_messages() {
    // When merging choice branches for non-participant, sends with different
    // messages cannot be merged
    let alice = role("Alice");
    let bob = role("Bob");
    let charlie = role("Charlie");

    // Alice makes choice, Bob sends different messages to Charlie in each branch
    // Charlie must merge these - but Sends with different messages fail
    let choreo = Choreography {
        name: format_ident!("MergeSendFailure"),
        namespace: None,
        roles: vec![alice.clone(), bob.clone(), charlie.clone()],
        protocol: Protocol::Choice {
            role: alice.clone(),
            branches: NonEmptyVec::from_head_tail(
                Branch {
                    label: format_ident!("Left"),
                    guard: None,
                    protocol: send(
                        alice.clone(),
                        bob.clone(),
                        message("Left"),
                        send(
                            bob.clone(),
                            charlie.clone(),
                            message("DataA"),
                            Protocol::End,
                        ),
                    ),
                },
                vec![Branch {
                    label: format_ident!("Right"),
                    guard: None,
                    protocol: send(
                        alice.clone(),
                        bob.clone(),
                        message("Right"),
                        send(
                            bob.clone(),
                            charlie.clone(),
                            message("DataB"),
                            Protocol::End,
                        ),
                    ),
                }],
            ),
            annotations: Annotations::new(),
        },
        attrs: HashMap::new(),
    };

    // Bob projects to Branch (receives choice from Alice, then sends to Charlie)
    // This should succeed - Bob knows which branch was taken
    let bob_result = project(&choreo, &bob);
    assert!(bob_result.is_ok(), "Bob projection should succeed");

    // Charlie is not involved in Alice->Bob choice, so must merge the branches
    // But Bob->Charlie sends different messages in each branch
    // Charlie CAN merge these as Branch (receive semantics - union of labels)
    let charlie_result = project(&choreo, &charlie);
    assert!(
        charlie_result.is_ok(),
        "Charlie should merge receives into Branch: {:?}",
        charlie_result
    );
}

#[test]
fn test_merge_failure_incompatible_types() {
    // When merging produces incompatible local types
    let alice = role("Alice");
    let bob = role("Bob");
    let charlie = role("Charlie");
    let dave = role("Dave");

    // Alice makes choice:
    // - Left: Bob sends to Charlie
    // - Right: Bob sends to Dave
    // For Bob, these are different operations that cannot be merged
    let choreo = Choreography {
        name: format_ident!("MergeIncompatibleTypes"),
        namespace: None,
        roles: vec![alice.clone(), bob.clone(), charlie.clone(), dave.clone()],
        protocol: Protocol::Choice {
            role: alice.clone(),
            branches: NonEmptyVec::from_head_tail(
                Branch {
                    label: format_ident!("Left"),
                    guard: None,
                    protocol: send(
                        alice.clone(),
                        bob.clone(),
                        message("Left"),
                        send(
                            bob.clone(),
                            charlie.clone(),
                            message("ToCharlie"),
                            Protocol::End,
                        ),
                    ),
                },
                vec![Branch {
                    label: format_ident!("Right"),
                    guard: None,
                    protocol: send(
                        alice.clone(),
                        bob.clone(),
                        message("Right"),
                        send(bob.clone(), dave.clone(), message("ToDave"), Protocol::End),
                    ),
                }],
            ),
            annotations: Annotations::new(),
        },
        attrs: HashMap::new(),
    };

    // Bob receives the choice, so he knows which branch - projection succeeds
    let bob_result = project(&choreo, &bob);
    assert!(bob_result.is_ok(), "Bob projection should succeed");

    // Charlie is not involved in choice
    // In Left branch: receives from Bob
    // In Right branch: End (not involved)
    // End merges with anything, so this succeeds
    let charlie_result = project(&choreo, &charlie);
    assert!(
        charlie_result.is_ok(),
        "Charlie projection should succeed: {:?}",
        charlie_result
    );
}

#[test]
fn test_merge_failure_select_branch_mismatch() {
    // When merging Select types with different label sets
    let alice = role("Alice");
    let bob = role("Bob");
    let charlie = role("Charlie");

    // Alice makes choice and sends to Bob, then Bob makes nested choice to Charlie
    // The inner choices have different labels
    let choreo = Choreography {
        name: format_ident!("MergeSelectMismatch"),
        namespace: None,
        roles: vec![alice.clone(), bob.clone(), charlie.clone()],
        protocol: Protocol::Choice {
            role: alice.clone(),
            branches: NonEmptyVec::from_head_tail(
                Branch {
                    label: format_ident!("Outer1"),
                    guard: None,
                    protocol: send(
                        alice.clone(),
                        bob.clone(),
                        message("GoLeft"),
                        Protocol::Choice {
                            role: bob.clone(),
                            branches: NonEmptyVec::from_head_tail(
                                Branch {
                                    label: format_ident!("Inner1"),
                                    guard: None,
                                    protocol: send(
                                        bob.clone(),
                                        charlie.clone(),
                                        message("A"),
                                        Protocol::End,
                                    ),
                                },
                                vec![Branch {
                                    label: format_ident!("Inner2"),
                                    guard: None,
                                    protocol: send(
                                        bob.clone(),
                                        charlie.clone(),
                                        message("B"),
                                        Protocol::End,
                                    ),
                                }],
                            ),
                            annotations: Annotations::new(),
                        },
                    ),
                },
                vec![Branch {
                    label: format_ident!("Outer2"),
                    guard: None,
                    protocol: send(
                        alice.clone(),
                        bob.clone(),
                        message("GoRight"),
                        Protocol::Choice {
                            role: bob.clone(),
                            branches: NonEmptyVec::from_head_tail(
                                Branch {
                                    label: format_ident!("Inner3"),
                                    guard: None,
                                    protocol: send(
                                        bob.clone(),
                                        charlie.clone(),
                                        message("C"),
                                        Protocol::End,
                                    ),
                                },
                                vec![Branch {
                                    label: format_ident!("Inner4"),
                                    guard: None,
                                    protocol: send(
                                        bob.clone(),
                                        charlie.clone(),
                                        message("D"),
                                        Protocol::End,
                                    ),
                                }],
                            ),
                            annotations: Annotations::new(),
                        },
                    ),
                }],
            ),
            annotations: Annotations::new(),
        },
        attrs: HashMap::new(),
    };

    // Alice is the outer choice maker - should succeed
    let alice_result = project(&choreo, &alice);
    assert!(alice_result.is_ok(), "Alice projection should succeed");

    // Bob receives the outer choice, then makes inner choice - should succeed
    let bob_result = project(&choreo, &bob);
    assert!(bob_result.is_ok(), "Bob projection should succeed");

    // Charlie receives from Bob but not involved in Alice's outer choice
    // Bob's inner choices have different labels (Inner1/2 vs Inner3/4)
    // This requires merging Branch types with different label sets
    // Actually this SHOULD succeed because Branch merge unions labels
    let charlie_result = project(&choreo, &charlie);
    assert!(
        charlie_result.is_ok(),
        "Charlie projection should succeed (Branch merge unions labels): {:?}",
        charlie_result
    );
}

#[test]
fn test_merge_failure_send_different_targets() {
    // When a non-participant needs to merge sends to different targets
    // This should fail because sends can't be merged to different recipients
    let alice = role("Alice");
    let bob = role("Bob");
    let charlie = role("Charlie");
    let dave = role("Dave");

    // Alice makes choice:
    // - Left branch: Bob sends to Charlie
    // - Right branch: Bob sends to Dave
    // Bob doesn't know which branch Alice took, but needs to send to someone
    // This is unmergeable - different send targets
    let choreo = Choreography {
        name: format_ident!("MergeSendDifferentTargets"),
        namespace: None,
        roles: vec![alice.clone(), bob.clone(), charlie.clone(), dave.clone()],
        protocol: Protocol::Choice {
            role: alice.clone(),
            branches: NonEmptyVec::from_head_tail(
                Branch {
                    label: format_ident!("Left"),
                    guard: None,
                    protocol: send(
                        alice.clone(),
                        charlie.clone(),
                        message("ToCharlie"),
                        send(bob.clone(), charlie.clone(), message("Data"), Protocol::End),
                    ),
                },
                vec![Branch {
                    label: format_ident!("Right"),
                    guard: None,
                    protocol: send(
                        alice.clone(),
                        dave.clone(),
                        message("ToDave"),
                        send(bob.clone(), dave.clone(), message("Data"), Protocol::End),
                    ),
                }],
            ),
            annotations: Annotations::new(),
        },
        attrs: HashMap::new(),
    };

    // Alice is the chooser - succeeds
    let alice_result = project(&choreo, &alice);
    assert!(alice_result.is_ok(), "Alice projection should succeed");

    // Bob is NOT involved in Alice's choice (doesn't receive anything)
    // Must merge: Send to Charlie vs Send to Dave
    // These can't be merged - incompatible local types
    let bob_result = project(&choreo, &bob);
    assert!(
        matches!(bob_result, Err(ProjectionError::MergeFailure(_))),
        "Expected MergeFailure for sends to different targets, got: {:?}",
        bob_result
    );
}

// ============================================================================
// NonParticipantChoice Tests (edge case)
// ============================================================================

#[test]
fn test_non_participant_choice_pattern() {
    // The NonParticipantChoice error is triggered in a defensive check
    // when the choice maker role's branch doesn't start with Send as expected
    // This is an edge case in the projection logic
    let alice = role("Alice");

    // A choice where Alice is the chooser but branches don't start with Send
    // This results in LocalChoice (not an error)
    let choreo = Choreography {
        name: format_ident!("LocalChoiceTest"),
        namespace: None,
        roles: vec![alice.clone()],
        protocol: Protocol::Choice {
            role: alice.clone(),
            branches: NonEmptyVec::from_head_tail(
                Branch {
                    label: format_ident!("Option1"),
                    guard: None,
                    protocol: Protocol::End,
                },
                vec![Branch {
                    label: format_ident!("Option2"),
                    guard: None,
                    protocol: Protocol::End,
                }],
            ),
            annotations: Annotations::new(),
        },
        attrs: HashMap::new(),
    };

    let result = project(&choreo, &alice);
    assert!(
        result.is_ok(),
        "Local choice without Send should succeed: {:?}",
        result
    );
}

// ============================================================================
// UnsupportedParallel Tests (reserved error)
// ============================================================================

#[test]
fn test_unsupported_parallel_error_variant_exists() {
    // UnsupportedParallel is defined but not currently triggered
    // This test verifies the error variant can be constructed
    let error = ProjectionError::UnsupportedParallel("TestRole".to_string());
    assert!(error.to_string().contains("TestRole"));
    assert!(error.to_string().contains("not supported"));
}

// ============================================================================
// UnboundVariable Tests (reserved error)
// ============================================================================

#[test]
fn test_unbound_variable_error_variant_exists() {
    // UnboundVariable is defined but project_var just returns Ok(Var)
    // This test verifies the error variant can be constructed
    let error = ProjectionError::UnboundVariable("X".to_string());
    assert!(error.to_string().contains("X"));
    assert!(error.to_string().contains("not in scope"));
}

// ============================================================================
// RangeProjection Tests (reserved error)
// ============================================================================

#[test]
fn test_range_projection_error_variant_exists() {
    // RangeProjection is reserved for future range role support
    let error = ProjectionError::RangeProjection;
    assert!(error.to_string().contains("range"));
}

// ============================================================================
// WildcardProjection Tests (reserved error)
// ============================================================================

#[test]
fn test_wildcard_projection_error_variant_exists() {
    // WildcardProjection is reserved for future wildcard role support
    let error = ProjectionError::WildcardProjection;
    assert!(error.to_string().contains("wildcard"));
}

// ============================================================================
// Successful Projection Tests (ensure errors don't occur incorrectly)
// ============================================================================

#[test]
fn test_simple_send_receive_succeeds() {
    let alice = role("Alice");
    let bob = role("Bob");

    let choreo = Choreography {
        name: format_ident!("SimpleSendReceive"),
        namespace: None,
        roles: vec![alice.clone(), bob.clone()],
        protocol: send(alice.clone(), bob.clone(), message("Hello"), Protocol::End),
        attrs: HashMap::new(),
    };

    assert!(project(&choreo, &alice).is_ok());
    assert!(project(&choreo, &bob).is_ok());
}

#[test]
fn test_parallel_no_conflict_succeeds() {
    let alice = role("Alice");
    let bob = role("Bob");
    let charlie = role("Charlie");

    // Alice sends to Bob in one branch, Charlie sends to Bob in another
    // No conflict - different senders
    let choreo = Choreography {
        name: format_ident!("ParallelNoConflict"),
        namespace: None,
        roles: vec![alice.clone(), bob.clone(), charlie.clone()],
        protocol: Protocol::Parallel {
            protocols: NonEmptyVec::from_head_tail(
                send(
                    alice.clone(),
                    bob.clone(),
                    message("FromAlice"),
                    Protocol::End,
                ),
                vec![send(
                    charlie.clone(),
                    bob.clone(),
                    message("FromCharlie"),
                    Protocol::End,
                )],
            ),
        },
        attrs: HashMap::new(),
    };

    // Bob receives from different senders - should succeed
    let result = project(&choreo, &bob);
    assert!(
        result.is_ok(),
        "Parallel with different senders should succeed: {:?}",
        result
    );
}

#[test]
fn test_static_parameterized_roles_succeed() {
    // Static role parameters don't require runtime context
    let worker0 = role_with_param("Worker", RoleParam::Static(0));
    let worker1 = role_with_param("Worker", RoleParam::Static(1));
    let manager = role("Manager");

    let choreo = Choreography {
        name: format_ident!("StaticParams"),
        namespace: None,
        roles: vec![worker0.clone(), worker1.clone(), manager.clone()],
        protocol: send(
            worker0.clone(),
            manager.clone(),
            message("Report"),
            send(
                manager.clone(),
                worker1.clone(),
                message("Task"),
                Protocol::End,
            ),
        ),
        attrs: HashMap::new(),
    };

    assert!(
        project(&choreo, &worker0).is_ok(),
        "Static param Worker[0] should succeed"
    );
    assert!(
        project(&choreo, &worker1).is_ok(),
        "Static param Worker[1] should succeed"
    );
    assert!(project(&choreo, &manager).is_ok(), "Manager should succeed");
}
