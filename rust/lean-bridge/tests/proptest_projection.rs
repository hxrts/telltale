//! Property-based tests for projection correctness.
//!
//! These tests verify that Rust's projection implementation matches
//! the formally verified Lean implementation using property-based testing.
//!
//! The tests:
//! 1. Generate random GlobalTypes using proptest
//! 2. Project them using Rust's projection algorithm
//! 3. Validate the result against Lean's verified projection
//!
//! All tests use fixed seeds for full reproducibility and skip gracefully
//! when the Lean binary is unavailable.

#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

use proptest::prelude::*;
use proptest::strategy::ValueTree;
use proptest::test_runner::{Config, RngAlgorithm, TestRng, TestRunner};
use serde_json::{json, Value};
use telltale_lean_bridge::{global_to_json, local_to_json, LeanRunner};
use telltale_theory::projection::{project, project_all};
use telltale_types::{GlobalType, Label, LocalTypeR, PayloadSort};

/// Deterministic seed for property-based tests.
const DETERMINISTIC_SEED: [u8; 32] = [
    0x50, 0x72, 0x6F, 0x6A, 0x65, 0x63, 0x74, 0x69, // "Projecti"
    0x6F, 0x6E, 0x54, 0x65, 0x73, 0x74, 0x53, 0x65, // "onTestSe"
    0x65, 0x64, 0x46, 0x6F, 0x72, 0x4C, 0x65, 0x61, // "edForLea"
    0x6E, 0x56, 0x65, 0x72, 0x69, 0x66, 0x79, 0x21, // "nVerify!"
];

/// Helper macro to skip tests when Lean binary is unavailable.
macro_rules! skip_without_lean {
    () => {
        if !LeanRunner::is_available() {
            eprintln!(
                "SKIPPED: Lean binary not available. Run `cd lean && lake build telltale_validator` to enable."
            );
            return;
        }
    };
}

// ============================================================================
// Strategies for generating test data
// ============================================================================

/// Strategy for generating role names.
fn role_strategy() -> impl Strategy<Value = String> {
    prop_oneof![
        Just("Alice".to_string()),
        Just("Bob".to_string()),
        Just("Carol".to_string()),
        Just("Server".to_string()),
        Just("Client".to_string()),
    ]
}

/// Strategy for generating labels.
fn label_strategy() -> impl Strategy<Value = Label> {
    prop_oneof![
        Just(Label::new("msg")),
        Just(Label::new("request")),
        Just(Label::new("response")),
        Just(Label::new("ping")),
        Just(Label::new("pong")),
        Just(Label::new("accept")),
        Just(Label::new("reject")),
        Just(Label::with_sort("data", PayloadSort::Nat)),
        Just(Label::with_sort("flag", PayloadSort::Bool)),
    ]
}

/// Strategy for generating simple GlobalTypes (non-recursive).
fn simple_global_strategy() -> impl Strategy<Value = GlobalType> {
    prop_oneof![
        // End type
        Just(GlobalType::End),
        // Single communication
        (role_strategy(), role_strategy(), label_strategy())
            .prop_filter("sender != receiver", |(s, r, _)| s != r)
            .prop_map(|(s, r, l)| GlobalType::comm(&s, &r, vec![(l, GlobalType::End)])),
        // Two communications in sequence
        (
            role_strategy(),
            role_strategy(),
            label_strategy(),
            role_strategy(),
            role_strategy(),
            label_strategy()
        )
            .prop_filter("no self-comm", |(s1, r1, _, s2, r2, _)| s1 != r1
                && s2 != r2)
            .prop_map(|(s1, r1, l1, s2, r2, l2)| {
                GlobalType::comm(
                    &s1,
                    &r1,
                    vec![(l1, GlobalType::comm(&s2, &r2, vec![(l2, GlobalType::End)]))],
                )
            }),
        // Choice (two branches)
        (
            role_strategy(),
            role_strategy(),
            label_strategy(),
            label_strategy()
        )
            .prop_filter(
                "sender != receiver and distinct labels",
                |(s, r, l1, l2)| s != r && l1.name != l2.name
            )
            .prop_map(|(s, r, l1, l2)| {
                GlobalType::comm(&s, &r, vec![(l1, GlobalType::End), (l2, GlobalType::End)])
            }),
    ]
}

/// Strategy for generating choice protocols with continuations.
/// This specifically tests the bug where choice continuations were incorrectly projected.
fn choice_with_continuation_strategy() -> impl Strategy<Value = GlobalType> {
    (
        role_strategy(),
        role_strategy(),
        label_strategy(),
        label_strategy(),
        label_strategy(),
        label_strategy(),
    )
        .prop_filter(
            "valid choice protocol",
            |(sender, receiver, l1, l2, cont1, cont2)| {
                sender != receiver && l1.name != l2.name && cont1.name != cont2.name
            },
        )
        .prop_map(|(sender, receiver, l1, l2, cont1, cont2)| {
            // Choice: sender -> receiver: { l1 -> sender -> receiver: cont1. end,
            //                               l2 -> sender -> receiver: cont2. end }
            GlobalType::comm(
                &sender,
                &receiver,
                vec![
                    (
                        l1,
                        GlobalType::comm(&sender, &receiver, vec![(cont1, GlobalType::End)]),
                    ),
                    (
                        l2,
                        GlobalType::comm(&sender, &receiver, vec![(cont2, GlobalType::End)]),
                    ),
                ],
            )
        })
}

// ============================================================================
// Conversion helpers
// ============================================================================

/// Convert a GlobalType to the JSON format expected by the Lean validator.
fn global_to_choreography_json(g: &GlobalType) -> Value {
    global_to_json(g)
}

/// Convert a LocalTypeR to the program JSON format expected by the Lean validator.
fn local_to_program_json(role: &str, local: &LocalTypeR) -> Value {
    json!({
        "role": role,
        "local_type": local_to_json(local)
    })
}

// ============================================================================
// Property tests for basic projection correctness
// ============================================================================

#[test]
fn test_projection_preserves_roles() {
    let mut runner = TestRunner::new_with_rng(
        Config::default(),
        TestRng::from_seed(RngAlgorithm::ChaCha, &DETERMINISTIC_SEED),
    );

    let strategy = simple_global_strategy();

    for _ in 0..50 {
        let global = strategy
            .new_tree(&mut runner)
            .expect("Should generate value")
            .current();

        let roles = global.roles();

        // Every role in the protocol should get a valid projection
        for role in &roles {
            let local = project(&global, role);
            assert!(
                local.is_ok(),
                "Projection should succeed for role {} in {:?}",
                role,
                global
            );
        }
    }
}

#[test]
fn test_sender_gets_send_receiver_gets_recv() {
    let mut runner = TestRunner::new_with_rng(
        Config::default(),
        TestRng::from_seed(RngAlgorithm::ChaCha, &DETERMINISTIC_SEED),
    );

    // Generate single-communication global types
    let strategy = (role_strategy(), role_strategy(), label_strategy())
        .prop_filter("sender != receiver", |(s, r, _)| s != r)
        .prop_map(|(s, r, l)| {
            (
                s.clone(),
                r.clone(),
                GlobalType::comm(&s, &r, vec![(l, GlobalType::End)]),
            )
        });

    for _ in 0..30 {
        let (sender, receiver, global) = strategy
            .new_tree(&mut runner)
            .expect("Should generate value")
            .current();

        // Sender should see Send
        let sender_local = project(&global, &sender).expect("Sender projection should succeed");
        assert!(
            matches!(&sender_local, LocalTypeR::Send { partner, .. } if partner == &receiver),
            "Sender {} should see Send to {}, got {:?}",
            sender,
            receiver,
            sender_local
        );

        // Receiver should see Recv
        let receiver_local =
            project(&global, &receiver).expect("Receiver projection should succeed");
        assert!(
            matches!(&receiver_local, LocalTypeR::Recv { partner, .. } if partner == &sender),
            "Receiver {} should see Recv from {}, got {:?}",
            receiver,
            sender,
            receiver_local
        );
    }
}

#[test]
fn test_choice_projections_have_all_branches() {
    let mut runner = TestRunner::new_with_rng(
        Config::default(),
        TestRng::from_seed(RngAlgorithm::ChaCha, &DETERMINISTIC_SEED),
    );

    // Generate choice protocols
    let strategy = (
        role_strategy(),
        role_strategy(),
        label_strategy(),
        label_strategy(),
    )
        .prop_filter("valid choice", |(s, r, l1, l2)| {
            s != r && l1.name != l2.name
        })
        .prop_map(|(s, r, l1, l2)| {
            (
                s.clone(),
                r.clone(),
                l1.name.clone(),
                l2.name.clone(),
                GlobalType::comm(&s, &r, vec![(l1, GlobalType::End), (l2, GlobalType::End)]),
            )
        });

    for _ in 0..30 {
        let (sender, receiver, label1, label2, global) = strategy
            .new_tree(&mut runner)
            .expect("Should generate value")
            .current();

        // Sender should see both branches in Send
        let sender_local = project(&global, &sender).expect("Sender projection should succeed");
        if let LocalTypeR::Send { branches, .. } = sender_local {
            let labels: Vec<_> = branches
                .iter()
                .map(|(l, _vt, _c)| l.name.as_str())
                .collect();
            assert!(
                labels.contains(&label1.as_str()) && labels.contains(&label2.as_str()),
                "Sender should see both labels {} and {}, got {:?}",
                label1,
                label2,
                labels
            );
        } else {
            panic!("Sender should get Send, got {:?}", sender_local);
        }

        // Receiver should see both branches in Recv
        let receiver_local =
            project(&global, &receiver).expect("Receiver projection should succeed");
        if let LocalTypeR::Recv { branches, .. } = receiver_local {
            let labels: Vec<_> = branches
                .iter()
                .map(|(l, _vt, _c)| l.name.as_str())
                .collect();
            assert!(
                labels.contains(&label1.as_str()) && labels.contains(&label2.as_str()),
                "Receiver should see both labels {} and {}, got {:?}",
                label1,
                label2,
                labels
            );
        } else {
            panic!("Receiver should get Recv, got {:?}", receiver_local);
        }
    }
}

/// This test specifically targets the bug that was fixed:
/// Choice branches should include the continuation Send/Recv, not just End.
#[test]
fn test_choice_continuations_preserved() {
    let mut runner = TestRunner::new_with_rng(
        Config::default(),
        TestRng::from_seed(RngAlgorithm::ChaCha, &DETERMINISTIC_SEED),
    );

    let strategy = choice_with_continuation_strategy();

    for _ in 0..30 {
        let global = strategy
            .new_tree(&mut runner)
            .expect("Should generate value")
            .current();

        let roles = global.roles();
        assert!(roles.len() >= 2, "Should have at least 2 roles");

        for role in &roles {
            let local = project(&global, role).expect("Projection should succeed");

            // Check that the local type is not just Send/Recv -> End when there should be continuations
            fn has_nested_action(lt: &LocalTypeR, depth: usize) -> bool {
                match lt {
                    LocalTypeR::End | LocalTypeR::Var(_) => depth > 0,
                    LocalTypeR::Send { branches, .. } | LocalTypeR::Recv { branches, .. } => {
                        branches
                            .iter()
                            .all(|(_, _vt, cont)| has_nested_action(cont, depth + 1))
                    }
                    LocalTypeR::Mu { body, .. } => has_nested_action(body, depth),
                }
            }

            // The generated protocols have nested communications, so projections should too
            assert!(
                has_nested_action(&local, 0),
                "Role {} projection should have nested actions for {:?}, got {:?}",
                role,
                global,
                local
            );
        }
    }
}

// ============================================================================
// Lean validation tests (require Lean binary)
// ============================================================================

#[test]
fn test_rust_projection_matches_lean_simple() {
    skip_without_lean!();

    let mut runner = TestRunner::new_with_rng(
        Config::default(),
        TestRng::from_seed(RngAlgorithm::ChaCha, &DETERMINISTIC_SEED),
    );

    let lean_runner = LeanRunner::new().expect("Lean binary should exist");
    let strategy = simple_global_strategy();

    for i in 0..20 {
        let global = strategy
            .new_tree(&mut runner)
            .expect("Should generate value")
            .current();

        // Skip End type as it has no roles
        if matches!(global, GlobalType::End) {
            continue;
        }

        let choreo_json = global_to_choreography_json(&global);
        let roles = global.roles();

        for role in &roles {
            let local = project(&global, role).expect("Rust projection should succeed");
            let program_json = local_to_program_json(role, &local);

            let result = lean_runner
                .validate(&choreo_json, &program_json)
                .unwrap_or_else(|e| panic!("Lean validation call failed for case {}: {:?}", i, e));

            assert!(
                result.success,
                "Case {}: Rust projection for {} should match Lean. Global: {:?}, Local: {:?}, Result: {:?}",
                i, role, global, local, result
            );
        }
    }
}

#[test]
fn test_rust_projection_matches_lean_choice() {
    skip_without_lean!();

    let mut runner = TestRunner::new_with_rng(
        Config::default(),
        TestRng::from_seed(RngAlgorithm::ChaCha, &DETERMINISTIC_SEED),
    );

    let lean_runner = LeanRunner::new().expect("Lean binary should exist");

    // Generate choice protocols
    let strategy = (
        role_strategy(),
        role_strategy(),
        label_strategy(),
        label_strategy(),
    )
        .prop_filter("valid choice", |(s, r, l1, l2)| {
            s != r && l1.name != l2.name
        })
        .prop_map(|(s, r, l1, l2)| {
            GlobalType::comm(&s, &r, vec![(l1, GlobalType::End), (l2, GlobalType::End)])
        });

    for i in 0..20 {
        let global = strategy
            .new_tree(&mut runner)
            .expect("Should generate value")
            .current();

        let choreo_json = global_to_choreography_json(&global);
        let roles = global.roles();

        for role in &roles {
            let local = project(&global, role).expect("Rust projection should succeed");
            let program_json = local_to_program_json(role, &local);

            let result = lean_runner
                .validate(&choreo_json, &program_json)
                .unwrap_or_else(|e| panic!("Lean validation call failed for case {}: {:?}", i, e));

            assert!(
                result.success,
                "Case {}: Choice projection for {} should match Lean. Global: {:?}, Local: {:?}, Result: {:?}",
                i, role, global, local, result
            );
        }
    }
}

/// This test specifically validates that the choice continuation bug is fixed
/// by checking against Lean's verified implementation.
#[test]
fn test_choice_continuation_bug_fix_against_lean() {
    skip_without_lean!();

    let lean_runner = LeanRunner::new().expect("Lean binary should exist");

    // The exact pattern that was buggy:
    // Client -> Server: { success -> Server -> Client: AuthToken. end,
    //                     failure -> Server -> Client: AuthError. end }
    let global = GlobalType::comm(
        "Client",
        "Server",
        vec![
            (
                Label::new("success"),
                GlobalType::comm(
                    "Server",
                    "Client",
                    vec![(Label::new("AuthToken"), GlobalType::End)],
                ),
            ),
            (
                Label::new("failure"),
                GlobalType::comm(
                    "Server",
                    "Client",
                    vec![(Label::new("AuthError"), GlobalType::End)],
                ),
            ),
        ],
    );

    let choreo_json = global_to_choreography_json(&global);

    // Test Client projection
    let client_local = project(&global, "Client").expect("Client projection should succeed");

    // Verify the structure: Client sends choice, then receives response
    match &client_local {
        LocalTypeR::Send { partner, branches } => {
            assert_eq!(partner, "Server");
            assert_eq!(branches.len(), 2);

            for (label, _vt, cont) in branches {
                // Each branch should have a Recv continuation, not End
                match cont {
                    LocalTypeR::Recv {
                        partner: recv_partner,
                        branches: recv_branches,
                    } => {
                        assert_eq!(recv_partner, "Server");
                        assert_eq!(recv_branches.len(), 1);
                        let expected_label = if label.name == "success" {
                            "AuthToken"
                        } else {
                            "AuthError"
                        };
                        assert_eq!(recv_branches[0].0.name, expected_label);
                    }
                    LocalTypeR::End => {
                        panic!(
                            "BUG DETECTED: Branch {} has End instead of Recv. This was the original bug.",
                            label.name
                        );
                    }
                    other => panic!(
                        "Unexpected continuation for branch {}: {:?}",
                        label.name, other
                    ),
                }
            }
        }
        _ => panic!("Client should see Send, got {:?}", client_local),
    }

    // Test Server projection
    let server_local = project(&global, "Server").expect("Server projection should succeed");

    // Verify the structure: Server receives choice, then sends response
    match &server_local {
        LocalTypeR::Recv { partner, branches } => {
            assert_eq!(partner, "Client");
            assert_eq!(branches.len(), 2);

            for (label, _vt, cont) in branches {
                // Each branch should have a Send continuation, not End
                match cont {
                    LocalTypeR::Send {
                        partner: send_partner,
                        branches: send_branches,
                    } => {
                        assert_eq!(send_partner, "Client");
                        assert_eq!(send_branches.len(), 1);
                        let expected_label = if label.name == "success" {
                            "AuthToken"
                        } else {
                            "AuthError"
                        };
                        assert_eq!(send_branches[0].0.name, expected_label);
                    }
                    LocalTypeR::End => {
                        panic!(
                            "BUG DETECTED: Branch {} has End instead of Send. This was the original bug.",
                            label.name
                        );
                    }
                    other => panic!(
                        "Unexpected continuation for branch {}: {:?}",
                        label.name, other
                    ),
                }
            }
        }
        _ => panic!("Server should see Recv, got {:?}", server_local),
    }

    // Validate against Lean for both roles
    for role in ["Client", "Server"] {
        let local = project(&global, role).expect("Projection should succeed");
        let program_json = local_to_program_json(role, &local);

        let result = lean_runner
            .validate(&choreo_json, &program_json)
            .expect("Lean validation should not crash");

        assert!(
            result.success,
            "{} projection should match Lean. Local: {:?}, Result: {:?}",
            role, local, result
        );
    }
}

// ============================================================================
// Extended coverage tests (multi-branch, deep nesting, non-participant)
// ============================================================================

/// Strategy for generating multi-way choices (3-5 branches).
fn multiway_choice_strategy() -> impl Strategy<Value = GlobalType> {
    (
        role_strategy(),
        role_strategy(),
        prop::collection::vec(label_strategy(), 3..=5),
    )
        .prop_filter("valid multiway choice", |(s, r, labels)| {
            s != r && {
                let names: std::collections::HashSet<_> =
                    labels.iter().map(|l| l.name.as_str()).collect();
                names.len() == labels.len() // all distinct
            }
        })
        .prop_map(|(s, r, labels)| {
            let branches: Vec<_> = labels.into_iter().map(|l| (l, GlobalType::End)).collect();
            GlobalType::comm(&s, &r, branches)
        })
}

/// Strategy for generating deeply nested protocols (4-6 levels).
fn deep_nesting_strategy() -> impl Strategy<Value = GlobalType> {
    (
        role_strategy(),
        role_strategy(),
        prop::collection::vec(label_strategy(), 4..=6),
    )
        .prop_filter("sender != receiver", |(s, r, _)| s != r)
        .prop_map(|(s, r, labels)| {
            // Build nested Send: s -> r: l1. s -> r: l2. ... s -> r: ln. end
            let mut current = GlobalType::End;
            for label in labels.into_iter().rev() {
                current = GlobalType::comm(&s, &r, vec![(label, current)]);
            }
            current
        })
}

/// Strategy for three-party protocols where one party is a non-participant in some communications.
fn three_party_nonparticipant_strategy() -> impl Strategy<Value = GlobalType> {
    (label_strategy(), label_strategy(), label_strategy())
        .prop_filter("distinct labels", |(l1, l2, l3)| {
            l1.name != l2.name && l2.name != l3.name && l1.name != l3.name
        })
        .prop_map(|(l1, l2, l3)| {
            // Alice -> Bob: l1. Bob -> Carol: l2. Carol -> Alice: l3. end
            GlobalType::comm(
                "Alice",
                "Bob",
                vec![(
                    l1,
                    GlobalType::comm(
                        "Bob",
                        "Carol",
                        vec![(
                            l2,
                            GlobalType::comm("Carol", "Alice", vec![(l3, GlobalType::End)]),
                        )],
                    ),
                )],
            )
        })
}

/// Strategy for choice where a third party is a non-participant.
fn choice_with_nonparticipant_strategy() -> impl Strategy<Value = GlobalType> {
    (label_strategy(), label_strategy(), label_strategy())
        .prop_filter("distinct labels", |(l1, l2, notify)| {
            l1.name != l2.name && l1.name != notify.name && l2.name != notify.name
        })
        .prop_map(|(l1, l2, notify)| {
            // Alice -> Bob: { l1 -> Bob -> Carol: notify. end,
            //                 l2 -> Bob -> Carol: notify. end }
            // Carol sees same action in both branches (mergeable)
            let cont = GlobalType::comm("Bob", "Carol", vec![(notify.clone(), GlobalType::End)]);
            GlobalType::comm("Alice", "Bob", vec![(l1, cont.clone()), (l2, cont)])
        })
}

#[test]
fn test_multiway_choice_projections() {
    let mut runner = TestRunner::new_with_rng(
        Config::default(),
        TestRng::from_seed(RngAlgorithm::ChaCha, &DETERMINISTIC_SEED),
    );

    let strategy = multiway_choice_strategy();

    for _ in 0..30 {
        let global = strategy
            .new_tree(&mut runner)
            .expect("Should generate value")
            .current();

        let roles = global.roles();
        for role in &roles {
            let local = project(&global, role);
            assert!(
                local.is_ok(),
                "Projection should succeed for multiway choice. Role: {}, Global: {:?}",
                role,
                global
            );

            // Verify branch count
            let local = local.unwrap();
            match &local {
                LocalTypeR::Send { branches, .. } | LocalTypeR::Recv { branches, .. } => {
                    // Multi-way choice should have 3-5 branches
                    assert!(
                        branches.len() >= 3,
                        "Multi-way choice should have at least 3 branches, got {}",
                        branches.len()
                    );
                }
                _ => {}
            }
        }
    }
}

#[test]
fn test_deep_nesting_projections() {
    let mut runner = TestRunner::new_with_rng(
        Config::default(),
        TestRng::from_seed(RngAlgorithm::ChaCha, &DETERMINISTIC_SEED),
    );

    let strategy = deep_nesting_strategy();

    for _ in 0..30 {
        let global = strategy
            .new_tree(&mut runner)
            .expect("Should generate value")
            .current();

        let roles = global.roles();
        for role in &roles {
            let local = project(&global, role);
            assert!(
                local.is_ok(),
                "Projection should succeed for deep nesting. Role: {}, Global: {:?}",
                role,
                global
            );

            // Verify nesting depth
            fn count_depth(lt: &LocalTypeR) -> usize {
                match lt {
                    LocalTypeR::End | LocalTypeR::Var(_) => 0,
                    LocalTypeR::Send { branches, .. } | LocalTypeR::Recv { branches, .. } => {
                        1 + branches
                            .iter()
                            .map(|(_, _vt, c)| count_depth(c))
                            .max()
                            .unwrap_or(0)
                    }
                    LocalTypeR::Mu { body, .. } => count_depth(body),
                }
            }

            let local = local.unwrap();
            let depth = count_depth(&local);
            assert!(
                depth >= 4,
                "Deep nesting should have at least 4 levels, got {}",
                depth
            );
        }
    }
}

#[test]
fn test_three_party_nonparticipant_projections() {
    let mut runner = TestRunner::new_with_rng(
        Config::default(),
        TestRng::from_seed(RngAlgorithm::ChaCha, &DETERMINISTIC_SEED),
    );

    let strategy = three_party_nonparticipant_strategy();

    for _ in 0..30 {
        let global = strategy
            .new_tree(&mut runner)
            .expect("Should generate value")
            .current();

        // All three roles should project successfully
        for role in ["Alice", "Bob", "Carol"] {
            let local = project(&global, role);
            assert!(
                local.is_ok(),
                "Three-party projection should succeed for role {}. Global: {:?}",
                role,
                global
            );
        }

        // Bob is in the middle: should see recv then send
        let bob_local = project(&global, "Bob").unwrap();
        assert!(
            matches!(&bob_local, LocalTypeR::Recv { partner: p, .. } if p == "Alice"),
            "Bob should first receive from Alice, got {:?}",
            bob_local
        );
    }
}

#[test]
fn test_choice_nonparticipant_merge() {
    let mut runner = TestRunner::new_with_rng(
        Config::default(),
        TestRng::from_seed(RngAlgorithm::ChaCha, &DETERMINISTIC_SEED),
    );

    let strategy = choice_with_nonparticipant_strategy();

    for _ in 0..30 {
        let global = strategy
            .new_tree(&mut runner)
            .expect("Should generate value")
            .current();

        // All three roles should project successfully
        for role in ["Alice", "Bob", "Carol"] {
            let local = project(&global, role);
            assert!(
                local.is_ok(),
                "Choice with non-participant should project for role {}. Global: {:?}, Error: {:?}",
                role,
                global,
                local.err()
            );
        }

        // Carol is non-participant in choice, should see merged behavior (single recv from Bob)
        let carol_local = project(&global, "Carol").unwrap();
        assert!(
            matches!(&carol_local, LocalTypeR::Recv { partner: p, .. } if p == "Bob"),
            "Carol should receive from Bob, got {:?}",
            carol_local
        );
    }
}

#[test]
fn test_multiway_choice_against_lean() {
    skip_without_lean!();

    let mut runner = TestRunner::new_with_rng(
        Config::default(),
        TestRng::from_seed(RngAlgorithm::ChaCha, &DETERMINISTIC_SEED),
    );

    let lean_runner = LeanRunner::new().expect("Lean binary should exist");
    let strategy = multiway_choice_strategy();

    for i in 0..15 {
        let global = strategy
            .new_tree(&mut runner)
            .expect("Should generate value")
            .current();

        let choreo_json = global_to_choreography_json(&global);
        let roles = global.roles();

        for role in &roles {
            let local = project(&global, role).expect("Rust projection should succeed");
            let program_json = local_to_program_json(role, &local);

            let result = lean_runner
                .validate(&choreo_json, &program_json)
                .unwrap_or_else(|e| panic!("Lean validation failed for case {}: {:?}", i, e));

            assert!(
                result.success,
                "Case {}: Multiway choice projection for {} should match Lean. Global: {:?}",
                i, role, global
            );
        }
    }
}

#[test]
fn test_deep_nesting_against_lean() {
    skip_without_lean!();

    let mut runner = TestRunner::new_with_rng(
        Config::default(),
        TestRng::from_seed(RngAlgorithm::ChaCha, &DETERMINISTIC_SEED),
    );

    let lean_runner = LeanRunner::new().expect("Lean binary should exist");
    let strategy = deep_nesting_strategy();

    for i in 0..15 {
        let global = strategy
            .new_tree(&mut runner)
            .expect("Should generate value")
            .current();

        let choreo_json = global_to_choreography_json(&global);
        let roles = global.roles();

        for role in &roles {
            let local = project(&global, role).expect("Rust projection should succeed");
            let program_json = local_to_program_json(role, &local);

            let result = lean_runner
                .validate(&choreo_json, &program_json)
                .unwrap_or_else(|e| panic!("Lean validation failed for case {}: {:?}", i, e));

            assert!(
                result.success,
                "Case {}: Deep nesting projection for {} should match Lean. Global: {:?}",
                i, role, global
            );
        }
    }
}

// ============================================================================
// JSON export consistency tests
// ============================================================================

#[test]
fn test_projection_json_export_consistency() {
    let mut runner = TestRunner::new_with_rng(
        Config::default(),
        TestRng::from_seed(RngAlgorithm::ChaCha, &DETERMINISTIC_SEED),
    );

    let strategy = simple_global_strategy();

    for _ in 0..50 {
        let global = strategy
            .new_tree(&mut runner)
            .expect("Should generate value")
            .current();

        // Skip End type
        if matches!(global, GlobalType::End) {
            continue;
        }

        // Export to JSON and verify structure
        let global_json = global_to_json(&global);
        assert!(
            global_json.get("kind").is_some(),
            "Global JSON should have 'kind' field"
        );

        for role in global.roles() {
            let local = project(&global, &role).expect("Projection should succeed");
            let local_json = local_to_json(&local);

            assert!(
                local_json.get("kind").is_some(),
                "Local JSON should have 'kind' field"
            );
        }
    }
}

#[test]
fn test_project_all_consistency() {
    let mut runner = TestRunner::new_with_rng(
        Config::default(),
        TestRng::from_seed(RngAlgorithm::ChaCha, &DETERMINISTIC_SEED),
    );

    let strategy = simple_global_strategy();

    for _ in 0..30 {
        let global = strategy
            .new_tree(&mut runner)
            .expect("Should generate value")
            .current();

        // project_all should return same results as individual projections
        let all_projections = project_all(&global).expect("project_all should succeed");

        for (role, local) in all_projections {
            let individual = project(&global, &role).expect("Individual projection should succeed");
            assert_eq!(
                local, individual,
                "project_all and project should return same result for role {}",
                role
            );
        }
    }
}
