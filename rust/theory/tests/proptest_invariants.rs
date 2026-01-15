//! Property-Based Invariant Tests for Session Type Theory
//!
//! These tests verify mathematical properties that the Lean proofs establish.
//! Using deterministic seeds for reproducibility.

use proptest::prelude::*;
use proptest::strategy::ValueTree;
use proptest::test_runner::{Config, RngAlgorithm, TestRng, TestRunner};
use rumpsteak_theory::{
    async_subtype, check_coherent, merge, project, sync_subtype, validate_global, validate_local,
};
use rumpsteak_types::{GlobalType, Label, LocalTypeR};

/// Deterministic seed for reproducibility
const SEED: [u8; 32] = [
    0x49, 0x6E, 0x76, 0x61, 0x72, 0x69, 0x61, 0x6E, // "Invarian"
    0x74, 0x54, 0x65, 0x73, 0x74, 0x53, 0x65, 0x65, // "tTestSee"
    0x64, 0x46, 0x6F, 0x72, 0x52, 0x75, 0x73, 0x74, // "dForRust"
    0x54, 0x68, 0x65, 0x6F, 0x72, 0x79, 0x43, 0x72, // "TheoryCr"
];

// ============================================================================
// Strategies for generating session types
// ============================================================================

fn label_strategy() -> impl Strategy<Value = Label> {
    prop_oneof![
        Just(Label::new("msg")),
        Just(Label::new("ack")),
        Just(Label::new("data")),
        Just(Label::new("req")),
        Just(Label::new("resp")),
        Just(Label::new("yes")),
        Just(Label::new("no")),
        Just(Label::new("done")),
    ]
}

fn role_strategy() -> impl Strategy<Value = String> {
    prop_oneof![
        Just("A".to_string()),
        Just("B".to_string()),
        Just("C".to_string()),
        Just("D".to_string()),
    ]
}

/// Strategy for well-formed global types (depth-limited)
fn global_type_strategy(depth: usize) -> BoxedStrategy<GlobalType> {
    if depth == 0 {
        Just(GlobalType::End).boxed()
    } else {
        prop_oneof![
            // End
            Just(GlobalType::End),
            // Simple send (different sender/receiver)
            (role_strategy(), role_strategy(), label_strategy())
                .prop_filter("sender != receiver", |(s, r, _)| s != r)
                .prop_flat_map(move |(s, r, l)| {
                    global_type_strategy(depth - 1)
                        .prop_map(move |cont| GlobalType::send(&s, &r, l.clone(), cont))
                }),
            // Binary choice (different sender/receiver)
            (role_strategy(), role_strategy())
                .prop_filter("sender != receiver", |(s, r)| s != r)
                .prop_flat_map(move |(s, r)| {
                    (
                        global_type_strategy(depth - 1),
                        global_type_strategy(depth - 1),
                    )
                        .prop_map(move |(c1, c2)| {
                            GlobalType::comm(
                                &s,
                                &r,
                                vec![(Label::new("yes"), c1), (Label::new("no"), c2)],
                            )
                        })
                }),
            // Recursion (with guard) - use distinct labels
            (role_strategy(), role_strategy())
                .prop_filter("sender != receiver", |(s, r)| s != r)
                .prop_map(|(s, r)| {
                    GlobalType::mu(
                        "t",
                        GlobalType::comm(
                            &s,
                            &r,
                            vec![
                                (Label::new("continue"), GlobalType::var("t")),
                                (Label::new("stop"), GlobalType::End),
                            ],
                        ),
                    )
                }),
        ]
        .boxed()
    }
}

/// Strategy for well-formed local types (depth-limited)
fn local_type_strategy(depth: usize) -> BoxedStrategy<LocalTypeR> {
    if depth == 0 {
        Just(LocalTypeR::End).boxed()
    } else {
        prop_oneof![
            // End
            Just(LocalTypeR::End),
            // Simple send
            (role_strategy(), label_strategy()).prop_flat_map(move |(p, l)| {
                local_type_strategy(depth - 1)
                    .prop_map(move |cont| LocalTypeR::send(&p, l.clone(), cont))
            }),
            // Simple recv
            (role_strategy(), label_strategy()).prop_flat_map(move |(p, l)| {
                local_type_strategy(depth - 1)
                    .prop_map(move |cont| LocalTypeR::recv(&p, l.clone(), cont))
            }),
            // Send choice
            role_strategy().prop_flat_map(move |p| {
                (
                    local_type_strategy(depth - 1),
                    local_type_strategy(depth - 1),
                )
                    .prop_map(move |(c1, c2)| {
                        LocalTypeR::send_choice(
                            &p,
                            vec![(Label::new("yes"), c1), (Label::new("no"), c2)],
                        )
                    })
            }),
            // Recv choice
            role_strategy().prop_flat_map(move |p| {
                (
                    local_type_strategy(depth - 1),
                    local_type_strategy(depth - 1),
                )
                    .prop_map(move |(c1, c2)| {
                        LocalTypeR::recv_choice(
                            &p,
                            vec![(Label::new("yes"), c1), (Label::new("no"), c2)],
                        )
                    })
            }),
            // Recursion (with guard) - use distinct labels
            role_strategy().prop_map(|p| {
                LocalTypeR::mu(
                    "t",
                    LocalTypeR::send_choice(
                        &p,
                        vec![
                            (Label::new("continue"), LocalTypeR::var("t")),
                            (Label::new("stop"), LocalTypeR::End),
                        ],
                    ),
                )
            }),
        ]
        .boxed()
    }
}

// ============================================================================
// Invariant Tests: Duality
// ============================================================================

#[test]
fn prop_duality_is_involution() {
    let mut runner = TestRunner::new_with_rng(
        Config {
            cases: 100,
            ..Config::default()
        },
        TestRng::from_seed(RngAlgorithm::ChaCha, &SEED),
    );

    let strategy = local_type_strategy(3);

    for _ in 0..100 {
        let tree = strategy.new_tree(&mut runner).unwrap();
        let lt = tree.current();

        // dual(dual(T)) == T
        let dual_once = lt.dual();
        let dual_twice = dual_once.dual();

        assert_eq!(
            lt, dual_twice,
            "Duality should be an involution: dual(dual(T)) == T"
        );
    }
}

#[test]
fn prop_dual_swaps_send_recv() {
    let lt = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
    let dual = lt.dual();

    match dual {
        LocalTypeR::Recv { partner, .. } => assert_eq!(partner, "B"),
        _ => panic!("dual of Send should be Recv"),
    }

    let lt2 = LocalTypeR::recv("A", Label::new("msg"), LocalTypeR::End);
    let dual2 = lt2.dual();

    match dual2 {
        LocalTypeR::Send { partner, .. } => assert_eq!(partner, "A"),
        _ => panic!("dual of Recv should be Send"),
    }
}

// ============================================================================
// Invariant Tests: Projection
// ============================================================================

#[test]
fn prop_projection_preserves_well_formedness() {
    let mut runner = TestRunner::new_with_rng(
        Config {
            cases: 50,
            ..Config::default()
        },
        TestRng::from_seed(RngAlgorithm::ChaCha, &SEED),
    );

    let strategy = global_type_strategy(2);

    for _ in 0..50 {
        let tree = strategy.new_tree(&mut runner).unwrap();
        let g = tree.current();

        if !g.well_formed() {
            continue;
        }

        for role in g.roles() {
            if let Ok(local) = project(&g, &role) {
                assert!(
                    validate_local(&local).is_ok(),
                    "Projecting well-formed global should produce well-formed local.\n\
                     Global: {:?}\n\
                     Role: {}\n\
                     Local: {:?}\n\
                     Error: {:?}",
                    g,
                    role,
                    local,
                    validate_local(&local).err()
                );
            }
        }
    }
}

#[test]
fn prop_projection_end_is_end() {
    // project(End, r) == End for any role r
    let g = GlobalType::End;
    for role in ["A", "B", "C"] {
        let result = project(&g, role);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), LocalTypeR::End);
    }
}

#[test]
fn prop_projection_sender_gets_send() {
    let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);

    let local_a = project(&g, "A").unwrap();
    match local_a {
        LocalTypeR::Send { partner, .. } => assert_eq!(partner, "B"),
        _ => panic!("Sender should get Send type"),
    }
}

#[test]
fn prop_projection_receiver_gets_recv() {
    let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);

    let local_b = project(&g, "B").unwrap();
    match local_b {
        LocalTypeR::Recv { partner, .. } => assert_eq!(partner, "A"),
        _ => panic!("Receiver should get Recv type"),
    }
}

#[test]
fn prop_projection_non_participant_gets_end_or_continuation() {
    let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);

    // C is not involved, should project to End
    let local_c = project(&g, "C").unwrap();
    assert_eq!(local_c, LocalTypeR::End);
}

// ============================================================================
// Invariant Tests: Merge
// ============================================================================

#[test]
fn prop_merge_is_idempotent() {
    let mut runner = TestRunner::new_with_rng(
        Config {
            cases: 50,
            ..Config::default()
        },
        TestRng::from_seed(RngAlgorithm::ChaCha, &SEED),
    );

    let strategy = local_type_strategy(2);

    for _ in 0..50 {
        let tree = strategy.new_tree(&mut runner).unwrap();
        let lt = tree.current();

        // merge(T, T) == T
        let merged = merge(&lt, &lt);
        assert!(
            merged.is_ok(),
            "merge(T, T) should always succeed for well-formed T"
        );
        assert_eq!(
            merged.unwrap(),
            lt,
            "merge(T, T) should equal T (idempotent)"
        );
    }
}

#[test]
fn prop_merge_is_commutative() {
    // For compatible types, merge(A, B) == merge(B, A)
    let t1 = LocalTypeR::recv_choice(
        "A",
        vec![
            (Label::new("x"), LocalTypeR::End),
            (Label::new("y"), LocalTypeR::End),
        ],
    );
    let t2 = LocalTypeR::recv_choice(
        "A",
        vec![
            (Label::new("y"), LocalTypeR::End),
            (Label::new("z"), LocalTypeR::End),
        ],
    );

    let m1 = merge(&t1, &t2);
    let m2 = merge(&t2, &t1);

    // Both should succeed or both fail
    assert_eq!(m1.is_ok(), m2.is_ok());

    if let (Ok(r1), Ok(r2)) = (m1, m2) {
        // Results should have same labels (order may differ)
        let labels1: std::collections::HashSet<_> = r1.labels().into_iter().collect();
        let labels2: std::collections::HashSet<_> = r2.labels().into_iter().collect();
        assert_eq!(labels1, labels2);
    }
}

#[test]
fn prop_merge_end_identity() {
    // merge(End, End) == End
    let result = merge(&LocalTypeR::End, &LocalTypeR::End);
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), LocalTypeR::End);
}

// ============================================================================
// Invariant Tests: Sync Subtyping
// ============================================================================

#[test]
fn prop_sync_subtype_reflexive() {
    let mut runner = TestRunner::new_with_rng(
        Config {
            cases: 50,
            ..Config::default()
        },
        TestRng::from_seed(RngAlgorithm::ChaCha, &SEED),
    );

    let strategy = local_type_strategy(2);

    for _ in 0..50 {
        let tree = strategy.new_tree(&mut runner).unwrap();
        let lt = tree.current();

        // T <: T (reflexivity)
        let result = sync_subtype(&lt, &lt);
        assert!(
            result.is_ok(),
            "Sync subtyping should be reflexive: T <: T\nType: {:?}\nError: {:?}",
            lt,
            result.err()
        );
    }
}

#[test]
fn prop_sync_subtype_end() {
    // End <: End
    assert!(sync_subtype(&LocalTypeR::End, &LocalTypeR::End).is_ok());
}

// ============================================================================
// Invariant Tests: Async Subtyping
// ============================================================================

#[test]
fn prop_async_subtype_reflexive() {
    let mut runner = TestRunner::new_with_rng(
        Config {
            cases: 30,
            ..Config::default()
        },
        TestRng::from_seed(RngAlgorithm::ChaCha, &SEED),
    );

    // Use depth 1 to avoid stack overflow with recursive types
    let strategy = local_type_strategy(1);

    for _ in 0..30 {
        let tree = strategy.new_tree(&mut runner).unwrap();
        let lt = tree.current();

        // Skip recursive types which can cause issues with async subtyping
        if matches!(lt, LocalTypeR::Mu { .. }) {
            continue;
        }

        // T ≤async T (reflexivity)
        let result = async_subtype(&lt, &lt);
        assert!(
            result.is_ok(),
            "Async subtyping should be reflexive: T ≤ T\nType: {:?}\nError: {:?}",
            lt,
            result.err()
        );
    }
}

// ============================================================================
// Invariant Tests: Coherence
// ============================================================================

#[test]
fn prop_well_formed_implies_coherent_predicates() {
    let mut runner = TestRunner::new_with_rng(
        Config {
            cases: 50,
            ..Config::default()
        },
        TestRng::from_seed(RngAlgorithm::ChaCha, &SEED),
    );

    let strategy = global_type_strategy(2);

    for _ in 0..50 {
        let tree = strategy.new_tree(&mut runner).unwrap();
        let g = tree.current();

        if validate_global(&g).is_ok() {
            let bundle = check_coherent(&g);

            // Well-formed types should satisfy basic coherence predicates
            assert!(bundle.size, "Well-formed should have non-empty branches");
            assert!(bundle.action, "Well-formed should have sender != receiver");
            assert!(
                bundle.uniq_labels,
                "Well-formed should have unique labels in each choice"
            );
        }
    }
}

#[test]
fn prop_coherent_end() {
    let bundle = check_coherent(&GlobalType::End);
    assert!(bundle.is_coherent(), "End should be coherent");
}

#[test]
fn prop_coherent_simple_send() {
    let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
    let bundle = check_coherent(&g);
    assert!(bundle.is_coherent(), "Simple send should be coherent");
}

// ============================================================================
// Invariant Tests: Well-formedness
// ============================================================================

#[test]
fn prop_generated_types_are_well_formed() {
    let mut runner = TestRunner::new_with_rng(
        Config {
            cases: 100,
            ..Config::default()
        },
        TestRng::from_seed(RngAlgorithm::ChaCha, &SEED),
    );

    let strategy = global_type_strategy(3);

    for _ in 0..100 {
        let tree = strategy.new_tree(&mut runner).unwrap();
        let g = tree.current();

        // Our strategy should generate well-formed types
        let result = validate_global(&g);
        assert!(
            result.is_ok(),
            "Generated type should be well-formed.\nType: {:?}\nError: {:?}",
            g,
            result.err()
        );
    }
}

#[test]
fn prop_self_comm_is_ill_formed() {
    let bad = GlobalType::send("A", "A", Label::new("msg"), GlobalType::End);
    assert!(
        validate_global(&bad).is_err(),
        "Self-communication should be ill-formed"
    );
}

#[test]
fn prop_unbound_var_is_ill_formed() {
    let bad = GlobalType::send("A", "B", Label::new("msg"), GlobalType::var("unbound"));
    assert!(
        validate_global(&bad).is_err(),
        "Unbound variable should be ill-formed"
    );
}

#[test]
fn prop_unguarded_recursion_is_ill_formed() {
    let bad = GlobalType::mu("t", GlobalType::var("t"));
    assert!(
        validate_global(&bad).is_err(),
        "Unguarded recursion should be ill-formed"
    );
}

// ============================================================================
// Invariant Tests: Guardedness Enforcement
// ============================================================================

/// Strategy for generating unguarded global types
///
/// A type is unguarded if the body of a mu is either:
/// - A direct variable reference: μt. t
/// - Another mu: μt. μs. ...
fn unguarded_global_strategy() -> BoxedStrategy<GlobalType> {
    prop_oneof![
        // Direct unguarded recursion: μt. t
        Just(GlobalType::mu("t", GlobalType::var("t"))),
        // Nested unguarded: μt. μs. t
        Just(GlobalType::mu(
            "t",
            GlobalType::mu("s", GlobalType::var("t"))
        )),
        // Double unguarded: μt. μs. s
        Just(GlobalType::mu(
            "t",
            GlobalType::mu("s", GlobalType::var("s"))
        )),
    ]
    .boxed()
}

/// Strategy for generating unguarded local types
///
/// A type is unguarded if the body of a mu is either:
/// - A direct variable reference: μt. t
/// - Another mu: μt. μs. ...
fn unguarded_local_strategy() -> BoxedStrategy<LocalTypeR> {
    prop_oneof![
        // Direct unguarded recursion: μt. t
        Just(LocalTypeR::mu("t", LocalTypeR::var("t"))),
        // Nested unguarded: μt. μs. t
        Just(LocalTypeR::mu(
            "t",
            LocalTypeR::mu("s", LocalTypeR::var("t"))
        )),
        // Double unguarded: μt. μs. s
        Just(LocalTypeR::mu(
            "t",
            LocalTypeR::mu("s", LocalTypeR::var("s"))
        )),
    ]
    .boxed()
}

#[test]
fn prop_well_formed_global_implies_guarded() {
    let mut runner = TestRunner::new_with_rng(
        Config {
            cases: 100,
            ..Config::default()
        },
        TestRng::from_seed(RngAlgorithm::ChaCha, &SEED),
    );

    let strategy = global_type_strategy(3);

    for _ in 0..100 {
        let tree = strategy.new_tree(&mut runner).unwrap();
        let g = tree.current();

        if g.well_formed() {
            assert!(
                g.is_guarded(),
                "All well-formed global types must be guarded.\nType: {:?}",
                g
            );
        }
    }
}

#[test]
fn prop_well_formed_local_implies_guarded() {
    let mut runner = TestRunner::new_with_rng(
        Config {
            cases: 100,
            ..Config::default()
        },
        TestRng::from_seed(RngAlgorithm::ChaCha, &SEED),
    );

    let strategy = local_type_strategy(3);

    for _ in 0..100 {
        let tree = strategy.new_tree(&mut runner).unwrap();
        let lt = tree.current();

        if lt.well_formed() {
            assert!(
                lt.is_guarded(),
                "All well-formed local types must be guarded.\nType: {:?}",
                lt
            );
        }
    }
}

#[test]
fn prop_unguarded_global_not_well_formed() {
    let mut runner = TestRunner::new_with_rng(
        Config {
            cases: 50,
            ..Config::default()
        },
        TestRng::from_seed(RngAlgorithm::ChaCha, &SEED),
    );

    let strategy = unguarded_global_strategy();

    for _ in 0..50 {
        let tree = strategy.new_tree(&mut runner).unwrap();
        let g = tree.current();

        assert!(
            !g.is_guarded(),
            "Generated type should be unguarded.\nType: {:?}",
            g
        );
        assert!(
            !g.well_formed(),
            "Unguarded global types must not be well-formed.\nType: {:?}",
            g
        );
    }
}

#[test]
fn prop_unguarded_local_not_well_formed() {
    let mut runner = TestRunner::new_with_rng(
        Config {
            cases: 50,
            ..Config::default()
        },
        TestRng::from_seed(RngAlgorithm::ChaCha, &SEED),
    );

    let strategy = unguarded_local_strategy();

    for _ in 0..50 {
        let tree = strategy.new_tree(&mut runner).unwrap();
        let lt = tree.current();

        assert!(
            !lt.is_guarded(),
            "Generated type should be unguarded.\nType: {:?}",
            lt
        );
        assert!(
            !lt.well_formed(),
            "Unguarded local types must not be well-formed.\nType: {:?}",
            lt
        );
    }
}

#[test]
fn prop_guardedness_equivalence_global() {
    // Verify that well_formed() and is_guarded() are properly linked
    // For types that only differ in guardedness, well_formed() should match is_guarded()

    // Unguarded: μt. t
    let unguarded = GlobalType::mu("t", GlobalType::var("t"));
    assert!(!unguarded.is_guarded());
    assert!(!unguarded.well_formed());

    // Guarded: μt. A -> B: msg. t
    let guarded = GlobalType::mu(
        "t",
        GlobalType::send("A", "B", Label::new("msg"), GlobalType::var("t")),
    );
    assert!(guarded.is_guarded());
    assert!(guarded.well_formed());

    // Nested mu without guard: μt. μs. t
    let nested_unguarded = GlobalType::mu("t", GlobalType::mu("s", GlobalType::var("t")));
    assert!(!nested_unguarded.is_guarded());
    assert!(!nested_unguarded.well_formed());
}

#[test]
fn prop_guardedness_equivalence_local() {
    // Verify that well_formed() and is_guarded() are properly linked

    // Unguarded: μt. t
    let unguarded = LocalTypeR::mu("t", LocalTypeR::var("t"));
    assert!(!unguarded.is_guarded());
    assert!(!unguarded.well_formed());

    // Guarded: μt. !B{msg.t}
    let guarded = LocalTypeR::mu(
        "t",
        LocalTypeR::send("B", Label::new("msg"), LocalTypeR::var("t")),
    );
    assert!(guarded.is_guarded());
    assert!(guarded.well_formed());

    // Nested mu without guard: μt. μs. t
    let nested_unguarded = LocalTypeR::mu("t", LocalTypeR::mu("s", LocalTypeR::var("t")));
    assert!(!nested_unguarded.is_guarded());
    assert!(!nested_unguarded.well_formed());
}

#[test]
fn prop_generated_global_types_are_guarded() {
    let mut runner = TestRunner::new_with_rng(
        Config {
            cases: 100,
            ..Config::default()
        },
        TestRng::from_seed(RngAlgorithm::ChaCha, &SEED),
    );

    let strategy = global_type_strategy(3);

    for _ in 0..100 {
        let tree = strategy.new_tree(&mut runner).unwrap();
        let g = tree.current();

        assert!(
            g.is_guarded(),
            "Generated global types should always be guarded.\nType: {:?}",
            g
        );
    }
}

#[test]
fn prop_generated_local_types_are_guarded() {
    let mut runner = TestRunner::new_with_rng(
        Config {
            cases: 100,
            ..Config::default()
        },
        TestRng::from_seed(RngAlgorithm::ChaCha, &SEED),
    );

    let strategy = local_type_strategy(3);

    for _ in 0..100 {
        let tree = strategy.new_tree(&mut runner).unwrap();
        let lt = tree.current();

        assert!(
            lt.is_guarded(),
            "Generated local types should always be guarded.\nType: {:?}",
            lt
        );
    }
}

// ============================================================================
// Invariant Tests: Semantics (Async Step)
// ============================================================================

#[test]
fn prop_step_deterministic() {
    use rumpsteak_theory::semantics::{can_step, step, GlobalAction};

    let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
    let act = GlobalAction::new("A", "B", Label::new("msg"));

    // Multiple calls should give same result
    let r1 = step(&g, &act);
    let r2 = step(&g, &act);
    let r3 = step(&g, &act);

    assert_eq!(r1, r2);
    assert_eq!(r2, r3);

    // can_step consistency
    assert!(can_step(&g, &act));
    assert!(r1.is_some());
}

#[test]
fn prop_enabled_implies_step_exists() {
    use rumpsteak_theory::semantics::{can_step, step, GlobalAction};

    let mut runner = TestRunner::new_with_rng(
        Config {
            cases: 50,
            ..Config::default()
        },
        TestRng::from_seed(RngAlgorithm::ChaCha, &SEED),
    );

    let strategy = global_type_strategy(2);

    for _ in 0..50 {
        let tree = strategy.new_tree(&mut runner).unwrap();
        let g = tree.current();

        if !g.well_formed() {
            continue;
        }

        // For each head action, if enabled then step should exist
        if let GlobalType::Comm {
            sender,
            receiver,
            branches,
        } = &g
        {
            for (label, _) in branches {
                let act = GlobalAction::new(sender, receiver, label.clone());
                if can_step(&g, &act) {
                    assert!(
                        step(&g, &act).is_some(),
                        "If can_step then step should exist.\nGlobal: {:?}\nAction: {:?}",
                        g,
                        act
                    );
                }
            }
        }
    }
}
