//! Semantics Verification Tests
//!
//! Tests that verify the Rust async step semantics implementation matches
//! the formal Lean specification from ECOOP 2025.
//!
//! These tests cover:
//! - `can_step`: Async enabledness predicate
//! - `step`: Async step relation
//! - `local_can_step` / `local_step`: Local type semantics
//! - `consume_with_proof`: Consumption with proof structure
//! - `reduces` / `reduces_star`: Reduction relations

#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

use proptest::prelude::*;
use proptest::strategy::ValueTree;
use proptest::test_runner::{Config, RngAlgorithm, TestRng, TestRunner};
use telltale_theory::semantics::{
    can_step, consume_with_proof, good_g, local_can_step, local_step, reduces, reduces_star, step,
    GlobalAction, LocalAction,
};
use telltale_types::{GlobalType, Label, LocalTypeR};

/// Deterministic seed for property-based tests.
const DETERMINISTIC_SEED: [u8; 32] = [
    0x53, 0x65, 0x6D, 0x61, 0x6E, 0x74, 0x69, 0x63, // "Semantic"
    0x73, 0x54, 0x65, 0x73, 0x74, 0x53, 0x65, 0x65, // "sTestSee"
    0x64, 0x46, 0x6F, 0x72, 0x56, 0x65, 0x72, 0x69, // "dForVeri"
    0x66, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, // "fication"
];

// ============================================================================
// Strategies for generating test data
// ============================================================================

/// Strategy for generating role names.
fn role_strategy() -> impl Strategy<Value = String> {
    prop_oneof![
        Just("A".to_string()),
        Just("B".to_string()),
        Just("C".to_string()),
        Just("D".to_string()),
    ]
}

/// Strategy for generating labels.
fn label_strategy() -> impl Strategy<Value = Label> {
    prop_oneof![
        Just(Label::new("m1")),
        Just(Label::new("m2")),
        Just(Label::new("m3")),
        Just(Label::new("accept")),
        Just(Label::new("reject")),
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
    ]
}

/// Strategy for generating simple LocalTypes (non-recursive).
#[allow(dead_code)]
fn simple_local_strategy() -> impl Strategy<Value = LocalTypeR> {
    prop_oneof![
        Just(LocalTypeR::End),
        (role_strategy(), label_strategy()).prop_map(|(p, l)| LocalTypeR::send(
            &p,
            l,
            LocalTypeR::End
        )),
        (role_strategy(), label_strategy()).prop_map(|(p, l)| LocalTypeR::recv(
            &p,
            l,
            LocalTypeR::End
        )),
    ]
}

// ============================================================================
// can_step Tests
// ============================================================================

#[test]
fn test_can_step_head_action() {
    // A -> B: msg. end
    let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
    let act = GlobalAction::new("A", "B", Label::new("msg"));

    assert!(can_step(&g, &act), "Head action should be enabled");
}

#[test]
fn test_can_step_wrong_sender() {
    let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
    let act = GlobalAction::new("C", "B", Label::new("msg"));

    assert!(!can_step(&g, &act), "Wrong sender should not be enabled");
}

#[test]
fn test_can_step_wrong_receiver() {
    let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
    let act = GlobalAction::new("A", "C", Label::new("msg"));

    assert!(!can_step(&g, &act), "Wrong receiver should not be enabled");
}

#[test]
fn test_can_step_wrong_label() {
    let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
    let act = GlobalAction::new("A", "B", Label::new("other"));

    assert!(!can_step(&g, &act), "Wrong label should not be enabled");
}

#[test]
fn test_can_step_end() {
    let g = GlobalType::End;
    let act = GlobalAction::new("A", "B", Label::new("msg"));

    assert!(!can_step(&g, &act), "End type should not enable any action");
}

#[test]
fn test_can_step_async_reorder() {
    // A -> B: m1. (C -> D: m2. end)
    // Action C -> D should skip A -> B since D ≠ B
    let inner = GlobalType::send("C", "D", Label::new("m2"), GlobalType::End);
    let g = GlobalType::send("A", "B", Label::new("m1"), inner);

    let act = GlobalAction::new("C", "D", Label::new("m2"));
    assert!(
        can_step(&g, &act),
        "Async action should skip unrelated comm"
    );
}

#[test]
fn test_can_step_async_blocked_same_receiver() {
    // A -> B: m1. (C -> B: m2. end)
    // Action C -> B CANNOT skip A -> B since B == B
    let inner = GlobalType::send("C", "B", Label::new("m2"), GlobalType::End);
    let g = GlobalType::send("A", "B", Label::new("m1"), inner);

    let act = GlobalAction::new("C", "B", Label::new("m2"));
    assert!(
        !can_step(&g, &act),
        "Action with same receiver should block"
    );
}

#[test]
fn test_can_step_async_blocked_sender_is_receiver() {
    // A -> B: m1. (B -> C: m2. end)
    // Action B -> C CANNOT skip A -> B since B == B (act.sender == receiver)
    let inner = GlobalType::send("B", "C", Label::new("m2"), GlobalType::End);
    let g = GlobalType::send("A", "B", Label::new("m1"), inner);

    let act = GlobalAction::new("B", "C", Label::new("m2"));
    assert!(!can_step(&g, &act), "Action from receiver should block");
}

#[test]
fn test_can_step_mu() {
    // μt. A -> B: msg. t
    let g = GlobalType::mu(
        "t",
        GlobalType::send("A", "B", Label::new("msg"), GlobalType::var("t")),
    );
    let act = GlobalAction::new("A", "B", Label::new("msg"));

    assert!(can_step(&g, &act), "Should enable after μ-unfolding");
}

// ============================================================================
// step Tests
// ============================================================================

#[test]
fn test_step_head() {
    let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
    let act = GlobalAction::new("A", "B", Label::new("msg"));

    let result = step(&g, &act);
    assert_eq!(result, Some(GlobalType::End), "Should step to End");
}

#[test]
fn test_step_async() {
    // A -> B: m1. (C -> D: m2. end)
    // Step C -> D results in: A -> B: m1. end
    let inner = GlobalType::send("C", "D", Label::new("m2"), GlobalType::End);
    let g = GlobalType::send("A", "B", Label::new("m1"), inner);

    let act = GlobalAction::new("C", "D", Label::new("m2"));
    let result = step(&g, &act);

    let expected = GlobalType::send("A", "B", Label::new("m1"), GlobalType::End);
    assert_eq!(
        result,
        Some(expected),
        "Should step inner and preserve outer"
    );
}

#[test]
fn test_step_mu() {
    // μt. A -> B: msg. t
    let g = GlobalType::mu(
        "t",
        GlobalType::send("A", "B", Label::new("msg"), GlobalType::var("t")),
    );
    let act = GlobalAction::new("A", "B", Label::new("msg"));

    let result = step(&g, &act);
    assert_eq!(result, Some(g), "Should step to recursive type itself");
}

#[test]
fn test_step_choice() {
    let g = GlobalType::comm(
        "A",
        "B",
        vec![
            (Label::new("accept"), GlobalType::End),
            (Label::new("reject"), GlobalType::End),
        ],
    );

    let accept_act = GlobalAction::new("A", "B", Label::new("accept"));
    let reject_act = GlobalAction::new("A", "B", Label::new("reject"));

    assert_eq!(step(&g, &accept_act), Some(GlobalType::End));
    assert_eq!(step(&g, &reject_act), Some(GlobalType::End));
}

// ============================================================================
// local_can_step / local_step Tests
// ============================================================================

#[test]
fn test_local_can_step_send() {
    let lt = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
    let act = LocalAction::send("B", Label::new("msg"));

    assert!(local_can_step(&lt, &act));
}

#[test]
fn test_local_can_step_recv() {
    let lt = LocalTypeR::recv("A", Label::new("msg"), LocalTypeR::End);
    let act = LocalAction::recv("A", Label::new("msg"));

    assert!(local_can_step(&lt, &act));
}

#[test]
fn test_local_can_step_async() {
    // !B{m1. !C{m2. end}}
    // Action !C{m2} can skip !B{m1} since C ≠ B
    let inner = LocalTypeR::send("C", Label::new("m2"), LocalTypeR::End);
    let lt = LocalTypeR::send("B", Label::new("m1"), inner);

    let act = LocalAction::send("C", Label::new("m2"));
    assert!(local_can_step(&lt, &act), "Should enable async send skip");
}

#[test]
fn test_local_step_send() {
    let lt = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
    let act = LocalAction::send("B", Label::new("msg"));

    assert_eq!(local_step(&lt, &act), Some(LocalTypeR::End));
}

#[test]
fn test_local_step_recv() {
    let lt = LocalTypeR::recv("A", Label::new("msg"), LocalTypeR::End);
    let act = LocalAction::recv("A", Label::new("msg"));

    assert_eq!(local_step(&lt, &act), Some(LocalTypeR::End));
}

#[test]
fn test_local_step_async() {
    // !B{m1. !C{m2. end}} --[!C,m2]--> !B{m1. end}
    let inner = LocalTypeR::send("C", Label::new("m2"), LocalTypeR::End);
    let lt = LocalTypeR::send("B", Label::new("m1"), inner);

    let act = LocalAction::send("C", Label::new("m2"));
    let result = local_step(&lt, &act);

    let expected = LocalTypeR::send("B", Label::new("m1"), LocalTypeR::End);
    assert_eq!(result, Some(expected));
}

// ============================================================================
// consume_with_proof Tests
// ============================================================================

#[test]
fn test_consume_proof_simple() {
    let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);

    let result = consume_with_proof(&g, "A", "B", &Label::new("msg"));
    assert!(result.is_some(), "Consume should succeed");

    let proof = result.unwrap();
    assert_eq!(proof.continuation(), &GlobalType::End);
}

#[test]
fn test_consume_proof_mu() {
    let g = GlobalType::mu(
        "t",
        GlobalType::send("A", "B", Label::new("msg"), GlobalType::var("t")),
    );

    let result = consume_with_proof(&g, "A", "B", &Label::new("msg"));
    assert!(result.is_some(), "Consume should succeed after unfolding");
}

#[test]
fn test_consume_proof_wrong_sender() {
    let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);

    let result = consume_with_proof(&g, "C", "B", &Label::new("msg"));
    assert!(result.is_none(), "Consume should fail for wrong sender");
}

// ============================================================================
// reduces / reduces_star Tests
// ============================================================================

#[test]
fn test_reduces_simple() {
    let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);

    assert!(
        reduces(&g, &GlobalType::End),
        "Should reduce to continuation"
    );
}

#[test]
fn test_reduces_choice() {
    let g = GlobalType::comm(
        "A",
        "B",
        vec![
            (
                Label::new("yes"),
                GlobalType::send("B", "C", Label::new("m2"), GlobalType::End),
            ),
            (Label::new("no"), GlobalType::End),
        ],
    );

    // Can reduce to either branch
    assert!(reduces(&g, &GlobalType::End));
    assert!(reduces(
        &g,
        &GlobalType::send("B", "C", Label::new("m2"), GlobalType::End)
    ));
}

#[test]
fn test_reduces_star_refl() {
    let g = GlobalType::End;
    assert!(reduces_star(&g, &g), "Reflexive: g reduces to itself");
}

#[test]
fn test_reduces_star_transitive() {
    // A -> B: m1. (B -> C: m2. end)
    let g = GlobalType::send(
        "A",
        "B",
        Label::new("m1"),
        GlobalType::send("B", "C", Label::new("m2"), GlobalType::End),
    );

    assert!(
        reduces_star(&g, &GlobalType::End),
        "Should reduce to End transitively"
    );
}

// ============================================================================
// good_g Tests
// ============================================================================

#[test]
fn test_good_g_simple() {
    let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
    assert!(good_g(&g), "Simple type should be good");
}

#[test]
fn test_good_g_end() {
    assert!(good_g(&GlobalType::End), "End should be good");
}

#[test]
fn test_good_g_choice() {
    let g = GlobalType::comm(
        "A",
        "B",
        vec![
            (Label::new("yes"), GlobalType::End),
            (Label::new("no"), GlobalType::End),
        ],
    );
    assert!(good_g(&g), "Choice should be good");
}

#[test]
fn test_good_g_recursive() {
    let g = GlobalType::mu(
        "t",
        GlobalType::comm(
            "A",
            "B",
            vec![
                (Label::new("continue"), GlobalType::var("t")),
                (Label::new("stop"), GlobalType::End),
            ],
        ),
    );
    assert!(good_g(&g), "Recursive type should be good");
}

// ============================================================================
// LocalAction Conversion Tests
// ============================================================================

#[test]
fn test_local_action_to_global_send() {
    let act = LocalAction::send("B", Label::new("msg"));
    let global = act.to_global("A");

    assert_eq!(global.sender, "A");
    assert_eq!(global.receiver, "B");
    assert_eq!(global.label.name, "msg");
}

#[test]
fn test_local_action_to_global_recv() {
    let act = LocalAction::recv("B", Label::new("msg"));
    let global = act.to_global("A");

    assert_eq!(global.sender, "B"); // Partner is sender for recv
    assert_eq!(global.receiver, "A"); // Role is receiver for recv
    assert_eq!(global.label.name, "msg");
}

// ============================================================================
// Property-Based Tests
// ============================================================================

#[test]
fn proptest_can_step_implies_step_exists() {
    let mut runner = TestRunner::new_with_rng(
        Config {
            test_name: Some("can_step_implies_step"),
            source_file: Some(file!()),
            ..Config::default()
        },
        TestRng::from_seed(RngAlgorithm::ChaCha, &DETERMINISTIC_SEED),
    );

    let strategy = simple_global_strategy();

    for _ in 0..50 {
        let tree = strategy.new_tree(&mut runner).unwrap();
        let g = tree.current();

        // For each role pair that could communicate
        let roles = g.roles();
        for sender in &roles {
            for receiver in &roles {
                if sender == receiver {
                    continue;
                }

                // Try a few labels
                for label_name in &["m1", "m2", "accept", "reject"] {
                    let label = Label::new(*label_name);
                    let act = GlobalAction::new(sender, receiver, label);

                    if can_step(&g, &act) {
                        assert!(
                            step(&g, &act).is_some(),
                            "can_step implies step exists for {:?} on action {:?}",
                            g,
                            act
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn proptest_step_implies_can_step() {
    let mut runner = TestRunner::new_with_rng(
        Config {
            test_name: Some("step_implies_can_step"),
            source_file: Some(file!()),
            ..Config::default()
        },
        TestRng::from_seed(RngAlgorithm::ChaCha, &DETERMINISTIC_SEED),
    );

    let strategy = simple_global_strategy();

    for _ in 0..50 {
        let tree = strategy.new_tree(&mut runner).unwrap();
        let g = tree.current();

        let roles = g.roles();
        for sender in &roles {
            for receiver in &roles {
                if sender == receiver {
                    continue;
                }

                for label_name in &["m1", "m2", "accept", "reject"] {
                    let label = Label::new(*label_name);
                    let act = GlobalAction::new(sender, receiver, label);

                    if step(&g, &act).is_some() {
                        assert!(
                            can_step(&g, &act),
                            "step exists implies can_step for {:?} on action {:?}",
                            g,
                            act
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn proptest_reduces_star_reflexive() {
    let mut runner = TestRunner::new_with_rng(
        Config {
            test_name: Some("reduces_star_reflexive"),
            source_file: Some(file!()),
            ..Config::default()
        },
        TestRng::from_seed(RngAlgorithm::ChaCha, &DETERMINISTIC_SEED),
    );

    let strategy = simple_global_strategy();

    for _ in 0..50 {
        let tree = strategy.new_tree(&mut runner).unwrap();
        let g = tree.current();

        assert!(
            reduces_star(&g, &g),
            "reduces_star should be reflexive for {:?}",
            g
        );
    }
}

#[test]
fn proptest_well_formed_is_good() {
    let mut runner = TestRunner::new_with_rng(
        Config {
            test_name: Some("well_formed_is_good"),
            source_file: Some(file!()),
            ..Config::default()
        },
        TestRng::from_seed(RngAlgorithm::ChaCha, &DETERMINISTIC_SEED),
    );

    let strategy = simple_global_strategy();

    for _ in 0..50 {
        let tree = strategy.new_tree(&mut runner).unwrap();
        let g = tree.current();

        if g.well_formed() {
            assert!(
                good_g(&g),
                "Well-formed type should satisfy good_g: {:?}",
                g
            );
        }
    }
}
