//! Coherence Tests for Global Types
//!
//! Tests that verify the coherence bundle implementation from ECOOP 2025.
//! A coherent global type satisfies:
//! - Linear: (placeholder, always true)
//! - Size: All communications have non-empty branches
//! - Action: Sender ≠ receiver
//! - Unique labels: Branch labels are unique
//! - Projectable: Every role has a successful projection
//! - Good: Enabledness implies step existence

#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

use proptest::prelude::*;
use proptest::strategy::ValueTree;
use proptest::test_runner::{Config, RngAlgorithm, TestRng, TestRunner};
use telltale_theory::coherence::{
    action_pred, check_coherent, good_g, linear_pred, projectable, size_pred,
};
use telltale_theory::well_formedness::unique_labels;
use telltale_types::{GlobalType, Label};

/// Deterministic seed for property-based tests.
const DETERMINISTIC_SEED: [u8; 32] = [
    0x43, 0x6F, 0x68, 0x65, 0x72, 0x65, 0x6E, 0x63, // "Coherenc"
    0x65, 0x54, 0x65, 0x73, 0x74, 0x53, 0x65, 0x65, // "eTestSee"
    0x64, 0x46, 0x6F, 0x72, 0x56, 0x61, 0x6C, 0x69, // "dForVali"
    0x64, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x21, 0x21, // "dation!!"
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
    ]
}

/// Strategy for generating labels.
fn label_strategy() -> impl Strategy<Value = Label> {
    prop_oneof![
        Just(Label::new("m1")),
        Just(Label::new("m2")),
        Just(Label::new("accept")),
        Just(Label::new("reject")),
    ]
}

/// Strategy for well-formed GlobalTypes (coherent).
fn well_formed_global_strategy() -> impl Strategy<Value = GlobalType> {
    prop_oneof![
        // End type
        Just(GlobalType::End),
        // Single communication with unique sender/receiver
        (role_strategy(), role_strategy(), label_strategy())
            .prop_filter("sender != receiver", |(s, r, _)| s != r)
            .prop_map(|(s, r, l)| GlobalType::comm(&s, &r, vec![(l, GlobalType::End)])),
        // Choice with unique labels
        (role_strategy(), role_strategy())
            .prop_filter("sender != receiver", |(s, r)| s != r)
            .prop_map(|(s, r)| {
                GlobalType::comm(
                    &s,
                    &r,
                    vec![
                        (Label::new("accept"), GlobalType::End),
                        (Label::new("reject"), GlobalType::End),
                    ],
                )
            }),
    ]
}

/// Strategy for malformed GlobalTypes (incoherent).
fn malformed_global_strategy() -> impl Strategy<Value = GlobalType> {
    prop_oneof![
        // Self-communication
        role_strategy().prop_map(|r| GlobalType::send(&r, &r, Label::new("msg"), GlobalType::End)),
        // Duplicate labels
        (role_strategy(), role_strategy())
            .prop_filter("sender != receiver", |(s, r)| s != r)
            .prop_map(|(s, r)| {
                GlobalType::comm(
                    &s,
                    &r,
                    vec![
                        (Label::new("dup"), GlobalType::End),
                        (Label::new("dup"), GlobalType::End),
                    ],
                )
            }),
        // Empty branches
        (role_strategy(), role_strategy())
            .prop_filter("sender != receiver", |(s, r)| s != r)
            .prop_map(|(s, r)| GlobalType::Comm {
                sender: s,
                receiver: r,
                branches: vec![],
            }),
    ]
}

// ============================================================================
// CoherentG Bundle Tests
// ============================================================================

#[test]
fn test_coherent_simple_protocol() {
    let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
    let bundle = check_coherent(&g);

    assert!(bundle.linear, "Should be linear");
    assert!(bundle.size, "Should have non-empty branches");
    assert!(bundle.action, "Sender ≠ receiver");
    assert!(bundle.uniq_labels, "Labels should be unique");
    assert!(bundle.projectable, "Should be projectable");
    assert!(bundle.good, "Should be good");
    assert!(bundle.is_coherent(), "Overall coherence");
}

#[test]
fn test_coherent_choice() {
    let g = GlobalType::comm(
        "A",
        "B",
        vec![
            (Label::new("yes"), GlobalType::End),
            (Label::new("no"), GlobalType::End),
        ],
    );
    let bundle = check_coherent(&g);

    assert!(bundle.is_coherent(), "Choice should be coherent");
}

#[test]
fn test_coherent_three_party() {
    // A -> B: m1. B -> C: m2. end
    let g = GlobalType::send(
        "A",
        "B",
        Label::new("m1"),
        GlobalType::send("B", "C", Label::new("m2"), GlobalType::End),
    );
    let bundle = check_coherent(&g);

    assert!(
        bundle.is_coherent(),
        "Three-party protocol should be coherent"
    );
}

#[test]
fn test_coherent_recursive() {
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
    let bundle = check_coherent(&g);

    assert!(bundle.is_coherent(), "Recursive type should be coherent");
}

#[test]
fn test_coherent_end() {
    let bundle = check_coherent(&GlobalType::End);
    assert!(bundle.is_coherent(), "End should be coherent");
}

// ============================================================================
// Incoherent Type Detection Tests
// ============================================================================

#[test]
fn test_incoherent_self_comm() {
    let g = GlobalType::send("A", "A", Label::new("msg"), GlobalType::End);
    let bundle = check_coherent(&g);

    assert!(!bundle.action, "Should fail action predicate");
    assert!(!bundle.is_coherent(), "Should be incoherent");
}

#[test]
fn test_incoherent_duplicate_labels() {
    let g = GlobalType::comm(
        "A",
        "B",
        vec![
            (Label::new("msg"), GlobalType::End),
            (Label::new("msg"), GlobalType::End),
        ],
    );
    let bundle = check_coherent(&g);

    assert!(!bundle.uniq_labels, "Should fail unique labels");
    assert!(!bundle.is_coherent(), "Should be incoherent");
}

#[test]
fn test_incoherent_empty_branches() {
    let g = GlobalType::Comm {
        sender: "A".to_string(),
        receiver: "B".to_string(),
        branches: vec![],
    };
    let bundle = check_coherent(&g);

    assert!(!bundle.size, "Should fail size predicate");
    assert!(!bundle.is_coherent(), "Should be incoherent");
}

#[test]
fn test_incoherent_nested_self_comm() {
    // A -> B: m1. (B -> B: m2. end)
    let g = GlobalType::send(
        "A",
        "B",
        Label::new("m1"),
        GlobalType::send("B", "B", Label::new("m2"), GlobalType::End),
    );
    let bundle = check_coherent(&g);

    assert!(!bundle.action, "Nested self-comm should fail action");
    assert!(!bundle.is_coherent(), "Should be incoherent");
}

#[test]
fn test_incoherent_nested_duplicate_labels() {
    // A -> B: m1. (B -> C: {dup | dup})
    let inner = GlobalType::comm(
        "B",
        "C",
        vec![
            (Label::new("dup"), GlobalType::End),
            (Label::new("dup"), GlobalType::End),
        ],
    );
    let g = GlobalType::send("A", "B", Label::new("m1"), inner);
    let bundle = check_coherent(&g);

    assert!(!bundle.uniq_labels, "Nested duplicate labels should fail");
    assert!(!bundle.is_coherent(), "Should be incoherent");
}

// ============================================================================
// Individual Predicate Tests
// ============================================================================

#[test]
fn test_linear_pred_always_true() {
    // Currently a placeholder
    assert!(linear_pred(&GlobalType::End));
    assert!(linear_pred(&GlobalType::send(
        "A",
        "B",
        Label::new("msg"),
        GlobalType::End
    )));
}

#[test]
fn test_size_pred() {
    let good = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
    assert!(size_pred(&good));

    let bad = GlobalType::Comm {
        sender: "A".to_string(),
        receiver: "B".to_string(),
        branches: vec![],
    };
    assert!(!size_pred(&bad));
}

#[test]
fn test_action_pred() {
    let good = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
    assert!(action_pred(&good));

    let bad = GlobalType::send("A", "A", Label::new("msg"), GlobalType::End);
    assert!(!action_pred(&bad));
}

#[test]
fn test_unique_labels() {
    let good = GlobalType::comm(
        "A",
        "B",
        vec![
            (Label::new("a"), GlobalType::End),
            (Label::new("b"), GlobalType::End),
        ],
    );
    assert!(unique_labels(&good));

    let bad = GlobalType::comm(
        "A",
        "B",
        vec![
            (Label::new("x"), GlobalType::End),
            (Label::new("x"), GlobalType::End),
        ],
    );
    assert!(!unique_labels(&bad));
}

#[test]
fn test_projectable_simple() {
    let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
    assert!(projectable(&g));
}

#[test]
fn test_projectable_three_party() {
    let g = GlobalType::send(
        "A",
        "B",
        Label::new("m1"),
        GlobalType::send("B", "C", Label::new("m2"), GlobalType::End),
    );
    assert!(projectable(&g));
}

#[test]
fn test_good_g_simple() {
    let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
    assert!(good_g(&g));
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
    assert!(good_g(&g));
}

// ============================================================================
// Property-Based Tests
// ============================================================================

#[test]
fn proptest_well_formed_implies_coherent() {
    let mut runner = TestRunner::new_with_rng(
        Config {
            test_name: Some("well_formed_implies_coherent"),
            source_file: Some(file!()),
            ..Config::default()
        },
        TestRng::from_seed(RngAlgorithm::ChaCha, &DETERMINISTIC_SEED),
    );

    let strategy = well_formed_global_strategy();

    for _ in 0..100 {
        let tree = strategy.new_tree(&mut runner).unwrap();
        let g = tree.current();

        if g.well_formed() {
            let bundle = check_coherent(&g);
            assert!(
                bundle.is_coherent(),
                "Well-formed type should be coherent: {:?} -> {:?}",
                g,
                bundle
            );
        }
    }
}

#[test]
fn proptest_malformed_is_incoherent() {
    let mut runner = TestRunner::new_with_rng(
        Config {
            test_name: Some("malformed_is_incoherent"),
            source_file: Some(file!()),
            ..Config::default()
        },
        TestRng::from_seed(RngAlgorithm::ChaCha, &DETERMINISTIC_SEED),
    );

    let strategy = malformed_global_strategy();

    for _ in 0..50 {
        let tree = strategy.new_tree(&mut runner).unwrap();
        let g = tree.current();

        let bundle = check_coherent(&g);
        assert!(
            !bundle.is_coherent(),
            "Malformed type should be incoherent: {:?} -> {:?}",
            g,
            bundle
        );
    }
}

#[test]
fn proptest_coherent_implies_well_formed() {
    let mut runner = TestRunner::new_with_rng(
        Config {
            test_name: Some("coherent_implies_well_formed"),
            source_file: Some(file!()),
            ..Config::default()
        },
        TestRng::from_seed(RngAlgorithm::ChaCha, &DETERMINISTIC_SEED),
    );

    let strategy = well_formed_global_strategy();

    for _ in 0..100 {
        let tree = strategy.new_tree(&mut runner).unwrap();
        let g = tree.current();

        let bundle = check_coherent(&g);
        if bundle.is_coherent() {
            assert!(
                g.well_formed(),
                "Coherent type should be well-formed: {:?}",
                g
            );
        }
    }
}

#[test]
fn proptest_coherence_bundle_consistency() {
    let mut runner = TestRunner::new_with_rng(
        Config {
            test_name: Some("coherence_bundle_consistency"),
            source_file: Some(file!()),
            ..Config::default()
        },
        TestRng::from_seed(RngAlgorithm::ChaCha, &DETERMINISTIC_SEED),
    );

    let strategy = well_formed_global_strategy();

    for _ in 0..100 {
        let tree = strategy.new_tree(&mut runner).unwrap();
        let g = tree.current();

        let bundle = check_coherent(&g);

        // Verify bundle fields match individual predicates
        assert_eq!(bundle.linear, linear_pred(&g), "linear mismatch");
        assert_eq!(bundle.size, size_pred(&g), "size mismatch");
        assert_eq!(bundle.action, action_pred(&g), "action mismatch");
        assert_eq!(
            bundle.uniq_labels,
            unique_labels(&g),
            "uniq_labels mismatch"
        );
        assert_eq!(bundle.projectable, projectable(&g), "projectable mismatch");
        assert_eq!(bundle.good, good_g(&g), "good mismatch");

        // Verify is_coherent matches conjunction
        let expected = bundle.linear
            && bundle.size
            && bundle.action
            && bundle.uniq_labels
            && bundle.projectable
            && bundle.good;
        assert_eq!(bundle.is_coherent(), expected, "is_coherent mismatch");
    }
}
