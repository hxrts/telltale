//! Property-based tests for asynchronous subtyping.
//!
//! These tests verify that the Rust async subtyping implementation
//! satisfies key algebraic properties. The SISO decomposition, tree
//! subtyping, and orphan checks are exercised with randomized inputs.
//!
//! All tests use fixed seeds for full reproducibility.

#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

use proptest::prelude::*;
use proptest::strategy::ValueTree;
use proptest::test_runner::{Config, RngAlgorithm, TestRng, TestRunner};
use rumpsteak_theory::{
    async_equivalent, async_subtype, orphan_free, siso_decompose, InputTree, OutputTree,
    SisoSegment,
};
use rumpsteak_types::{Label, LocalTypeR, PayloadSort};

/// Deterministic seed for property-based tests.
const DETERMINISTIC_SEED: [u8; 32] = [
    0x41, 0x73, 0x79, 0x6E, 0x63, 0x53, 0x75, 0x62, // "AsyncSub"
    0x74, 0x79, 0x70, 0x69, 0x6E, 0x67, 0x54, 0x65, // "typingTe"
    0x73, 0x74, 0x53, 0x65, 0x65, 0x64, 0x56, 0x61, // "stSeedVa"
    0x6C, 0x75, 0x65, 0x31, 0x32, 0x33, 0x34, 0x21, // "lue1234!"
];

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

/// Strategy for generating simple local types (non-recursive).
fn simple_local_strategy() -> impl Strategy<Value = LocalTypeR> {
    prop_oneof![
        // End type
        Just(LocalTypeR::End),
        // Single send
        (role_strategy(), label_strategy()).prop_map(|(r, l)| LocalTypeR::send(&r, l, LocalTypeR::End)),
        // Single recv
        (role_strategy(), label_strategy()).prop_map(|(r, l)| LocalTypeR::recv(&r, l, LocalTypeR::End)),
    ]
}

/// Strategy for generating send-recv sequences.
fn send_recv_sequence_strategy() -> impl Strategy<Value = LocalTypeR> {
    prop_oneof![
        // Send then End
        (role_strategy(), label_strategy())
            .prop_map(|(r, l)| LocalTypeR::send(&r, l, LocalTypeR::End)),
        // Recv then End
        (role_strategy(), label_strategy())
            .prop_map(|(r, l)| LocalTypeR::recv(&r, l, LocalTypeR::End)),
        // Send then Recv
        (role_strategy(), label_strategy(), role_strategy(), label_strategy())
            .prop_map(|(r1, l1, r2, l2)| {
                LocalTypeR::send(&r1, l1, LocalTypeR::recv(&r2, l2, LocalTypeR::End))
            }),
        // Recv then Send
        (role_strategy(), label_strategy(), role_strategy(), label_strategy())
            .prop_map(|(r1, l1, r2, l2)| {
                LocalTypeR::recv(&r1, l1, LocalTypeR::send(&r2, l2, LocalTypeR::End))
            }),
        // Send, Send, Recv
        (
            role_strategy(),
            label_strategy(),
            role_strategy(),
            label_strategy(),
            role_strategy(),
            label_strategy()
        )
            .prop_map(|(r1, l1, r2, l2, r3, l3)| {
                LocalTypeR::send(
                    &r1,
                    l1,
                    LocalTypeR::send(&r2, l2, LocalTypeR::recv(&r3, l3, LocalTypeR::End)),
                )
            }),
    ]
}

/// Strategy for generating choice types (internal or external).
fn choice_strategy() -> impl Strategy<Value = LocalTypeR> {
    (
        role_strategy(),
        label_strategy(),
        label_strategy(),
        any::<bool>(),
    )
        .prop_filter("distinct labels", |(_, l1, l2, _)| l1.name != l2.name)
        .prop_map(|(partner, l1, l2, is_send)| {
            let branches = vec![(l1, LocalTypeR::End), (l2, LocalTypeR::End)];
            if is_send {
                LocalTypeR::Send {
                    partner,
                    branches,
                }
            } else {
                LocalTypeR::Recv {
                    partner,
                    branches,
                }
            }
        })
}

/// Strategy for input trees.
fn input_tree_strategy() -> impl Strategy<Value = InputTree> {
    prop_oneof![
        // Leaf
        Just(InputTree::Leaf),
        // Simple node
        (role_strategy(), label_strategy()).prop_map(|(p, l)| InputTree::Node {
            partner: p,
            label: l,
            children: vec![InputTree::Leaf],
        }),
        // Node with two children
        (role_strategy(), label_strategy()).prop_map(|(p, l)| InputTree::Node {
            partner: p,
            label: l,
            children: vec![InputTree::Leaf, InputTree::Leaf],
        }),
    ]
}

/// Strategy for output trees.
fn output_tree_strategy() -> impl Strategy<Value = OutputTree> {
    prop_oneof![
        // Leaf
        Just(OutputTree::Leaf),
        // Simple node
        (role_strategy(), label_strategy()).prop_map(|(p, l)| OutputTree::Node {
            partner: p,
            label: l,
            children: vec![OutputTree::Leaf],
        }),
        // Node with two children
        (role_strategy(), label_strategy()).prop_map(|(p, l)| OutputTree::Node {
            partner: p,
            label: l,
            children: vec![OutputTree::Leaf, OutputTree::Leaf],
        }),
    ]
}

// ============================================================================
// InputTree subtyping properties
// ============================================================================

#[test]
fn test_input_tree_reflexivity() {
    let mut runner = TestRunner::new_with_rng(
        Config::default(),
        TestRng::from_seed(RngAlgorithm::ChaCha, &DETERMINISTIC_SEED),
    );

    let strategy = input_tree_strategy();

    for _ in 0..50 {
        let tree = strategy
            .new_tree(&mut runner)
            .expect("Should generate value")
            .current();

        // Reflexivity: t ≤ t
        assert!(
            tree.subtype(&tree),
            "InputTree reflexivity failed for {:?}",
            tree
        );
    }
}

#[test]
fn test_input_tree_contravariance_leaf_accepts_all() {
    let mut runner = TestRunner::new_with_rng(
        Config::default(),
        TestRng::from_seed(RngAlgorithm::ChaCha, &DETERMINISTIC_SEED),
    );

    let strategy = input_tree_strategy();

    for _ in 0..50 {
        let tree = strategy
            .new_tree(&mut runner)
            .expect("Should generate value")
            .current();

        // Leaf accepts nothing, so anything is a subtype of Leaf
        assert!(
            tree.subtype(&InputTree::Leaf),
            "InputTree {:?} should be subtype of Leaf",
            tree
        );
    }
}

#[test]
fn test_input_tree_partner_mismatch_fails() {
    let tree1 = InputTree::Node {
        partner: "Alice".to_string(),
        label: Label::new("msg"),
        children: vec![InputTree::Leaf],
    };
    let tree2 = InputTree::Node {
        partner: "Bob".to_string(),
        label: Label::new("msg"),
        children: vec![InputTree::Leaf],
    };

    // Different partners should not be subtypes
    assert!(!tree1.subtype(&tree2));
    assert!(!tree2.subtype(&tree1));
}

#[test]
fn test_input_tree_label_mismatch_fails() {
    let tree1 = InputTree::Node {
        partner: "Alice".to_string(),
        label: Label::new("request"),
        children: vec![InputTree::Leaf],
    };
    let tree2 = InputTree::Node {
        partner: "Alice".to_string(),
        label: Label::new("response"),
        children: vec![InputTree::Leaf],
    };

    // Different labels should not be subtypes
    assert!(!tree1.subtype(&tree2));
    assert!(!tree2.subtype(&tree1));
}

// ============================================================================
// OutputTree subtyping properties
// ============================================================================

#[test]
fn test_output_tree_reflexivity() {
    let mut runner = TestRunner::new_with_rng(
        Config::default(),
        TestRng::from_seed(RngAlgorithm::ChaCha, &DETERMINISTIC_SEED),
    );

    let strategy = output_tree_strategy();

    for _ in 0..50 {
        let tree = strategy
            .new_tree(&mut runner)
            .expect("Should generate value")
            .current();

        // Reflexivity: t ≤ t
        assert!(
            tree.subtype(&tree),
            "OutputTree reflexivity failed for {:?}",
            tree
        );
    }
}

#[test]
fn test_output_tree_covariance_leaf_subtype_of_all() {
    let mut runner = TestRunner::new_with_rng(
        Config::default(),
        TestRng::from_seed(RngAlgorithm::ChaCha, &DETERMINISTIC_SEED),
    );

    let strategy = output_tree_strategy();

    for _ in 0..50 {
        let tree = strategy
            .new_tree(&mut runner)
            .expect("Should generate value")
            .current();

        // Leaf sends nothing, so Leaf is subtype of everything (covariant)
        assert!(
            OutputTree::Leaf.subtype(&tree),
            "Leaf should be subtype of {:?}",
            tree
        );
    }
}

#[test]
fn test_output_tree_node_not_subtype_of_leaf() {
    let mut runner = TestRunner::new_with_rng(
        Config::default(),
        TestRng::from_seed(RngAlgorithm::ChaCha, &DETERMINISTIC_SEED),
    );

    let strategy = output_tree_strategy().prop_filter("not leaf", |t| !t.is_empty());

    for _ in 0..30 {
        let tree = strategy
            .new_tree(&mut runner)
            .expect("Should generate value")
            .current();

        // Non-leaf output is NOT subtype of Leaf (covariant: can't send if nothing expected)
        assert!(
            !tree.subtype(&OutputTree::Leaf),
            "Non-leaf {:?} should NOT be subtype of Leaf",
            tree
        );
    }
}

#[test]
fn test_output_tree_partner_mismatch_fails() {
    let tree1 = OutputTree::Node {
        partner: "Server".to_string(),
        label: Label::new("response"),
        children: vec![OutputTree::Leaf],
    };
    let tree2 = OutputTree::Node {
        partner: "Client".to_string(),
        label: Label::new("response"),
        children: vec![OutputTree::Leaf],
    };

    // Different partners should not be subtypes
    assert!(!tree1.subtype(&tree2));
    assert!(!tree2.subtype(&tree1));
}

// ============================================================================
// SISO decomposition properties
// ============================================================================

#[test]
fn test_siso_decompose_end_is_empty() {
    let segments = siso_decompose(&LocalTypeR::End).unwrap();
    assert!(
        segments.is_empty(),
        "End should decompose to empty segments"
    );
}

#[test]
fn test_siso_decompose_succeeds_for_simple_types() {
    let mut runner = TestRunner::new_with_rng(
        Config::default(),
        TestRng::from_seed(RngAlgorithm::ChaCha, &DETERMINISTIC_SEED),
    );

    let strategy = simple_local_strategy();

    for _ in 0..50 {
        let lt = strategy
            .new_tree(&mut runner)
            .expect("Should generate value")
            .current();

        let result = siso_decompose(&lt);
        assert!(
            result.is_ok(),
            "SISO decompose should succeed for {:?}, got {:?}",
            lt,
            result
        );
    }
}

#[test]
fn test_siso_decompose_succeeds_for_sequences() {
    let mut runner = TestRunner::new_with_rng(
        Config::default(),
        TestRng::from_seed(RngAlgorithm::ChaCha, &DETERMINISTIC_SEED),
    );

    let strategy = send_recv_sequence_strategy();

    for _ in 0..50 {
        let lt = strategy
            .new_tree(&mut runner)
            .expect("Should generate value")
            .current();

        let result = siso_decompose(&lt);
        assert!(
            result.is_ok(),
            "SISO decompose should succeed for sequence {:?}, got {:?}",
            lt,
            result
        );
    }
}

#[test]
fn test_siso_decompose_non_empty_for_non_end() {
    let mut runner = TestRunner::new_with_rng(
        Config::default(),
        TestRng::from_seed(RngAlgorithm::ChaCha, &DETERMINISTIC_SEED),
    );

    let strategy = send_recv_sequence_strategy();

    for _ in 0..30 {
        let lt = strategy
            .new_tree(&mut runner)
            .expect("Should generate value")
            .current();

        if !matches!(lt, LocalTypeR::End) {
            let segments = siso_decompose(&lt).unwrap();
            assert!(
                !segments.is_empty(),
                "Non-End type {:?} should have at least one segment",
                lt
            );
        }
    }
}

// ============================================================================
// async_subtype properties
// ============================================================================

#[test]
fn test_async_subtype_reflexive() {
    let mut runner = TestRunner::new_with_rng(
        Config::default(),
        TestRng::from_seed(RngAlgorithm::ChaCha, &DETERMINISTIC_SEED),
    );

    let strategy = send_recv_sequence_strategy();

    for _ in 0..50 {
        let lt = strategy
            .new_tree(&mut runner)
            .expect("Should generate value")
            .current();

        let result = async_subtype(&lt, &lt);
        assert!(
            result.is_ok(),
            "async_subtype should be reflexive for {:?}, got {:?}",
            lt,
            result
        );
    }
}

#[test]
fn test_async_subtype_end_reflexive() {
    let result = async_subtype(&LocalTypeR::End, &LocalTypeR::End);
    assert!(result.is_ok(), "End should be async subtype of End");
}

#[test]
fn test_async_subtype_end_is_subtype_of_all() {
    let mut runner = TestRunner::new_with_rng(
        Config::default(),
        TestRng::from_seed(RngAlgorithm::ChaCha, &DETERMINISTIC_SEED),
    );

    let strategy = send_recv_sequence_strategy();

    for _ in 0..30 {
        let lt = strategy
            .new_tree(&mut runner)
            .expect("Should generate value")
            .current();

        // End (doing nothing) should be a subtype of any type
        // because End trivially satisfies the supertype's requirements
        let result = async_subtype(&LocalTypeR::End, &lt);
        assert!(
            result.is_ok(),
            "End should be async subtype of {:?}, got {:?}",
            lt,
            result
        );
    }
}

// ============================================================================
// async_equivalent properties
// ============================================================================

#[test]
fn test_async_equivalent_reflexive() {
    let mut runner = TestRunner::new_with_rng(
        Config::default(),
        TestRng::from_seed(RngAlgorithm::ChaCha, &DETERMINISTIC_SEED),
    );

    let strategy = send_recv_sequence_strategy();

    for _ in 0..50 {
        let lt = strategy
            .new_tree(&mut runner)
            .expect("Should generate value")
            .current();

        assert!(
            async_equivalent(&lt, &lt),
            "async_equivalent should be reflexive for {:?}",
            lt
        );
    }
}

#[test]
fn test_async_equivalent_symmetric() {
    let mut runner = TestRunner::new_with_rng(
        Config::default(),
        TestRng::from_seed(RngAlgorithm::ChaCha, &DETERMINISTIC_SEED),
    );

    let strategy = send_recv_sequence_strategy();

    for _ in 0..30 {
        let lt1 = strategy
            .new_tree(&mut runner)
            .expect("Should generate value")
            .current();
        let lt2 = strategy
            .new_tree(&mut runner)
            .expect("Should generate value")
            .current();

        // Symmetry: equivalent(a, b) iff equivalent(b, a)
        let result1 = async_equivalent(&lt1, &lt2);
        let result2 = async_equivalent(&lt2, &lt1);
        assert_eq!(
            result1, result2,
            "async_equivalent should be symmetric: ({:?}, {:?}) gave {} and {}",
            lt1, lt2, result1, result2
        );
    }
}

// ============================================================================
// orphan_free properties
// ============================================================================

#[test]
fn test_orphan_free_end() {
    assert!(orphan_free(&LocalTypeR::End), "End should be orphan-free");
}

#[test]
fn test_orphan_free_simple_types() {
    let mut runner = TestRunner::new_with_rng(
        Config::default(),
        TestRng::from_seed(RngAlgorithm::ChaCha, &DETERMINISTIC_SEED),
    );

    let strategy = simple_local_strategy();

    for _ in 0..50 {
        let lt = strategy
            .new_tree(&mut runner)
            .expect("Should generate value")
            .current();

        // Simple types should all be orphan-free
        assert!(
            orphan_free(&lt),
            "Simple type {:?} should be orphan-free",
            lt
        );
    }
}

#[test]
fn test_orphan_free_sequences() {
    let mut runner = TestRunner::new_with_rng(
        Config::default(),
        TestRng::from_seed(RngAlgorithm::ChaCha, &DETERMINISTIC_SEED),
    );

    let strategy = send_recv_sequence_strategy();

    for _ in 0..50 {
        let lt = strategy
            .new_tree(&mut runner)
            .expect("Should generate value")
            .current();

        // All our generated sequences should be orphan-free
        assert!(
            orphan_free(&lt),
            "Sequence {:?} should be orphan-free",
            lt
        );
    }
}

// ============================================================================
// Choice type tests
// ============================================================================

#[test]
fn test_choice_types_decompose() {
    let mut runner = TestRunner::new_with_rng(
        Config::default(),
        TestRng::from_seed(RngAlgorithm::ChaCha, &DETERMINISTIC_SEED),
    );

    let strategy = choice_strategy();

    for _ in 0..30 {
        let lt = strategy
            .new_tree(&mut runner)
            .expect("Should generate value")
            .current();

        let result = siso_decompose(&lt);
        assert!(
            result.is_ok(),
            "Choice type {:?} should decompose, got {:?}",
            lt,
            result
        );
    }
}

#[test]
fn test_choice_types_reflexive_subtype() {
    let mut runner = TestRunner::new_with_rng(
        Config::default(),
        TestRng::from_seed(RngAlgorithm::ChaCha, &DETERMINISTIC_SEED),
    );

    let strategy = choice_strategy();

    for _ in 0..30 {
        let lt = strategy
            .new_tree(&mut runner)
            .expect("Should generate value")
            .current();

        let result = async_subtype(&lt, &lt);
        assert!(
            result.is_ok(),
            "Choice type {:?} should be subtype of itself, got {:?}",
            lt,
            result
        );
    }
}

// ============================================================================
// SisoSegment properties
// ============================================================================

#[test]
fn test_siso_segment_reflexive() {
    let mut runner = TestRunner::new_with_rng(
        Config::default(),
        TestRng::from_seed(RngAlgorithm::ChaCha, &DETERMINISTIC_SEED),
    );

    let input_strat = input_tree_strategy();
    let output_strat = output_tree_strategy();

    for _ in 0..30 {
        let inputs = input_strat
            .new_tree(&mut runner)
            .expect("Should generate input")
            .current();
        let outputs = output_strat
            .new_tree(&mut runner)
            .expect("Should generate output")
            .current();

        let seg = SisoSegment::new(inputs, outputs);
        assert!(
            seg.subtype(&seg),
            "SisoSegment should be reflexive: {:?}",
            seg
        );
    }
}

#[test]
fn test_siso_segment_empty_is_subtype() {
    let empty = SisoSegment::new(InputTree::Leaf, OutputTree::Leaf);

    let mut runner = TestRunner::new_with_rng(
        Config::default(),
        TestRng::from_seed(RngAlgorithm::ChaCha, &DETERMINISTIC_SEED),
    );

    let input_strat = input_tree_strategy();
    let output_strat = output_tree_strategy();

    for _ in 0..30 {
        let inputs = input_strat
            .new_tree(&mut runner)
            .expect("Should generate input")
            .current();
        let outputs = output_strat
            .new_tree(&mut runner)
            .expect("Should generate output")
            .current();

        let seg = SisoSegment::new(inputs, outputs);

        // Empty segment (does nothing) should be subtype of any segment
        assert!(
            empty.subtype(&seg),
            "Empty segment should be subtype of {:?}",
            seg
        );
    }
}

// ============================================================================
// Specific pattern tests
// ============================================================================

#[test]
fn test_async_reordering_send_recv() {
    // Test the key async insight: sends don't block receives
    // Under async semantics, !a.?b and ?b.!a may be comparable

    let send_recv = LocalTypeR::send(
        "B",
        Label::new("req"),
        LocalTypeR::recv("B", Label::new("resp"), LocalTypeR::End),
    );

    let recv_send = LocalTypeR::recv(
        "B",
        Label::new("resp"),
        LocalTypeR::send("B", Label::new("req"), LocalTypeR::End),
    );

    // Both should decompose successfully
    let send_recv_segs = siso_decompose(&send_recv);
    let recv_send_segs = siso_decompose(&recv_send);

    assert!(send_recv_segs.is_ok(), "send_recv should decompose");
    assert!(recv_send_segs.is_ok(), "recv_send should decompose");
}

#[test]
fn test_independent_sends_to_different_partners() {
    // Sends to different partners can be reordered
    let t1 = LocalTypeR::send(
        "B",
        Label::new("msg1"),
        LocalTypeR::send("C", Label::new("msg2"), LocalTypeR::End),
    );

    let t2 = LocalTypeR::send(
        "C",
        Label::new("msg2"),
        LocalTypeR::send("B", Label::new("msg1"), LocalTypeR::End),
    );

    // Both should decompose
    assert!(siso_decompose(&t1).is_ok());
    assert!(siso_decompose(&t2).is_ok());

    // Both should be orphan-free
    assert!(orphan_free(&t1));
    assert!(orphan_free(&t2));
}

#[test]
fn test_recursive_type_decomposition() {
    // μX. !B{ping.X} - infinite ping loop
    let recursive = LocalTypeR::mu(
        "loop",
        LocalTypeR::send("B", Label::new("ping"), LocalTypeR::var("loop")),
    );

    // Should decompose (with fuel limit preventing infinite recursion)
    let result = siso_decompose(&recursive);
    assert!(result.is_ok(), "Recursive type should decompose: {:?}", result);
}

#[test]
fn test_deeply_nested_sequence() {
    // Deep nesting: !A{m1.!B{m2.!C{m3.?A{r1.?B{r2.?C{r3.end}}}}}}
    let deep = LocalTypeR::send(
        "A",
        Label::new("m1"),
        LocalTypeR::send(
            "B",
            Label::new("m2"),
            LocalTypeR::send(
                "C",
                Label::new("m3"),
                LocalTypeR::recv(
                    "A",
                    Label::new("r1"),
                    LocalTypeR::recv(
                        "B",
                        Label::new("r2"),
                        LocalTypeR::recv("C", Label::new("r3"), LocalTypeR::End),
                    ),
                ),
            ),
        ),
    );

    let result = siso_decompose(&deep);
    assert!(result.is_ok(), "Deep nesting should decompose");

    assert!(orphan_free(&deep), "Deep nesting should be orphan-free");

    // Should be subtype of itself
    assert!(async_subtype(&deep, &deep).is_ok());
}

// ============================================================================
// Edge case tests
// ============================================================================

#[test]
fn test_var_type() {
    let var = LocalTypeR::var("X");

    // Var should decompose to empty (like End)
    let segs = siso_decompose(&var).unwrap();
    assert!(segs.is_empty(), "Var should decompose to empty");

    // Var should be orphan-free
    assert!(orphan_free(&var));

    // Var should be subtype of itself
    assert!(async_subtype(&var, &var).is_ok());
}

#[test]
fn test_single_branch_send() {
    let single = LocalTypeR::Send {
        partner: "B".to_string(),
        branches: vec![(Label::new("only"), LocalTypeR::End)],
    };

    let segs = siso_decompose(&single).unwrap();
    assert!(!segs.is_empty());
    assert!(orphan_free(&single));
    assert!(async_subtype(&single, &single).is_ok());
}

#[test]
fn test_single_branch_recv() {
    let single = LocalTypeR::Recv {
        partner: "A".to_string(),
        branches: vec![(Label::new("only"), LocalTypeR::End)],
    };

    let segs = siso_decompose(&single).unwrap();
    assert!(!segs.is_empty());
    assert!(orphan_free(&single));
    assert!(async_subtype(&single, &single).is_ok());
}

#[test]
fn test_three_branch_choice() {
    let three_way = LocalTypeR::Send {
        partner: "B".to_string(),
        branches: vec![
            (Label::new("opt1"), LocalTypeR::End),
            (Label::new("opt2"), LocalTypeR::End),
            (Label::new("opt3"), LocalTypeR::End),
        ],
    };

    let segs = siso_decompose(&three_way).unwrap();
    assert!(!segs.is_empty());
    assert!(orphan_free(&three_way));
    assert!(async_subtype(&three_way, &three_way).is_ok());
}

#[test]
fn test_mixed_partners_sequence() {
    // Send to B, recv from C, send to A
    let mixed = LocalTypeR::send(
        "B",
        Label::new("to_b"),
        LocalTypeR::recv(
            "C",
            Label::new("from_c"),
            LocalTypeR::send("A", Label::new("to_a"), LocalTypeR::End),
        ),
    );

    let segs = siso_decompose(&mixed).unwrap();
    assert!(!segs.is_empty());
    assert!(orphan_free(&mixed));
    assert!(async_subtype(&mixed, &mixed).is_ok());
}

// ============================================================================
// Tree size properties
// ============================================================================

#[test]
fn test_input_tree_size() {
    let mut runner = TestRunner::new_with_rng(
        Config::default(),
        TestRng::from_seed(RngAlgorithm::ChaCha, &DETERMINISTIC_SEED),
    );

    let strategy = input_tree_strategy();

    for _ in 0..30 {
        let tree = strategy
            .new_tree(&mut runner)
            .expect("Should generate value")
            .current();

        let size = tree.size();

        // Leaf has size 0, nodes have size >= 1
        match &tree {
            InputTree::Leaf => assert_eq!(size, 0),
            InputTree::Node { .. } => assert!(size >= 1),
        }
    }
}

#[test]
fn test_output_tree_size() {
    let mut runner = TestRunner::new_with_rng(
        Config::default(),
        TestRng::from_seed(RngAlgorithm::ChaCha, &DETERMINISTIC_SEED),
    );

    let strategy = output_tree_strategy();

    for _ in 0..30 {
        let tree = strategy
            .new_tree(&mut runner)
            .expect("Should generate value")
            .current();

        let size = tree.size();

        // Leaf has size 0, nodes have size >= 1
        match &tree {
            OutputTree::Leaf => assert_eq!(size, 0),
            OutputTree::Node { .. } => assert!(size >= 1),
        }
    }
}
