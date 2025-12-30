//! Deterministic property-based tests for JSON round-tripping.
//!
//! These tests verify that GlobalType and LocalTypeR values can be
//! serialized to JSON and parsed back without loss of information.
//!
//! All tests use fixed seeds for full reproducibility.

#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

use proptest::prelude::*;
use proptest::strategy::ValueTree;
use proptest::test_runner::{Config, RngAlgorithm, TestRng, TestRunner};
use rumpsteak_lean_bridge::{global_to_json, json_to_global, json_to_local, local_to_json};
use rumpsteak_types::{GlobalType, Label, LocalTypeR, PayloadSort};

/// Deterministic seed for property-based tests.
/// Using a fixed seed ensures all proptest runs are reproducible.
const DETERMINISTIC_SEED: [u8; 32] = [
    0x52, 0x75, 0x6D, 0x70, 0x73, 0x74, 0x65, 0x61, // "Rumpstea"
    0x6B, 0x41, 0x75, 0x72, 0x61, 0x4C, 0x65, 0x61, // "kAuraLea"
    0x6E, 0x42, 0x72, 0x69, 0x64, 0x67, 0x65, 0x54, // "nBridgeT"
    0x65, 0x73, 0x74, 0x53, 0x65, 0x65, 0x64, 0x21, // "estSeed!"
];

/// Deterministic proptest config.
fn deterministic_config() -> Config {
    Config {
        // Run enough cases to be meaningful
        cases: 100,
        // Fail fast for debugging
        max_shrink_iters: 100,
        ..Config::default()
    }
}

/// Strategy for generating role names.
/// Uses a fixed set to avoid unbounded string generation.
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
/// Uses a fixed set with various payload sorts.
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
        Just(Label::with_sort("text", PayloadSort::String)),
    ]
}

/// Strategy for generating simple (non-recursive) GlobalTypes.
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

/// Strategy for generating simple (non-recursive) LocalTypes.
fn simple_local_strategy() -> impl Strategy<Value = LocalTypeR> {
    prop_oneof![
        // End type
        Just(LocalTypeR::End),
        // Single send
        (role_strategy(), label_strategy()).prop_map(|(p, l)| LocalTypeR::send(
            &p,
            l,
            LocalTypeR::End
        )),
        // Single recv
        (role_strategy(), label_strategy()).prop_map(|(p, l)| LocalTypeR::recv(
            &p,
            l,
            LocalTypeR::End
        )),
        // Send then recv
        (
            role_strategy(),
            label_strategy(),
            role_strategy(),
            label_strategy()
        )
            .prop_map(|(p1, l1, p2, l2)| {
                LocalTypeR::send(&p1, l1, LocalTypeR::recv(&p2, l2, LocalTypeR::End))
            }),
        // Internal choice (send with multiple branches)
        (role_strategy(), label_strategy(), label_strategy())
            .prop_filter("distinct labels", |(_, l1, l2)| l1.name != l2.name)
            .prop_map(|(p, l1, l2)| {
                LocalTypeR::Send {
                    partner: p,
                    branches: vec![(l1, LocalTypeR::End), (l2, LocalTypeR::End)],
                }
            }),
    ]
}

proptest! {
    #![proptest_config(deterministic_config())]

    /// Property: GlobalType JSON round-trip preserves structure.
    #[test]
    fn global_json_roundtrip(g in simple_global_strategy()) {
        let json = global_to_json(&g);
        let parsed = json_to_global(&json).expect("Should parse back");
        prop_assert_eq!(g, parsed, "Round-trip should preserve structure");
    }

    /// Property: LocalTypeR JSON round-trip preserves structure.
    #[test]
    fn local_json_roundtrip(lt in simple_local_strategy()) {
        let json = local_to_json(&lt);
        let parsed = json_to_local(&json).expect("Should parse back");
        prop_assert_eq!(lt, parsed, "Round-trip should preserve structure");
    }

    /// Property: Generated GlobalTypes are well-formed.
    #[test]
    fn generated_globals_well_formed(g in simple_global_strategy()) {
        prop_assert!(g.well_formed(), "Generated type should be well-formed");
    }

    /// Property: Generated LocalTypes are well-formed.
    #[test]
    fn generated_locals_well_formed(lt in simple_local_strategy()) {
        prop_assert!(lt.well_formed(), "Generated type should be well-formed");
    }

    /// Property: JSON export produces valid JSON with required fields.
    #[test]
    fn global_json_has_required_fields(g in simple_global_strategy()) {
        let json = global_to_json(&g);
        prop_assert!(json.get("kind").is_some(), "JSON must have 'kind' field");
    }

    /// Property: Well-formed simple types have no free variables.
    #[test]
    fn no_free_vars_in_generated(g in simple_global_strategy()) {
        prop_assert!(g.free_vars().is_empty(), "Simple types have no free vars");
    }
}

/// Tests with explicit seeds for maximum reproducibility.
#[cfg(test)]
mod seeded_tests {
    use super::*;

    #[test]
    fn reproducible_global_roundtrip() {
        let mut runner = TestRunner::new_with_rng(
            Config::default(),
            TestRng::from_seed(RngAlgorithm::ChaCha, &DETERMINISTIC_SEED),
        );

        let strategy = simple_global_strategy();

        // Generate 50 test cases with same seed
        for i in 0..50 {
            let value = strategy
                .new_tree(&mut runner)
                .expect("Should generate value")
                .current();

            let json = global_to_json(&value);
            let parsed = json_to_global(&json).expect("Should parse");

            assert_eq!(value, parsed, "Case {} failed round-trip", i);
        }
    }

    #[test]
    fn reproducible_local_roundtrip() {
        let mut runner = TestRunner::new_with_rng(
            Config::default(),
            TestRng::from_seed(RngAlgorithm::ChaCha, &DETERMINISTIC_SEED),
        );

        let strategy = simple_local_strategy();

        for i in 0..50 {
            let value = strategy
                .new_tree(&mut runner)
                .expect("Should generate value")
                .current();

            let json = local_to_json(&value);
            let parsed = json_to_local(&json).expect("Should parse");

            assert_eq!(value, parsed, "Case {} failed round-trip", i);
        }
    }

    /// Verify that running twice with same seed produces same sequence.
    #[test]
    fn seed_produces_deterministic_sequence() {
        // First run
        let mut runner1 = TestRunner::new_with_rng(
            Config::default(),
            TestRng::from_seed(RngAlgorithm::ChaCha, &DETERMINISTIC_SEED),
        );
        let strategy = simple_global_strategy();
        let first_run: Vec<GlobalType> = (0..10)
            .map(|_| {
                strategy
                    .new_tree(&mut runner1)
                    .expect("Should generate")
                    .current()
            })
            .collect();

        // Second run with same seed
        let mut runner2 = TestRunner::new_with_rng(
            Config::default(),
            TestRng::from_seed(RngAlgorithm::ChaCha, &DETERMINISTIC_SEED),
        );
        let second_run: Vec<GlobalType> = (0..10)
            .map(|_| {
                strategy
                    .new_tree(&mut runner2)
                    .expect("Should generate")
                    .current()
            })
            .collect();

        assert_eq!(
            first_run, second_run,
            "Same seed must produce same sequence"
        );
    }
}

/// Tests for recursive types.
#[cfg(test)]
mod recursive_tests {
    use super::*;

    #[test]
    fn recursive_global_roundtrip() {
        let g = GlobalType::mu(
            "X",
            GlobalType::comm("A", "B", vec![(Label::new("ping"), GlobalType::var("X"))]),
        );

        let json = global_to_json(&g);
        let parsed = json_to_global(&json).expect("Should parse recursive type");
        assert_eq!(g, parsed);
    }

    #[test]
    fn recursive_local_roundtrip() {
        let lt = LocalTypeR::mu(
            "X",
            LocalTypeR::send("B", Label::new("ping"), LocalTypeR::var("X")),
        );

        let json = local_to_json(&lt);
        let parsed = json_to_local(&json).expect("Should parse recursive type");
        assert_eq!(lt, parsed);
    }

    #[test]
    fn nested_recursive_roundtrip() {
        let g = GlobalType::mu(
            "Outer",
            GlobalType::comm(
                "A",
                "B",
                vec![(
                    Label::new("start"),
                    GlobalType::mu(
                        "Inner",
                        GlobalType::comm(
                            "B",
                            "A",
                            vec![
                                (Label::new("continue"), GlobalType::var("Inner")),
                                (Label::new("done"), GlobalType::var("Outer")),
                            ],
                        ),
                    ),
                )],
            ),
        );

        let json = global_to_json(&g);
        let parsed = json_to_global(&json).expect("Should parse nested recursive type");
        assert_eq!(g, parsed);
    }
}
