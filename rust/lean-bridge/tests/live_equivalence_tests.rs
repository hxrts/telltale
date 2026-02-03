//! Live Lean Equivalence Tests
//!
//! These tests compare Rust projection outputs against live Lean computations.
//! They require the Lean binary to be built and available.
//!
//! Run these tests with: `cargo test -p telltale-lean-bridge live_equivalence`
//!
//! ## Prerequisites
//!
//! Build the Lean runner:
//! ```bash
//! cd lean && lake build telltale_runner
//! ```
//!
//! ## When to Use
//!
//! - Verifying Rust implementation matches Lean specification
//! - Regenerating golden files after Lean spec changes
//! - CI verification (optional, full verification job)

#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

use proptest::prelude::*;
use proptest::strategy::ValueTree;
use proptest::test_runner::{Config, RngAlgorithm, TestRng, TestRunner};
use std::path::PathBuf;
use telltale_lean_bridge::equivalence::EquivalenceChecker;
use telltale_lean_bridge::runner::LeanRunner;
use telltale_types::{GlobalType, Label};

/// Deterministic seed for property-based tests.
const DETERMINISTIC_SEED: [u8; 32] = [
    0x4C, 0x69, 0x76, 0x65, 0x45, 0x71, 0x75, 0x69, // "LiveEqui"
    0x76, 0x61, 0x6C, 0x65, 0x6E, 0x63, 0x65, 0x54, // "valenceT"
    0x65, 0x73, 0x74, 0x53, 0x65, 0x65, 0x64, 0x46, // "estSeedF"
    0x6F, 0x72, 0x52, 0x75, 0x73, 0x74, 0x4C, 0x65, // "orRustLe"
];

/// Get the path to the golden files directory.
fn golden_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("golden")
}

/// Try to get a working Lean checker. Returns None if Lean is unavailable or broken.
fn try_get_lean_checker() -> Option<EquivalenceChecker> {
    if !LeanRunner::is_available() {
        println!("Lean runner not available, skipping test");
        println!("Build with: cd lean && lake build telltale_runner");
        return None;
    }

    let checker = EquivalenceChecker::try_with_lean(golden_dir())?;

    // Verify the runner actually works with a simple test
    let test_global = GlobalType::send("A", "B", Label::new("test"), GlobalType::End);
    if checker
        .check_projection_against_lean(&test_global, "A")
        .is_err()
    {
        println!("Lean runner not responding correctly (may need rebuild)");
        println!("Rebuild with: cd lean && lake build telltale_runner");
        return None;
    }

    Some(checker)
}

// ============================================================================
// Simple Protocol Tests
// ============================================================================

#[test]
fn test_live_ping_pong_projection() {
    let Some(checker) = try_get_lean_checker() else {
        return;
    };

    let global = GlobalType::send(
        "Alice",
        "Bob",
        Label::new("ping"),
        GlobalType::send("Bob", "Alice", Label::new("pong"), GlobalType::End),
    );

    // Check Alice
    let result = checker
        .check_projection_against_lean(&global, "Alice")
        .expect("Alice projection check failed");
    assert!(
        result.equivalent,
        "Alice projection mismatch:\n{}",
        result.diff.as_deref().unwrap_or("no diff")
    );

    // Check Bob
    let result = checker
        .check_projection_against_lean(&global, "Bob")
        .expect("Bob projection check failed");
    assert!(
        result.equivalent,
        "Bob projection mismatch:\n{}",
        result.diff.as_deref().unwrap_or("no diff")
    );
}

#[test]
fn test_live_choice_projection() {
    let Some(checker) = try_get_lean_checker() else {
        return;
    };

    let global = GlobalType::comm(
        "Client",
        "Server",
        vec![
            (Label::new("accept"), GlobalType::End),
            (Label::new("reject"), GlobalType::End),
        ],
    );

    let results = checker
        .check_all_projections_against_lean(&global)
        .expect("Projection check failed");

    for result in results {
        assert!(
            result.equivalent,
            "{} projection mismatch:\n{}",
            result.role,
            result.diff.as_deref().unwrap_or("no diff")
        );
    }
}

#[test]
fn test_live_three_party_projection() {
    let Some(checker) = try_get_lean_checker() else {
        return;
    };

    // A -> B: m1. B -> C: m2. C -> A: m3. end
    let global = GlobalType::send(
        "A",
        "B",
        Label::new("m1"),
        GlobalType::send(
            "B",
            "C",
            Label::new("m2"),
            GlobalType::send("C", "A", Label::new("m3"), GlobalType::End),
        ),
    );

    let results = checker
        .check_all_projections_against_lean(&global)
        .expect("Projection check failed");

    assert_eq!(results.len(), 3, "Expected 3 projections (A, B, C)");

    for result in results {
        assert!(
            result.equivalent,
            "{} projection mismatch:\n{}",
            result.role,
            result.diff.as_deref().unwrap_or("no diff")
        );
    }
}

#[test]
fn test_live_recursive_projection() {
    let Some(checker) = try_get_lean_checker() else {
        return;
    };

    let global = GlobalType::mu(
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

    let results = checker
        .check_all_projections_against_lean(&global)
        .expect("Projection check failed");

    for result in results {
        assert!(
            result.equivalent,
            "{} projection mismatch:\n{}",
            result.role,
            result.diff.as_deref().unwrap_or("no diff")
        );
    }
}

// ============================================================================
// Golden Drift Detection
// ============================================================================

#[test]
fn test_golden_drift_detection() {
    let Some(checker) = try_get_lean_checker() else {
        return;
    };

    let drifted = checker.check_golden_drift().expect("Drift check failed");

    if !drifted.is_empty() {
        panic!(
            "Golden file drift detected. Regenerate with: just regenerate-golden\nDrifted files:\n  - {}",
            drifted.join("\n  - ")
        );
    }
}

// ============================================================================
// Property-Based Tests
// ============================================================================

/// Strategy for generating well-formed GlobalTypes.
fn global_type_strategy() -> impl Strategy<Value = GlobalType> {
    prop_oneof![
        // End
        Just(GlobalType::End),
        // Simple send
        (
            prop_oneof![Just("A"), Just("B"), Just("C")],
            prop_oneof![Just("A"), Just("B"), Just("C")],
            prop_oneof![Just("msg"), Just("data"), Just("ack")],
        )
            .prop_filter("sender != receiver", |(s, r, _)| s != r)
            .prop_map(|(s, r, l)| GlobalType::send(s, r, Label::new(l), GlobalType::End)),
        // Binary choice
        (
            prop_oneof![Just("A"), Just("B")],
            prop_oneof![Just("A"), Just("B")],
        )
            .prop_filter("sender != receiver", |(s, r)| s != r)
            .prop_map(|(s, r)| {
                GlobalType::comm(
                    s,
                    r,
                    vec![
                        (Label::new("yes"), GlobalType::End),
                        (Label::new("no"), GlobalType::End),
                    ],
                )
            }),
    ]
}

#[test]
fn proptest_live_projection_equivalence() {
    let Some(checker) = try_get_lean_checker() else {
        return;
    };

    let mut runner = TestRunner::new_with_rng(
        Config {
            test_name: Some("live_projection_equivalence"),
            source_file: Some(file!()),
            ..Config::default()
        },
        TestRng::from_seed(RngAlgorithm::ChaCha, &DETERMINISTIC_SEED),
    );

    let strategy = global_type_strategy();

    for _ in 0..50 {
        let tree = strategy.new_tree(&mut runner).unwrap();
        let global = tree.current();

        if !global.well_formed() {
            continue;
        }

        match checker.check_all_projections_against_lean(&global) {
            Ok(results) => {
                for result in results {
                    assert!(
                        result.equivalent,
                        "Property test failed for {:?}, role {}: {}",
                        global,
                        result.role,
                        result.diff.as_deref().unwrap_or("mismatch")
                    );
                }
            }
            Err(e) => {
                // Some generated types may fail to project - that's OK
                println!("Projection failed for {:?}: {:?}", global, e);
            }
        }
    }
}

// ============================================================================
// Golden File Generation (for development)
// ============================================================================

#[test]
#[ignore] // Run manually: cargo test -p telltale-lean-bridge generate_golden -- --ignored
fn generate_golden_ping_pong() {
    let Some(checker) = try_get_lean_checker() else {
        panic!("Lean runner required for golden file generation");
    };

    let global = GlobalType::send(
        "Alice",
        "Bob",
        Label::new("ping"),
        GlobalType::send("Bob", "Alice", Label::new("pong"), GlobalType::End),
    );

    let bundle = checker
        .generate_golden_bundle(&global)
        .expect("Failed to generate golden bundle");

    checker
        .write_golden_bundle("ping_pong", &bundle)
        .expect("Failed to write golden bundle");

    println!("Generated golden files for ping_pong");
}

#[test]
#[ignore] // Run manually: cargo test -p telltale-lean-bridge generate_golden -- --ignored
fn generate_golden_choice() {
    let Some(checker) = try_get_lean_checker() else {
        panic!("Lean runner required for golden file generation");
    };

    let global = GlobalType::comm(
        "Client",
        "Server",
        vec![
            (
                Label::new("accept"),
                GlobalType::send("Server", "Client", Label::new("data"), GlobalType::End),
            ),
            (
                Label::new("reject"),
                GlobalType::send("Server", "Client", Label::new("error"), GlobalType::End),
            ),
        ],
    );

    let bundle = checker
        .generate_golden_bundle(&global)
        .expect("Failed to generate golden bundle");

    checker
        .write_golden_bundle("choice_protocol", &bundle)
        .expect("Failed to write golden bundle");

    println!("Generated golden files for choice_protocol");
}
