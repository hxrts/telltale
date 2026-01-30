//! Golden File Equivalence Tests
//!
//! These tests compare Rust projection outputs against pre-computed Lean outputs
//! stored as golden files. This enables fast CI without requiring the Lean runtime.
//!
//! Golden files are generated from Lean using `cargo run -p telltale-lean-bridge --bin golden`
//! and should be regenerated when the Lean specification changes.
//!
//! ## Directory Structure
//!
//! ```text
//! golden/
//!   projection/
//!     ping_pong/
//!       input.json           # GlobalType
//!       Alice.expected.json  # Lean's projection for Alice
//!       Bob.expected.json    # Lean's projection for Bob
//!     choice_protocol/
//!       ...
//! ```

#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

use telltale_lean_bridge::equivalence::EquivalenceChecker;
use telltale_lean_bridge::import::json_to_global;
use std::path::PathBuf;

/// Get the path to the golden files directory.
fn golden_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("golden")
}

/// Load a GlobalType from a golden input file.
fn load_input(test_name: &str) -> telltale_types::GlobalType {
    let path = golden_dir()
        .join("projection")
        .join(test_name)
        .join("input.json");
    let content =
        std::fs::read_to_string(&path).unwrap_or_else(|_| panic!("Failed to read {:?}", path));
    let json: serde_json::Value = serde_json::from_str(&content).expect("Failed to parse JSON");
    json_to_global(&json).expect("Failed to convert to GlobalType")
}

// ============================================================================
// Ping-Pong Protocol Tests
// ============================================================================

#[test]
fn test_ping_pong_alice_projection() {
    let checker = EquivalenceChecker::with_golden_dir(golden_dir());
    let global = load_input("ping_pong");

    let result = checker
        .check_projection_against_golden("ping_pong", &global, "Alice")
        .expect("Projection check failed");

    assert!(
        result.equivalent,
        "Alice projection mismatch:\n{}",
        result.diff.as_deref().unwrap_or("no diff")
    );
}

#[test]
fn test_ping_pong_bob_projection() {
    let checker = EquivalenceChecker::with_golden_dir(golden_dir());
    let global = load_input("ping_pong");

    let result = checker
        .check_projection_against_golden("ping_pong", &global, "Bob")
        .expect("Projection check failed");

    assert!(
        result.equivalent,
        "Bob projection mismatch:\n{}",
        result.diff.as_deref().unwrap_or("no diff")
    );
}

#[test]
fn test_ping_pong_all_projections() {
    let checker = EquivalenceChecker::with_golden_dir(golden_dir());
    let global = load_input("ping_pong");

    let results = checker
        .check_all_projections_against_golden("ping_pong", &global)
        .expect("All projections check failed");

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
// Choice Protocol Tests
// ============================================================================

#[test]
fn test_choice_protocol_client_projection() {
    let checker = EquivalenceChecker::with_golden_dir(golden_dir());
    let global = load_input("choice_protocol");

    let result = checker
        .check_projection_against_golden("choice_protocol", &global, "Client")
        .expect("Projection check failed");

    assert!(
        result.equivalent,
        "Client projection mismatch:\n{}",
        result.diff.as_deref().unwrap_or("no diff")
    );
}

#[test]
fn test_choice_protocol_server_projection() {
    let checker = EquivalenceChecker::with_golden_dir(golden_dir());
    let global = load_input("choice_protocol");

    let result = checker
        .check_projection_against_golden("choice_protocol", &global, "Server")
        .expect("Projection check failed");

    assert!(
        result.equivalent,
        "Server projection mismatch:\n{}",
        result.diff.as_deref().unwrap_or("no diff")
    );
}

#[test]
fn test_choice_protocol_all_projections() {
    let checker = EquivalenceChecker::with_golden_dir(golden_dir());
    let global = load_input("choice_protocol");

    let results = checker
        .check_all_projections_against_golden("choice_protocol", &global)
        .expect("All projections check failed");

    assert_eq!(results.len(), 2, "Expected 2 projections (Client, Server)");

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
// All Golden Files Test
// ============================================================================

/// Test all golden files in the projection directory.
#[test]
fn test_all_golden_projections() {
    let checker = EquivalenceChecker::with_golden_dir(golden_dir());
    let projection_dir = golden_dir().join("projection");

    if !projection_dir.exists() {
        println!("No golden files found, skipping test");
        return;
    }

    let mut failures = Vec::new();

    for entry in std::fs::read_dir(&projection_dir).expect("Failed to read projection dir") {
        let entry = entry.expect("Failed to read entry");
        if !entry.file_type().unwrap().is_dir() {
            continue;
        }

        let test_name = entry.file_name().to_string_lossy().to_string();
        let input_path = entry.path().join("input.json");

        if !input_path.exists() {
            println!("Skipping {} (no input.json)", test_name);
            continue;
        }

        let global = load_input(&test_name);

        match checker.check_all_projections_against_golden(&test_name, &global) {
            Ok(results) => {
                for result in results {
                    if !result.equivalent {
                        failures.push(format!(
                            "{}:{} - {}",
                            test_name,
                            result.role,
                            result.diff.as_deref().unwrap_or("mismatch")
                        ));
                    }
                }
            }
            Err(e) => {
                failures.push(format!("{}: {:?}", test_name, e));
            }
        }
    }

    if !failures.is_empty() {
        panic!(
            "Golden file equivalence failures:\n{}",
            failures.join("\n\n")
        );
    }
}
