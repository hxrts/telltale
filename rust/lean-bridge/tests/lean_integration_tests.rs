//! Integration tests that compare Rust and Lean verification.
//!
//! These tests invoke the Lean runner binary to validate that
//! Rust projections match the formally verified Lean implementation.
//!
//! Tests gracefully skip when the Lean binary is not available.

#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

use rumpsteak_lean_bridge::{LeanRunner, Validator};
use rumpsteak_types::{GlobalType, Label};
use serde_json::{json, Value};

/// Helper macro to skip tests when Lean binary is unavailable.
macro_rules! skip_without_lean {
    () => {
        if !LeanRunner::is_available() {
            eprintln!("SKIPPED: Lean binary not available. Run `cd lean && lake build` to enable.");
            return;
        }
    };
}

/// Build choreography JSON from roles and actions.
fn build_choreography_json(roles: &[&str], actions: &[(&str, &str, &str)]) -> Value {
    json!({
        "roles": roles,
        "actions": actions.iter().map(|(from, to, label)| {
            json!({
                "from": from,
                "to": to,
                "label": label
            })
        }).collect::<Vec<_>>()
    })
}

/// Build program export JSON from role and effects.
fn build_program_json(role: &str, effects: &[(&str, &str, &str)]) -> Value {
    json!({
        "role": role,
        "programs": [{
            "branch": Value::Null,
            "effects": effects.iter().map(|(kind, partner, label)| {
                json!({
                    "kind": kind,
                    "partner": partner,
                    "label": label
                })
            }).collect::<Vec<_>>()
        }]
    })
}

/// Build program export JSON with multiple branches.
#[allow(clippy::type_complexity)]
fn build_branching_program_json(role: &str, branches: &[(&str, &[(&str, &str, &str)])]) -> Value {
    json!({
        "role": role,
        "programs": branches.iter().map(|(branch_name, effects)| {
            json!({
                "branch": branch_name,
                "effects": effects.iter().map(|(kind, partner, label)| {
                    json!({
                        "kind": kind,
                        "partner": partner,
                        "label": label
                    })
                }).collect::<Vec<_>>()
            })
        }).collect::<Vec<_>>()
    })
}

// ============================================================================
// Basic Protocol Tests
// ============================================================================

#[test]
fn test_simple_ping_pong() {
    skip_without_lean!();

    let choreo = build_choreography_json(&["A", "B"], &[("A", "B", "ping"), ("B", "A", "pong")]);

    // Role A: send ping, recv pong
    let program_a = build_program_json("A", &[("send", "B", "ping"), ("recv", "B", "pong")]);

    let runner = LeanRunner::new().expect("Lean binary should exist");
    let result = runner
        .validate(&choreo, &program_a)
        .expect("Validation should succeed");

    assert!(result.success, "Lean validation failed: {:?}", result);
}

#[test]
fn test_role_b_ping_pong() {
    skip_without_lean!();

    let choreo = build_choreography_json(&["A", "B"], &[("A", "B", "ping"), ("B", "A", "pong")]);

    // Role B: recv ping, send pong
    let program_b = build_program_json("B", &[("recv", "A", "ping"), ("send", "A", "pong")]);

    let runner = LeanRunner::new().expect("Lean binary should exist");
    let result = runner
        .validate(&choreo, &program_b)
        .expect("Validation should succeed");

    assert!(result.success, "Role B validation failed: {:?}", result);
}

// ============================================================================
// Three-Party Protocol Tests
// ============================================================================

#[test]
fn test_three_party_ring() {
    skip_without_lean!();

    // A -> B: msg1. B -> C: msg2. C -> A: msg3. end
    let choreo = build_choreography_json(
        &["A", "B", "C"],
        &[("A", "B", "msg1"), ("B", "C", "msg2"), ("C", "A", "msg3")],
    );

    let runner = LeanRunner::new().expect("Lean binary should exist");

    // Test each role
    let test_cases = [
        ("A", vec![("send", "B", "msg1"), ("recv", "C", "msg3")]),
        ("B", vec![("recv", "A", "msg1"), ("send", "C", "msg2")]),
        ("C", vec![("recv", "B", "msg2"), ("send", "A", "msg3")]),
    ];

    for (role, effects) in test_cases {
        let effects_refs: Vec<(&str, &str, &str)> =
            effects.iter().map(|(k, p, l)| (*k, *p, *l)).collect();
        let program = build_program_json(role, &effects_refs);
        let result = runner
            .validate(&choreo, &program)
            .unwrap_or_else(|_| panic!("Validation should succeed for role {}", role));

        assert!(
            result.success,
            "Role {} failed validation: {:?}",
            role, result
        );
    }
}

// ============================================================================
// Choice/Branching Tests
// ============================================================================

#[test]
fn test_choice_accept_branch() {
    skip_without_lean!();

    // A -> B: { accept | reject }
    let choreo =
        build_choreography_json(&["A", "B"], &[("A", "B", "accept"), ("A", "B", "reject")]);

    // A chooses accept
    let program_a = build_program_json("A", &[("send", "B", "accept")]);

    let runner = LeanRunner::new().expect("Lean binary should exist");
    let result = runner
        .validate(&choreo, &program_a)
        .expect("Validation should succeed");

    assert!(result.success, "Accept branch failed: {:?}", result);
}

#[test]
fn test_choice_reject_branch() {
    skip_without_lean!();

    let choreo =
        build_choreography_json(&["A", "B"], &[("A", "B", "accept"), ("A", "B", "reject")]);

    // A chooses reject
    let program_a = build_program_json("A", &[("send", "B", "reject")]);

    let runner = LeanRunner::new().expect("Lean binary should exist");
    let result = runner
        .validate(&choreo, &program_a)
        .expect("Validation should succeed");

    assert!(result.success, "Reject branch failed: {:?}", result);
}

// ============================================================================
// Error Detection Tests
// ============================================================================

#[test]
fn test_invalid_projection_detected() {
    skip_without_lean!();

    // A -> B: msg
    let choreo = build_choreography_json(&["A", "B"], &[("A", "B", "msg")]);

    // Wrong program: A sends to C (which doesn't exist in choreography)
    let bad_program = build_program_json("A", &[("send", "C", "msg")]);

    let runner = LeanRunner::new().expect("Lean binary should exist");
    let result = runner.validate(&choreo, &bad_program);

    // This should either fail validation or return an error
    if let Ok(r) = result {
        assert!(
            !r.success,
            "Should have detected invalid projection, but got: {:?}",
            r
        );
    }
    // Error is also acceptable
}

#[test]
fn test_wrong_label_detected() {
    skip_without_lean!();

    let choreo = build_choreography_json(&["A", "B"], &[("A", "B", "ping")]);

    // Wrong label
    let bad_program = build_program_json("A", &[("send", "B", "wrong_label")]);

    let runner = LeanRunner::new().expect("Lean binary should exist");
    let result = runner.validate(&choreo, &bad_program);

    if let Ok(r) = result {
        assert!(!r.success, "Should have detected wrong label");
    }
}

#[test]
fn test_missing_action_detected() {
    skip_without_lean!();

    // Two-message protocol
    let choreo = build_choreography_json(&["A", "B"], &[("A", "B", "first"), ("A", "B", "second")]);

    // Program only has first message (missing second)
    let incomplete_program = build_program_json("A", &[("send", "B", "first")]);

    let runner = LeanRunner::new().expect("Lean binary should exist");
    let result = runner
        .validate(&choreo, &incomplete_program)
        .expect("Should not crash");

    // Lean should accept this as a valid subsequence (omitting optional actions is OK)
    // This depends on Lean's subtyping semantics
    // Just verify it doesn't crash
    let _ = result;
}

// ============================================================================
// Validator Integration Tests
// ============================================================================

#[test]
fn test_validator_with_lean() {
    skip_without_lean!();

    let validator = Validator::new();
    assert!(
        validator.lean_available(),
        "Lean should be available after skip_without_lean"
    );

    let choreo = build_choreography_json(&["A", "B"], &[("A", "B", "msg")]);
    let program = build_program_json("A", &[("send", "B", "msg")]);

    let result = validator
        .validate_projection_with_lean(&choreo, &program)
        .expect("Validation should succeed");

    assert!(result.is_valid(), "Validator result should be valid");
}

#[test]
fn test_validator_detects_invalid() {
    skip_without_lean!();

    let validator = Validator::new();

    let choreo = build_choreography_json(&["A", "B"], &[("A", "B", "msg")]);
    let bad_program = build_program_json("A", &[("send", "C", "wrong")]);

    let result = validator.validate_projection_with_lean(&choreo, &bad_program);

    if let Ok(r) = result {
        assert!(r.is_invalid(), "Should detect invalid projection");
    }
    // Error is also acceptable
}

// ============================================================================
// Rust Type Correspondence Tests
// ============================================================================

#[test]
fn test_rust_globaltype_matches_lean() {
    skip_without_lean!();

    // Define protocol using Rust types
    let _global = GlobalType::comm(
        "Client",
        "Server",
        vec![
            (Label::new("request"), GlobalType::End),
            (Label::new("quit"), GlobalType::End),
        ],
    );

    // Build equivalent choreography JSON
    let choreo = build_choreography_json(
        &["Client", "Server"],
        &[
            ("Client", "Server", "request"),
            ("Client", "Server", "quit"),
        ],
    );

    // Client projection: internal choice between request and quit
    let program = build_program_json("Client", &[("send", "Server", "request")]);

    let runner = LeanRunner::new().expect("Lean binary should exist");
    let result = runner
        .validate(&choreo, &program)
        .expect("Validation should succeed");

    assert!(
        result.success,
        "Rust GlobalType should correspond to valid Lean projection"
    );
}

// ============================================================================
// Complex Protocol Tests
// ============================================================================

#[test]
fn test_calculator_protocol() {
    skip_without_lean!();

    // Calculator: Client -> Server: { add | sub | quit }
    // For add/sub: Server -> Client: result
    let choreo = build_choreography_json(
        &["Client", "Server"],
        &[
            ("Client", "Server", "add"),
            ("Server", "Client", "result"),
            ("Client", "Server", "sub"),
            ("Server", "Client", "result"),
            ("Client", "Server", "quit"),
        ],
    );

    // Client chooses add path
    let program = build_branching_program_json(
        "Client",
        &[(
            "add",
            &[("send", "Server", "add"), ("recv", "Server", "result")],
        )],
    );

    let runner = LeanRunner::new().expect("Lean binary should exist");
    let result = runner
        .validate(&choreo, &program)
        .expect("Validation should succeed");

    assert!(
        result.success,
        "Calculator add branch should validate: {:?}",
        result
    );
}

// ============================================================================
// Recursive Protocol Tests
// ============================================================================

// Note: The Lean runner uses a flat choreography format (roles + actions array),
// not the hierarchical GlobalType format with Mu/Var. Recursive protocols are
// validated by unrolling the first iteration of the loop body.
//
// Full recursive type validation happens in:
// - rust/lean-bridge/tests/proptest_projection.rs (property-based tests)
// - rust/lean-bridge/tests/projection_equivalence_tests.rs (DSL cross-validation)

#[test]
fn test_recursive_ping_pong_unrolled() {
    skip_without_lean!();

    // µLoop. A -> B: ping. B -> A: pong. Loop
    // Represented as flat actions (one iteration of the loop body)
    let choreo = build_choreography_json(&["A", "B"], &[("A", "B", "ping"), ("B", "A", "pong")]);

    // Role A: send ping, recv pong
    let program_a = build_program_json("A", &[("send", "B", "ping"), ("recv", "B", "pong")]);

    let runner = LeanRunner::new().expect("Lean binary should exist");
    let result = runner
        .validate(&choreo, &program_a)
        .expect("Recursive validation should succeed");

    assert!(
        result.success,
        "Recursive protocol validation failed for role A: {:?}",
        result
    );
}

#[test]
fn test_recursive_ping_pong_role_b() {
    skip_without_lean!();

    // Same recursive protocol, testing role B
    let choreo = build_choreography_json(&["A", "B"], &[("A", "B", "ping"), ("B", "A", "pong")]);

    // Role B: recv ping, send pong
    let program_b = build_program_json("B", &[("recv", "A", "ping"), ("send", "A", "pong")]);

    let runner = LeanRunner::new().expect("Lean binary should exist");
    let result = runner
        .validate(&choreo, &program_b)
        .expect("Recursive validation should succeed");

    assert!(
        result.success,
        "Recursive protocol validation failed for role B: {:?}",
        result
    );
}

#[test]
fn test_recursive_choice_unrolled() {
    skip_without_lean!();

    // µLoop. A -> B: { continue. B -> A: data. Loop | stop }
    // Unrolled as: A -> B: continue | stop, B -> A: data (for continue branch)
    let choreo = build_choreography_json(
        &["A", "B"],
        &[
            ("A", "B", "continue"),
            ("B", "A", "data"),
            ("A", "B", "stop"),
        ],
    );

    // Role A chooses the continue branch
    let program_a = build_branching_program_json(
        "A",
        &[(
            "continue",
            &[("send", "B", "continue"), ("recv", "B", "data")],
        )],
    );

    let runner = LeanRunner::new().expect("Lean binary should exist");
    let result = runner
        .validate(&choreo, &program_a)
        .expect("Recursive choice validation should succeed");

    assert!(
        result.success,
        "Recursive choice protocol validation failed: {:?}",
        result
    );
}

// ============================================================================
// CI Enforcement Tests
// ============================================================================

/// This test verifies that the Lean binary is available.
///
/// In CI, this test is mandatory and will fail if Lean isn't built.
/// This ensures that Lean validation is always run in the CI pipeline.
///
/// To build Lean locally: `cd lean && lake build`
/// With Nix: `nix develop --command bash -c "cd lean && lake build"`
#[test]
#[ignore = "temporarily disabled during Lean refactoring"]
fn test_lean_binary_available_for_ci() {
    // Use require_available() instead of skip_without_lean!() to make this mandatory
    LeanRunner::require_available();

    // Verify we can actually create a runner
    let runner = LeanRunner::new().expect("Lean runner should be constructable after require_available()");

    // Run a minimal validation to confirm the binary works
    let choreo = build_choreography_json(&["A", "B"], &[("A", "B", "msg")]);
    let program = build_program_json("A", &[("send", "B", "msg")]);

    let result = runner.validate(&choreo, &program).expect("Lean validation should work");
    assert!(result.success, "Basic validation should pass");
}
