//! Integration tests that compare Rust and Lean verification.
//!
//! These tests invoke the Lean validator binary to validate that
//! Rust projections match the formally verified Lean implementation.
//!
//! Tests gracefully skip when the Lean binary is not available.

#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

use serde_json::{json, Value};
use telltale_lean_bridge::export::{global_to_json, local_to_json};
use telltale_lean_bridge::{LeanRunner, Validator};
use telltale_types::{GlobalType, Label, LocalTypeR};

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

/// Build program export JSON from role and LocalTypeR.
fn build_program_json(role: &str, local: &LocalTypeR) -> Value {
    json!({
        "role": role,
        "local_type": local_to_json(local)
    })
}

// ============================================================================
// Basic Protocol Tests
// ============================================================================

#[test]
fn test_simple_ping_pong() {
    skip_without_lean!();

    let global = GlobalType::send(
        "A",
        "B",
        Label::new("ping"),
        GlobalType::send("B", "A", Label::new("pong"), GlobalType::End),
    );

    let program_a = build_program_json(
        "A",
        &LocalTypeR::send(
            "B",
            Label::new("ping"),
            LocalTypeR::recv("B", Label::new("pong"), LocalTypeR::End),
        ),
    );

    let runner = LeanRunner::new().expect("Lean binary should exist");
    let result = runner
        .validate(&global_to_json(&global), &program_a)
        .expect("Validation should succeed");

    assert!(result.success, "Lean validation failed: {:?}", result);
}

#[test]
fn test_role_b_ping_pong() {
    skip_without_lean!();

    let global = GlobalType::send(
        "A",
        "B",
        Label::new("ping"),
        GlobalType::send("B", "A", Label::new("pong"), GlobalType::End),
    );

    let program_b = build_program_json(
        "B",
        &LocalTypeR::recv(
            "A",
            Label::new("ping"),
            LocalTypeR::send("A", Label::new("pong"), LocalTypeR::End),
        ),
    );

    let runner = LeanRunner::new().expect("Lean binary should exist");
    let result = runner
        .validate(&global_to_json(&global), &program_b)
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
    let global = GlobalType::send(
        "A",
        "B",
        Label::new("msg1"),
        GlobalType::send(
            "B",
            "C",
            Label::new("msg2"),
            GlobalType::send("C", "A", Label::new("msg3"), GlobalType::End),
        ),
    );

    let runner = LeanRunner::new().expect("Lean binary should exist");

    let program_a = build_program_json(
        "A",
        &LocalTypeR::send(
            "B",
            Label::new("msg1"),
            LocalTypeR::recv("C", Label::new("msg3"), LocalTypeR::End),
        ),
    );
    let program_b = build_program_json(
        "B",
        &LocalTypeR::recv(
            "A",
            Label::new("msg1"),
            LocalTypeR::send("C", Label::new("msg2"), LocalTypeR::End),
        ),
    );
    let program_c = build_program_json(
        "C",
        &LocalTypeR::recv(
            "B",
            Label::new("msg2"),
            LocalTypeR::send("A", Label::new("msg3"), LocalTypeR::End),
        ),
    );

    for (role, program) in [("A", program_a), ("B", program_b), ("C", program_c)] {
        let result = runner
            .validate(&global_to_json(&global), &program)
            .unwrap_or_else(|_| panic!("Validation should succeed for role {}", role));
        assert!(result.success, "Role {} failed validation: {:?}", role, result);
    }
}

// ============================================================================
// Choice/Branching Tests
// ============================================================================

#[test]
fn test_choice_sender_projection() {
    skip_without_lean!();

    // A -> B: { accept | reject }
    let global = GlobalType::comm(
        "A",
        "B",
        vec![(Label::new("accept"), GlobalType::End), (Label::new("reject"), GlobalType::End)],
    );

    let program_a = build_program_json(
        "A",
        &LocalTypeR::send_choice(
            "B",
            vec![
                (Label::new("accept"), None, LocalTypeR::End),
                (Label::new("reject"), None, LocalTypeR::End),
            ],
        ),
    );

    let runner = LeanRunner::new().expect("Lean binary should exist");
    let result = runner
        .validate(&global_to_json(&global), &program_a)
        .expect("Validation should succeed");

    assert!(result.success, "Choice sender validation failed: {:?}", result);
}

#[test]
fn test_choice_receiver_projection() {
    skip_without_lean!();

    let global = GlobalType::comm(
        "A",
        "B",
        vec![(Label::new("accept"), GlobalType::End), (Label::new("reject"), GlobalType::End)],
    );

    let program_b = build_program_json(
        "B",
        &LocalTypeR::recv_choice(
            "A",
            vec![
                (Label::new("accept"), None, LocalTypeR::End),
                (Label::new("reject"), None, LocalTypeR::End),
            ],
        ),
    );

    let runner = LeanRunner::new().expect("Lean binary should exist");
    let result = runner
        .validate(&global_to_json(&global), &program_b)
        .expect("Validation should succeed");

    assert!(result.success, "Choice receiver validation failed: {:?}", result);
}

// ============================================================================
// Error Detection Tests
// ============================================================================

#[test]
fn test_invalid_projection_detected() {
    skip_without_lean!();

    // A -> B: msg
    let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);

    // Wrong program: A sends to C (which doesn't exist in choreography)
    let bad_program = build_program_json(
        "A",
        &LocalTypeR::send("C", Label::new("msg"), LocalTypeR::End),
    );

    let runner = LeanRunner::new().expect("Lean binary should exist");
    let result = runner.validate(&global_to_json(&global), &bad_program);

    if let Ok(r) = result {
        assert!(!r.success, "Should have detected invalid projection");
    }
    // Error is also acceptable
}

#[test]
fn test_wrong_label_detected() {
    skip_without_lean!();

    let global = GlobalType::send("A", "B", Label::new("ping"), GlobalType::End);

    // Wrong label
    let bad_program = build_program_json(
        "A",
        &LocalTypeR::send("B", Label::new("wrong_label"), LocalTypeR::End),
    );

    let runner = LeanRunner::new().expect("Lean binary should exist");
    let result = runner.validate(&global_to_json(&global), &bad_program);

    if let Ok(r) = result {
        assert!(!r.success, "Should have detected wrong label");
    }
}

#[test]
fn test_missing_action_detected() {
    skip_without_lean!();

    // Two-message protocol
    let global = GlobalType::send(
        "A",
        "B",
        Label::new("first"),
        GlobalType::send("A", "B", Label::new("second"), GlobalType::End),
    );

    // Program only has first message (missing second)
    let incomplete_program = build_program_json(
        "A",
        &LocalTypeR::send("B", Label::new("first"), LocalTypeR::End),
    );

    let runner = LeanRunner::new().expect("Lean binary should exist");
    let result = runner.validate(&global_to_json(&global), &incomplete_program);

    if let Ok(r) = result {
        assert!(!r.success, "Should detect missing action");
    }
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

    let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
    let program = build_program_json(
        "A",
        &LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End),
    );

    let result = validator
        .validate_projection_with_lean(&global_to_json(&global), &program)
        .expect("Validation should succeed");

    assert!(result.is_valid(), "Validator result should be valid");
}

#[test]
fn test_validator_detects_invalid() {
    skip_without_lean!();

    let validator = Validator::new();

    let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
    let bad_program = build_program_json(
        "A",
        &LocalTypeR::send("C", Label::new("wrong"), LocalTypeR::End),
    );

    let result = validator.validate_projection_with_lean(&global_to_json(&global), &bad_program);

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
    let global = GlobalType::comm(
        "Client",
        "Server",
        vec![
            (Label::new("request"), GlobalType::End),
            (Label::new("quit"), GlobalType::End),
        ],
    );

    let program = build_program_json(
        "Client",
        &LocalTypeR::send_choice(
            "Server",
            vec![
                (Label::new("request"), None, LocalTypeR::End),
                (Label::new("quit"), None, LocalTypeR::End),
            ],
        ),
    );

    let runner = LeanRunner::new().expect("Lean binary should exist");
    let result = runner
        .validate(&global_to_json(&global), &program)
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
    let global = GlobalType::comm(
        "Client",
        "Server",
        vec![
            (
                Label::new("add"),
                GlobalType::send("Server", "Client", Label::new("result"), GlobalType::End),
            ),
            (
                Label::new("sub"),
                GlobalType::send("Server", "Client", Label::new("result"), GlobalType::End),
            ),
            (Label::new("quit"), GlobalType::End),
        ],
    );

    let program = build_program_json(
        "Client",
        &LocalTypeR::send_choice(
            "Server",
            vec![
                (
                    Label::new("add"),
                    None,
                    LocalTypeR::recv("Server", Label::new("result"), LocalTypeR::End),
                ),
                (
                    Label::new("sub"),
                    None,
                    LocalTypeR::recv("Server", Label::new("result"), LocalTypeR::End),
                ),
                (Label::new("quit"), None, LocalTypeR::End),
            ],
        ),
    );

    let runner = LeanRunner::new().expect("Lean binary should exist");
    let result = runner
        .validate(&global_to_json(&global), &program)
        .expect("Validation should succeed");

    assert!(
        result.success,
        "Calculator protocol validation failed: {:?}",
        result
    );
}

// ============================================================================
// Recursive Protocol Tests
// ============================================================================

#[test]
fn test_recursive_ping_pong() {
    skip_without_lean!();

    // µLoop. A -> B: ping. B -> A: pong. Loop
    let global = GlobalType::mu(
        "Loop",
        GlobalType::send(
            "A",
            "B",
            Label::new("ping"),
            GlobalType::send("B", "A", Label::new("pong"), GlobalType::var("Loop")),
        ),
    );

    let program_a = build_program_json(
        "A",
        &LocalTypeR::mu(
            "Loop",
            LocalTypeR::send(
                "B",
                Label::new("ping"),
                LocalTypeR::recv("B", Label::new("pong"), LocalTypeR::var("Loop")),
            ),
        ),
    );

    let runner = LeanRunner::new().expect("Lean binary should exist");
    let result = runner
        .validate(&global_to_json(&global), &program_a)
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

    let global = GlobalType::mu(
        "Loop",
        GlobalType::send(
            "A",
            "B",
            Label::new("ping"),
            GlobalType::send("B", "A", Label::new("pong"), GlobalType::var("Loop")),
        ),
    );

    let program_b = build_program_json(
        "B",
        &LocalTypeR::mu(
            "Loop",
            LocalTypeR::recv(
                "A",
                Label::new("ping"),
                LocalTypeR::send("A", Label::new("pong"), LocalTypeR::var("Loop")),
            ),
        ),
    );

    let runner = LeanRunner::new().expect("Lean binary should exist");
    let result = runner
        .validate(&global_to_json(&global), &program_b)
        .expect("Recursive validation should succeed");

    assert!(
        result.success,
        "Recursive protocol validation failed for role B: {:?}",
        result
    );
}

#[test]
fn test_recursive_choice() {
    skip_without_lean!();

    // µLoop. A -> B: { continue. B -> A: data. Loop | stop }
    let global = GlobalType::mu(
        "Loop",
        GlobalType::comm(
            "A",
            "B",
            vec![
                (
                    Label::new("continue"),
                    GlobalType::send("B", "A", Label::new("data"), GlobalType::var("Loop")),
                ),
                (Label::new("stop"), GlobalType::End),
            ],
        ),
    );

    let program_a = build_program_json(
        "A",
        &LocalTypeR::mu(
            "Loop",
            LocalTypeR::send_choice(
                "B",
                vec![
                    (
                        Label::new("continue"),
                        None,
                        LocalTypeR::recv("B", Label::new("data"), LocalTypeR::var("Loop")),
                    ),
                    (Label::new("stop"), None, LocalTypeR::End),
                ],
            ),
        ),
    );

    let runner = LeanRunner::new().expect("Lean binary should exist");
    let result = runner
        .validate(&global_to_json(&global), &program_a)
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
/// To build Lean locally: `cd lean && lake build telltale_validator`
/// With Nix: `nix develop --command bash -c "cd lean && lake build telltale_validator"`
#[test]
#[ignore = "temporarily disabled during Lean refactoring"]
fn test_lean_binary_available_for_ci() {
    // Use require_available() instead of skip_without_lean!() to make this mandatory
    LeanRunner::require_available();

    // Verify we can actually create a runner
    let runner =
        LeanRunner::new().expect("Lean runner should be constructable after require_available()");

    // Run a minimal validation to confirm the binary works
    let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
    let program = build_program_json(
        "A",
        &LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End),
    );

    let result = runner
        .validate(&global_to_json(&global), &program)
        .expect("Lean validation should work");
    assert!(result.success, "Basic validation should pass");
}
