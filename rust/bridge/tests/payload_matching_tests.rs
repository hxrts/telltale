//! Payload-annotation agreement between Rust and Lean projection validators.
//!
//! Lean's EQ2 compares branch payloads (`BranchR := Label × Option ValType ×
//! LocalTypeR`). The process `send "b" [(m, payload nat, end)]` must therefore
//! be rejected against the projection of `comm a b [(m, end)]`, whose payload
//! is `none`, by both the Rust validator and the Lean `telltale_validator`.

#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

use serde_json::Value;
use telltale_bridge::{
    global_to_json, json_to_global, json_to_local, LeanRunner, LeanRunnerError, Validator,
};
use telltale_theory::projection::project;
use telltale_types::ValType;

const STRICT_ENV: &str = "TELLTALE_REQUIRE_LEAN_VALIDATOR";

fn strict_projection_required() -> bool {
    std::env::var(STRICT_ENV)
        .map(|value| value != "0")
        .unwrap_or(false)
}

macro_rules! skip_without_lean {
    () => {
        if !LeanRunner::is_available() {
            assert!(
                !strict_projection_required(),
                "strict projection verification is enabled but telltale_validator is unavailable"
            );
            eprintln!(
                "SKIPPED: Lean binary not available. Run `cd lean && lake build telltale_validator` to enable."
            );
            return;
        }
    };
}

fn fixture() -> Value {
    serde_json::from_str(include_str!("fixtures/payload_matching.json")).expect("fixture JSON")
}

/// Validate `program` against Rust's projection of the fixture choreography.
fn rust_validate(program_key: &str) -> bool {
    let fx = fixture();
    let global = json_to_global(&fx["choreography"]).expect("global");
    let program = &fx[program_key];
    let role = program["role"].as_str().expect("role");
    let projected = project(&global, role).expect("projection");
    Validator::new()
        .compare_projection(&projected, &program["local_type"])
        .expect("compare")
        .is_valid()
}

fn lean_validate(program_key: &str) -> bool {
    let fx = fixture();
    let runner = LeanRunner::new().expect("Lean binary should exist");
    // On a projection mismatch the validator prints to stdout and exits 1 with an
    // empty stderr; decode/parse failures are reported on stderr and count as crashes.
    match runner.validate(&fx["choreography"], &fx[program_key]) {
        Ok(result) => result.success,
        Err(LeanRunnerError::ProcessFailed { code: 1, stderr }) if stderr.trim().is_empty() => {
            false
        }
        Err(err) => panic!("Lean validation crashed: {err}"),
    }
}

#[test]
fn fixture_payload_decodes() {
    let fx = fixture();
    let lt = json_to_local(&fx["mismatch_program"]["local_type"]).expect("local");
    match lt {
        telltale_types::LocalTypeR::Send { branches, .. } => {
            assert_eq!(branches[0].1, Some(ValType::Nat));
        }
        other => panic!("expected send, got {other:?}"),
    }
    let global = json_to_global(&fx["choreography"]).expect("global");
    assert_eq!(global_to_json(&global), fx["choreography"]);
}

#[test]
fn rust_validator_rejects_payload_mismatch() {
    assert!(!rust_validate("mismatch_program"));
}

#[test]
fn rust_validator_accepts_payload_agreement() {
    assert!(rust_validate("matching_program"));
}

#[test]
fn lean_validator_rejects_payload_mismatch() {
    skip_without_lean!();
    assert!(!lean_validate("mismatch_program"));
}

#[test]
fn lean_validator_accepts_payload_agreement() {
    skip_without_lean!();
    assert!(lean_validate("matching_program"));
}
