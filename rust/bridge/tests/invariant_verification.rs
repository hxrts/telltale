#![allow(clippy::expect_used)]

#[path = "test_choreographies/mod.rs"]
mod test_choreographies;

use telltale_bridge::{
    InvariantVerificationResult, ProtocolMachineRunner, ProtocolMachineRunnerError,
};

#[derive(Debug)]
enum BundleVerificationOutcome {
    Verified(InvariantVerificationResult),
}

fn strict_protocol_bundle_verification_required() -> bool {
    std::env::var("TELLTALE_REQUIRE_VERIFY_PROTOCOL_BUNDLE")
        .map(|value| value != "0")
        .unwrap_or(false)
}

fn strict_protocol_machine_runner_required() -> bool {
    std::env::var("TELLTALE_REQUIRE_PROTOCOL_MACHINE_RUNNER")
        .map(|value| value != "0")
        .unwrap_or(false)
}

fn verify_bundle(
    bundle: &telltale_bridge::ProtocolBundle,
) -> Result<BundleVerificationOutcome, ProtocolMachineRunnerError> {
    if strict_protocol_bundle_verification_required() || strict_protocol_machine_runner_required() {
        ProtocolMachineRunner::require_available();
    }
    let runner = ProtocolMachineRunner::try_new()
        .expect("Lean protocol-machine runner must be available for invariant verification");

    runner
        .verify_invariants(bundle)
        .map(BundleVerificationOutcome::Verified)
}

fn verified_result_or_skip(
    outcome: Result<BundleVerificationOutcome, ProtocolMachineRunnerError>,
) -> Option<InvariantVerificationResult> {
    match outcome {
        Ok(BundleVerificationOutcome::Verified(result)) => Some(result),
        Err(err) => panic!("verify_invariants failed unexpectedly: {err}"),
    }
}

#[test]
fn test_verify_protocol_bundle_classifies_expected_stderr_patterns() {
    let fixture = test_choreographies::tier3_distributed::simple_majority();
    if strict_protocol_machine_runner_required() {
        ProtocolMachineRunner::require_available();
    }
    let runner = ProtocolMachineRunner::try_new()
        .expect("Lean protocol-machine runner must be available for invariant verification");
    let result = runner
        .verify_invariants(&fixture.to_bundle())
        .expect("verifyProtocolBundle should execute");
    assert!(
        result.valid,
        "supported verifyProtocolBundle path should accept the valid quorum fixture"
    );
}

#[test]
fn test_verify_protocol_bundle_support_matrix_is_explicit() {
    let fixture = test_choreographies::tier3_distributed::simple_majority();

    match verify_bundle(&fixture.to_bundle()).expect("support probe should not hard-fail") {
        BundleVerificationOutcome::Verified(result) => {
            assert!(
                result.valid,
                "supported verifyProtocolBundle path should accept the valid quorum fixture"
            );
        }
    }
}

#[test]
fn test_verify_protocol_bundle_emits_transported_theorem_boundary_inventory() {
    let fixture = test_choreographies::tier3_distributed::simple_majority();
    let result = verify_bundle(&fixture.to_bundle()).expect("support probe should not hard-fail");
    let result = match result {
        BundleVerificationOutcome::Verified(result) => result,
    };

    let boundary = result
        .artifacts
        .get("transported_theorem_boundary")
        .and_then(serde_json::Value::as_array)
        .expect("verifyProtocolBundle should emit transported theorem boundary artifacts");
    assert!(
        !boundary.is_empty(),
        "transported theorem boundary ledger must not be empty"
    );

    let rust_runtime_keys = result
        .artifacts
        .get("rust_runtime_critical_transport_theorem_keys")
        .and_then(serde_json::Value::as_array)
        .expect("verifyProtocolBundle should emit Rust runtime theorem keys");
    let rust_runtime_keys: Vec<_> = rust_runtime_keys
        .iter()
        .map(|value| {
            value
                .as_str()
                .expect("runtime theorem key entries must be strings")
        })
        .collect();
    assert_eq!(
        rust_runtime_keys,
        vec![
            "protocol_machine_envelope_adherence",
            "protocol_machine_envelope_admission",
            "protocol_envelope_bridge",
        ]
    );
    assert_eq!(
        result
            .artifacts
            .get("runtime_critical_transport_theorems_explicit")
            .and_then(serde_json::Value::as_bool),
        Some(true),
        "runtime-critical theorem boundary must fail closed when assumption markers disappear",
    );

    let byzantine = boundary
        .iter()
        .find(|entry| {
            entry.get("key").and_then(serde_json::Value::as_str)
                == Some("byzantine_safety_characterization")
        })
        .expect("transported theorem boundary should classify byzantine safety");
    assert_eq!(
        byzantine
            .get("usage_class")
            .and_then(serde_json::Value::as_str),
        Some("runtime_critical_instantiated_premise")
    );
    assert_eq!(
        byzantine
            .get("consumed_by_rust_runtime_admission")
            .and_then(serde_json::Value::as_bool),
        Some(false)
    );
    assert_eq!(
        byzantine
            .get("consumed_by_lean_runtime_gate")
            .and_then(serde_json::Value::as_bool),
        Some(true)
    );
    assert!(
        byzantine
            .get("assumption_boundary")
            .and_then(serde_json::Value::as_str)
            .is_some(),
        "Lean-only runtime-critical theorem gates must carry explicit assumption markers",
    );
}

#[test]
fn test_lean_verifies_valid_quorum_protocol() {
    let fixture = test_choreographies::tier3_distributed::simple_majority();
    let Some(result) = verified_result_or_skip(verify_bundle(&fixture.to_bundle())) else {
        return;
    };

    assert!(
        result.valid,
        "expected valid protocol bundle, errors: {:?}",
        result.errors
    );
}

#[test]
fn test_lean_rejects_bad_quorum() {
    let fixture = test_choreographies::bad_quorum();
    let Some(result) = verified_result_or_skip(verify_bundle(&fixture.to_bundle())) else {
        return;
    };

    assert!(
        !result.valid,
        "expected bad quorum fixture to fail verification"
    );
    assert!(
        !result.errors.is_empty(),
        "expected structured errors on bad quorum failure"
    );
    assert!(
        result
            .errors
            .iter()
            .all(|e| !e.code.trim().is_empty() && e.path.is_some()),
        "expected structured error code/path fields, got: {:?}",
        result.errors
    );
}

#[test]
fn test_lean_rejects_deadlock() {
    let fixture = test_choreographies::deadlock();
    let Some(result) = verified_result_or_skip(verify_bundle(&fixture.to_bundle())) else {
        return;
    };

    assert!(
        !result.valid,
        "expected deadlock fixture to fail verification"
    );
    assert!(
        result
            .errors
            .iter()
            .all(|e| !e.code.trim().is_empty() && e.path.is_some()),
        "expected structured error code/path fields, got: {:?}",
        result.errors
    );
}

#[test]
fn test_lean_rejects_unbounded_wait() {
    let fixture = test_choreographies::unbounded_wait();
    let Some(result) = verified_result_or_skip(verify_bundle(&fixture.to_bundle())) else {
        return;
    };

    assert!(
        !result.valid,
        "expected unbounded wait fixture to fail verification"
    );
    assert!(
        result
            .errors
            .iter()
            .all(|e| !e.code.trim().is_empty() && e.path.is_some()),
        "expected structured error code/path fields, got: {:?}",
        result.errors
    );
}
