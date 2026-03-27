#![allow(clippy::expect_used)]

#[path = "test_choreographies/mod.rs"]
mod test_choreographies;

use telltale_bridge::{
    InvariantVerificationResult, ProtocolMachineRunner, ProtocolMachineRunnerError,
};

#[derive(Debug)]
enum BundleVerificationOutcome {
    Verified(InvariantVerificationResult),
    MissingRunner,
    UnsupportedOperation(String),
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

fn unsupported_verify_protocol_bundle(stderr: &str) -> bool {
    stderr.contains("verifyProtocolBundle")
        || stderr.contains("unknown operation")
        || stderr.contains("unsupported operation")
        || stderr.contains("missing choreographies")
}

fn verify_bundle(
    bundle: &telltale_bridge::ProtocolBundle,
) -> Result<BundleVerificationOutcome, ProtocolMachineRunnerError> {
    let Some(runner) = ProtocolMachineRunner::try_new() else {
        if strict_protocol_bundle_verification_required()
            || strict_protocol_machine_runner_required()
        {
            ProtocolMachineRunner::require_available();
        }
        return Ok(BundleVerificationOutcome::MissingRunner);
    };

    match runner.verify_invariants(bundle) {
        Ok(result) => Ok(BundleVerificationOutcome::Verified(result)),
        Err(ProtocolMachineRunnerError::ProcessFailed { stderr, .. })
            if unsupported_verify_protocol_bundle(&stderr) =>
        {
            assert!(
                !strict_protocol_bundle_verification_required(),
                "strict protocol-bundle verification is enabled but verifyProtocolBundle is unsupported: {stderr}"
            );
            Ok(BundleVerificationOutcome::UnsupportedOperation(stderr))
        }
        Err(err) => Err(err),
    }
}

fn verified_result_or_skip(
    outcome: Result<BundleVerificationOutcome, ProtocolMachineRunnerError>,
) -> Option<InvariantVerificationResult> {
    match outcome {
        Ok(BundleVerificationOutcome::Verified(result)) => Some(result),
        Ok(BundleVerificationOutcome::MissingRunner) => {
            eprintln!("SKIPPED: Lean protocol-machine runner not available");
            None
        }
        Ok(BundleVerificationOutcome::UnsupportedOperation(stderr)) => {
            eprintln!(
                "SKIPPED: Lean protocol-machine runner does not support verifyProtocolBundle yet: {stderr}"
            );
            None
        }
        Err(err) => panic!("verify_invariants failed unexpectedly: {err}"),
    }
}

#[test]
fn test_verify_protocol_bundle_classifies_expected_stderr_patterns() {
    assert!(unsupported_verify_protocol_bundle(
        "unsupported operation: verifyProtocolBundle"
    ));
    assert!(unsupported_verify_protocol_bundle(
        "unknown operation verifyProtocolBundle"
    ));
    assert!(unsupported_verify_protocol_bundle("missing choreographies"));
    assert!(!unsupported_verify_protocol_bundle("schema decode failed"));
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
        BundleVerificationOutcome::MissingRunner => {
            assert!(
                !strict_protocol_machine_runner_required(),
                "strict protocol-machine runner verification is enabled but the runner is unavailable"
            );
            eprintln!("SKIPPED: Lean protocol-machine runner not available");
        }
        BundleVerificationOutcome::UnsupportedOperation(stderr) => {
            assert!(
                unsupported_verify_protocol_bundle(&stderr),
                "unsupported operation path should preserve the classifier diagnostic"
            );
        }
    }
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
