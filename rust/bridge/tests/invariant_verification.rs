#![allow(clippy::expect_used)]

#[path = "test_choreographies/mod.rs"]
mod test_choreographies;

use telltale_bridge::{
    InvariantVerificationResult, ProtocolMachineRunner, ProtocolMachineRunnerError,
};

fn strict_protocol_bundle_verification_required() -> bool {
    std::env::var("TELLTALE_REQUIRE_VERIFY_PROTOCOL_BUNDLE")
        .map(|value| value != "0")
        .unwrap_or_else(|_| std::env::var("CI").is_ok())
}

fn unsupported_verify_protocol_bundle(stderr: &str) -> bool {
    stderr.contains("verifyProtocolBundle")
        || stderr.contains("unknown operation")
        || stderr.contains("unsupported operation")
        || stderr.contains("missing choreographies")
}

fn verify_bundle_or_skip(
    bundle: &telltale_bridge::ProtocolBundle,
) -> Option<InvariantVerificationResult> {
    let strict = strict_protocol_bundle_verification_required();
    let Some(runner) = ProtocolMachineRunner::try_new() else {
        assert!(
            !strict,
            "protocol-machine runner binary is required when strict protocol-bundle verification is enabled"
        );
        eprintln!("SKIPPED: Lean protocol-machine runner not available");
        return None;
    };

    match runner.verify_invariants(bundle) {
        Ok(result) => Some(result),
        Err(ProtocolMachineRunnerError::ProcessFailed { stderr, .. })
            if unsupported_verify_protocol_bundle(&stderr) =>
        {
            assert!(
                !strict,
                "strict protocol-bundle verification is enabled but verifyProtocolBundle is unsupported: {stderr}"
            );
            eprintln!(
                "SKIPPED: Lean protocol-machine runner does not support verifyProtocolBundle yet"
            );
            None
        }
        Err(err) => panic!("verify_invariants failed unexpectedly: {err}"),
    }
}

#[test]
fn test_lean_verifies_valid_quorum_protocol() {
    let fixture = test_choreographies::tier3_distributed::simple_majority();
    let Some(result) = verify_bundle_or_skip(&fixture.to_bundle()) else {
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
    let Some(result) = verify_bundle_or_skip(&fixture.to_bundle()) else {
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
    let Some(result) = verify_bundle_or_skip(&fixture.to_bundle()) else {
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
    let Some(result) = verify_bundle_or_skip(&fixture.to_bundle()) else {
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
