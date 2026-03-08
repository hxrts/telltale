#![allow(clippy::expect_used)]

#[path = "test_choreographies/mod.rs"]
mod test_choreographies;

use telltale_lean_bridge::{InvariantVerificationResult, VmRunner, VmRunnerError};

fn verify_bundle_or_skip(
    bundle: &telltale_lean_bridge::ProtocolBundle,
) -> Option<InvariantVerificationResult> {
    let Some(runner) = VmRunner::try_new() else {
        eprintln!("SKIPPED: Lean vm_runner not available");
        return None;
    };

    match runner.verify_invariants(bundle) {
        Ok(result) => Some(result),
        Err(VmRunnerError::ProcessFailed { stderr, .. })
            if stderr.contains("verifyProtocolBundle")
                || stderr.contains("unknown operation")
                || stderr.contains("unsupported operation")
                || stderr.contains("missing choreographies") =>
        {
            eprintln!("SKIPPED: Lean vm_runner does not support verifyProtocolBundle yet");
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
