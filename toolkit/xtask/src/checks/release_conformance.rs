use std::path::Path;
use std::process::Command;

use anyhow::{bail, Result};

fn rg_q(pattern: &str, path: &Path) -> bool {
    if !path.exists() {
        return false;
    }
    Command::new("rg")
        .args(["--pcre2", "-q", pattern, path.to_str().unwrap()])
        .status()
        .map(|s| s.success())
        .unwrap_or(false)
}

pub fn run(repo_root: &Path) -> Result<()> {
    let release_file = repo_root.join("lean/Runtime/Proofs/TheoremPack/ReleaseConformance.lean");
    let api_file = repo_root.join("lean/Runtime/Proofs/TheoremPack/API.lean");
    let test_file = repo_root.join("lean/Runtime/Tests/Main.lean");
    let justfile = repo_root.join("justfile");

    let mut errors: usize = 0;
    let mut checks: usize = 0;

    let mut check = |desc: &str, ok: bool| {
        checks += 1;
        if ok {
            println!("OK   {desc}");
        } else {
            eprintln!("FAIL {desc}");
            errors += 1;
        }
    };

    println!("== Release Conformance ==");

    check(
        "optimization envelope classes are defined",
        rg_q(
            "inductive RuntimeTransformationEnvelopeClass",
            &release_file,
        ) && rg_q("def transformationClassEligible", &release_file),
    );

    check(
        "effect-bisim bridge theorem for transformation classes exists",
        rg_q(
            r"theorem transformation(_class|Class)_preserves_observer_behavior",
            &release_file,
        ),
    );

    check(
        "certified replay conformance helpers exist",
        rg_q("structure CertifiedReplayEquivalenceClass", &release_file)
            && rg_q("def replayConformsToCertifiedClass", &release_file)
            && rg_q("def replayConformsToClasses", &release_file),
    );

    check(
        "failure-envelope cross-target witness gate exists",
        rg_q("def hasFailureEnvelopeCrossTargetWitness", &release_file),
    );

    check(
        "restart/structured-error adequacy witness gate exists",
        rg_q(
            "def hasRestartStructuredErrorAdequacyWitness",
            &release_file,
        ),
    );

    check(
        "single-thread, multi-thread, and sharded evidence gates exist",
        rg_q("def hasSingleThreadEvidence", &release_file)
            && rg_q("def hasMultiThreadEvidence", &release_file)
            && rg_q("def hasShardedEvidence", &release_file),
    );

    check(
        "release report and release build gate are defined",
        rg_q("def releaseConformanceReportVersion", &release_file)
            && rg_q("structure ReleaseConformanceReport", &release_file)
            && rg_q("def buildReleaseConformanceReport", &release_file)
            && rg_q("def releaseBuildGate", &release_file),
    );

    check(
        "theorem-pack API exports release conformance helpers",
        rg_q("abbrev releaseConformanceReport", &api_file)
            && rg_q("abbrev releaseBuildGate", &api_file)
            && rg_q("abbrev hasFailureEnvelopeCrossTargetWitness", &api_file),
    );

    check(
        "Lean runtime tests cover certified replay conformance",
        rg_q(
            "replay conformance mismatch against certified equivalence class",
            &test_file,
        ),
    );

    check(
        "Justfile includes release conformance check target",
        rg_q("^check-release-conformance:", &justfile)
            && rg_q("just check-release-conformance", &justfile),
    );

    // Run cargo tests for release-critical components
    let status = Command::new("cargo")
        .args([
            "test",
            "-p",
            "telltale-bridge",
            "--test",
            "protocol_bundle_admission_contracts",
            "--",
            "--nocapture",
        ])
        .current_dir(repo_root)
        .status()?;
    check(
        "protocol_bundle_admission_contracts tests pass",
        status.success(),
    );

    println!("\nrelease-conformance: {checks} check(s), {errors} error(s)");

    if errors > 0 {
        bail!("release-conformance failed: {errors} error(s)");
    }

    println!("release-conformance: ok");
    Ok(())
}
