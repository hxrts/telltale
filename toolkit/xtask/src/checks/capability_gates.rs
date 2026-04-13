use std::path::Path;
use std::process::Command;

use anyhow::{bail, Result};

fn rg_contains(pattern: &str, path: &Path) -> bool {
    Command::new("rg")
        .args(["--pcre2", "-q", pattern, path.to_str().unwrap()])
        .status()
        .map(|s| s.success())
        .unwrap_or(false)
}

fn ensure_lean_prebuilt(repo_root: &Path) -> Result<()> {
    let bootstrap = repo_root.join("scripts/bootstrap/ensure-lean-prebuilt.sh");
    let status = Command::new(&bootstrap).current_dir(repo_root).status()?;
    if !status.success() {
        bail!("capability-gates: ensure-lean-prebuilt failed");
    }
    Ok(())
}

pub fn run(repo_root: &Path, extra: &[String]) -> Result<()> {
    let mode = extra.first().map(String::as_str).unwrap_or("--all");

    match mode {
        "--all" => {
            check_byzantine(repo_root)?;
            check_delegation(repo_root)?;
            check_envelope(repo_root)?;
            check_failure(repo_root)?;
            check_contracts(repo_root)?;
            check_speculation(repo_root)?;
        }
        "--byzantine" => check_byzantine(repo_root)?,
        "--delegation" => check_delegation(repo_root)?,
        "--envelope" => check_envelope(repo_root)?,
        "--failure" => check_failure(repo_root)?,
        "--contracts" => check_contracts(repo_root)?,
        "--speculation" => check_speculation(repo_root)?,
        other => bail!("capability-gates: unknown mode: {other}"),
    }

    println!("capability-gates: ok");
    Ok(())
}

fn check_byzantine(repo_root: &Path) -> Result<()> {
    ensure_lean_prebuilt(repo_root)?;
    let test_file = repo_root.join("lean/Distributed/Tests/ByzantineConformance.lean");
    let api_file = repo_root.join("lean/Runtime/Proofs/TheoremPack/API.lean");
    let mut failures = 0;

    println!("== Byzantine Conformance ==");

    let checks: &[(&str, &[(&str, &Path)], bool)] = &[
        (
            "positive profile test: theorem-pack byzantine slot materializes",
            &[("def canOperateUnderByzantineEnvelope", &api_file)],
            true,
        ),
        (
            "positive profile test: BFT specialization theorem is covered",
            &[("bft_specialization_of_quorum", &test_file)],
            true,
        ),
        (
            "positive profile test: Nakamoto specialization theorem is covered",
            &[("nakamoto_specialization_of_security", &test_file)],
            true,
        ),
        (
            "positive profile test: hybrid specialization theorem is covered",
            &[("hybrid_specialization_of_characterization", &test_file)],
            true,
        ),
    ];

    for (desc, file_checks, _) in checks {
        let ok = file_checks
            .iter()
            .all(|(pat, path)| path.exists() && rg_contains(pat, path));
        if ok {
            println!("OK   {desc}");
        } else {
            eprintln!("FAIL {desc}");
            failures += 1;
        }
    }

    if failures > 0 {
        bail!("capability-gates: byzantine checks failed ({failures} failure(s))");
    }
    Ok(())
}

fn check_delegation(repo_root: &Path) -> Result<()> {
    println!("== Delegation Shard Gate ==");
    let mut failures = 0;

    let cooperative_target_dir = repo_root.join("target/capability-gates/cooperative");
    let threaded_target_dir = repo_root.join("target/capability-gates/threaded");

    let checks: &[(&str, Vec<&str>, Vec<(&str, &str)>, &Path)] = &[
        (
            "cooperative transfer guard rejects non-delegation ownership mutation",
            vec![
                "test",
                "-p",
                "telltale-machine",
                "test_transfer_rejects_delegation_guard_violation",
            ],
            vec![],
            &cooperative_target_dir,
        ),
        (
            "threaded transfer handoff emits delegation evidence",
            vec![
                "test",
                "-p",
                "telltale-machine",
                "--features",
                "multi-thread",
                "--test",
                "threaded_lane_runtime",
                "deterministic_transfer_handoff_uses_delegation_path",
            ],
            vec![("TT_EXPECT_MULTI_THREAD", "1")],
            &threaded_target_dir,
        ),
        (
            "threaded transfer guard rejects ambiguous ownership mutation",
            vec![
                "test",
                "-p",
                "telltale-machine",
                "--features",
                "multi-thread",
                "delegation_handoff_guard_rejects_ambiguous_endpoint_ownership",
            ],
            vec![("TT_EXPECT_MULTI_THREAD", "1")],
            &threaded_target_dir,
        ),
    ];

    for (desc, args, envs, target_dir) in checks {
        let mut cmd = Command::new("cargo");
        cmd.args(args)
            .env("CARGO_TARGET_DIR", target_dir)
            .current_dir(repo_root);
        for (k, v) in envs {
            cmd.env(k, v);
        }
        let status = cmd.status()?;
        if status.success() {
            println!("OK   {desc}");
        } else {
            eprintln!("FAIL {desc}");
            failures += 1;
        }
    }

    if failures > 0 {
        bail!("capability-gates: delegation checks failed ({failures} failure(s))");
    }
    Ok(())
}

fn check_envelope(repo_root: &Path) -> Result<()> {
    ensure_lean_prebuilt(repo_root)?;
    let api_file = repo_root.join("lean/Runtime/Proofs/TheoremPack/API.lean");
    let inventory_file = repo_root.join("lean/Runtime/Proofs/TheoremPack/Inventory.lean");
    let adapter_file =
        repo_root.join("lean/Runtime/Proofs/Adapters/Distributed/ProfileWrappers.lean");
    let test_file = repo_root.join("lean/Runtime/Tests/Main.lean");
    let rust_envelope_test = repo_root.join("rust/machine/tests/parity_fixtures_v2.rs");
    let mut failures = 0;

    println!("== Envelope Conformance ==");

    let checks: Vec<(&str, bool)> = vec![
        (
            "runtime shard-placement gate helper exists",
            rg_contains("def canAdmitShardPlacement", &api_file),
        ),
        (
            "runtime live-migration gate helper exists",
            rg_contains("def canLiveMigrate", &api_file),
        ),
        (
            "runtime placement-refinement gate helper exists",
            rg_contains("def canRefinePlacement", &api_file),
        ),
        (
            "runtime reordering gate helper exists",
            rg_contains("def canRelaxReordering", &api_file),
        ),
        (
            "runtime mixed-determinism gate helper exists",
            rg_contains("def canUseMixedDeterminismProfiles", &api_file),
        ),
        (
            "runtime byzantine-envelope gate helper exists",
            rg_contains("def canOperateUnderByzantineEnvelope", &api_file),
        ),
        (
            "runtime autoscale/repartition gate helper exists",
            rg_contains("def canAutoscaleOrRepartition", &api_file),
        ),
        (
            "CI inventory-claim guard helper exists",
            rg_contains("def claimedCapabilitiesWithinInventory", &api_file),
        ),
        (
            "serialized envelope capability snapshot helper exists",
            rg_contains("def envelopeCapabilitySnapshot", &api_file),
        ),
        (
            "theorem-pack carries protocol bridge capability bit",
            rg_contains(
                r#"\("protocol_envelope_bridge", pack\.protocolEnvelopeBridge\?\.isSome\)"#,
                &inventory_file,
            ),
        ),
        (
            "theorem-pack carries byzantine safety capability bit",
            rg_contains(
                r#"\("byzantine_safety_characterization", pack\.byzantineSafety\?\.isSome\)"#,
                &inventory_file,
            ),
        ),
        (
            "theorem-pack carries protocol machine envelope adherence capability bit",
            rg_contains(
                r#"\("protocol_machine_envelope_adherence", pack\.protocolMachineEnvelopeAdherence\?\.isSome\)"#,
                &inventory_file,
            ),
        ),
        (
            "theorem-pack carries protocol machine envelope admission capability bit",
            rg_contains(
                r#"\("protocol_machine_envelope_admission", pack\.protocolMachineEnvelopeAdmission\?\.isSome\)"#,
                &inventory_file,
            ),
        ),
        (
            "distributed adapter carries protocol bridge profile slot",
            rg_contains(r"protocolEnvelopeBridge\?", &adapter_file),
        ),
        (
            "distributed adapter carries byzantine safety profile slot",
            rg_contains(r"byzantineSafety\?", &adapter_file),
        ),
        (
            "distributed adapter carries protocol machine adherence profile slot",
            rg_contains(r"protocolMachineEnvelopeAdherence\?", &adapter_file),
        ),
        (
            "distributed adapter carries protocol machine admission profile slot",
            rg_contains(r"protocolMachineEnvelopeAdmission\?", &adapter_file),
        ),
        (
            "local-envelope differential conformance test exists",
            rg_contains("local envelope modulo conformance mismatch", &test_file),
        ),
        (
            "sharded-envelope differential conformance test exists",
            rg_contains("sharded envelope modulo conformance mismatch", &test_file),
        ),
        (
            "admission regression boundary tests exist",
            rg_contains("admission regression:", &test_file),
        ),
        (
            "threaded wave-width envelope bound positive test exists",
            rg_contains(
                "envelope_bounded_parity_holds_for_n_gt_1",
                &rust_envelope_test,
            ),
        ),
        (
            "threaded wave-width envelope bound violation test exists",
            rg_contains(
                "envelope_bounded_parity_detects_wave_width_bound_violation",
                &rust_envelope_test,
            ),
        ),
    ];

    for (desc, ok) in &checks {
        if *ok {
            println!("OK   {desc}");
        } else {
            eprintln!("FAIL {desc}");
            failures += 1;
        }
    }

    // Run Lean conformance test module
    let lean_dir = repo_root.join("lean");
    let status = Command::new("lake")
        .args(["build", "Runtime.Tests.Main"])
        .current_dir(&lean_dir)
        .status();
    match status {
        Ok(s) if s.success() => {
            let run_status = Command::new("lake")
                .args(["env", "lean", "--run", "Runtime/Tests/Main.lean"])
                .current_dir(&lean_dir)
                .status();
            match run_status {
                Ok(s) if s.success() => println!("OK   Runtime.Tests.Main executes successfully"),
                _ => {
                    eprintln!("FAIL Runtime.Tests.Main execution failed");
                    failures += 1;
                }
            }
        }
        Ok(_) => {
            eprintln!("FAIL Runtime.Tests.Main build failed");
            failures += 1;
        }
        Err(_) => println!("WARN skipping Lean test execution (no lake found)"),
    }

    if failures > 0 {
        bail!("capability-gates: envelope checks failed ({failures} failure(s))");
    }
    Ok(())
}

fn check_failure(repo_root: &Path) -> Result<()> {
    ensure_lean_prebuilt(repo_root)?;
    let failure_file = repo_root.join("lean/Runtime/ProtocolMachine/Runtime/Failure.lean");
    let failure_proofs = repo_root.join("lean/Runtime/Proofs/ProtocolMachine/Failure.lean");
    let adapter_file =
        repo_root.join("lean/Runtime/Proofs/Adapters/Distributed/ProfileWrappers.lean");
    let build_file = repo_root.join("lean/Runtime/Proofs/TheoremPack/Build.lean");
    let artifacts_file = repo_root.join("lean/Runtime/Proofs/TheoremPack/Artifacts.lean");
    let inventory_file = repo_root.join("lean/Runtime/Proofs/TheoremPack/Inventory.lean");
    let profiles_file = repo_root.join("lean/Runtime/Proofs/TheoremPack/Profiles.lean");
    let test_file = repo_root.join("lean/Runtime/Tests/Main.lean");
    let state_file = repo_root.join("lean/Runtime/ProtocolMachine/Model/State.lean");
    let envelope_file = repo_root.join("lean/Runtime/Adequacy/EnvelopeCore.lean");
    let mut failures = 0;

    println!("== Failure Capability Conformance ==");

    let checks: Vec<(&str, bool)> = vec![
        (
            "bounded-diff recovery mode exists in runtime failure policy",
            rg_contains(r"\.boundedDiff", &failure_file),
        ),
        (
            "distributed adapters expose failure-envelope profile slot",
            rg_contains(r"failureEnvelope\?", &adapter_file),
        ),
        (
            "distributed adapters expose failure-envelope attach helper",
            rg_contains("withFailureEnvelope", &profiles_file),
        ),
        (
            "theorem-pack carries failure-envelope artifact slot",
            rg_contains(
                r"failureEnvelope\? : Option FailureEnvelopeArtifact",
                &build_file,
            ),
        ),
        (
            "theorem inventory exposes failure-envelope capability bit",
            rg_contains(
                r#"\("failure_envelope", pack\.failureEnvelope\?\.isSome\)"#,
                &inventory_file,
            ),
        ),
        (
            "artifact-level cross-target error-code compatibility tests exist",
            rg_contains("error-code compatibility mismatch", &test_file),
        ),
        (
            "cross-target failure-visible conformance regression tests exist",
            rg_contains(
                "cross-target failure-visible conformance mismatch",
                &test_file,
            ),
        ),
        (
            "restart structured-error adequacy regression tests exist",
            rg_contains("restart structured-error adequacy mismatch", &test_file),
        ),
        (
            "phase-1 gate: structured error schema + mappings",
            rg_contains("structure StructuredErrorEvent", &state_file)
                && rg_contains("def failureClassOfRustFaultTag", &envelope_file)
                && rg_contains("def errorCodeOfRustFaultTag", &envelope_file),
        ),
        (
            "phase-2 gate: deterministic recovery + checkpoint/idempotency",
            rg_contains(
                r"theorem decide(Recovery|_recovery)_deterministic",
                &failure_proofs,
            ) && rg_contains("checkpointLog", &state_file)
                && rg_contains("nextEffectNonce", &state_file),
        ),
        (
            "phase-3 gate: abstract failure proofs bridged through adapters/theorem-pack",
            rg_contains("structure FailureEnvelopeProtocol", &envelope_file)
                && rg_contains(r"failureEnvelope\?", &adapter_file)
                && rg_contains("FailureEnvelopeArtifact", &artifacts_file),
        ),
        (
            "phase-3.5 gate: cross-target failure conformance theorem exposed",
            rg_contains("def CrossTargetFailureConformance", &envelope_file)
                && rg_contains("crossTargetConformance", &artifacts_file),
        ),
        (
            "phase-3.6 gate: restart-refinement + structured-error adequacy theorem exposed",
            rg_contains(
                "def RestartRefinementStructuredErrorAdequacy",
                &envelope_file,
            ) && rg_contains("restartStructuredErrorAdequacy", &artifacts_file),
        ),
    ];

    for (desc, ok) in &checks {
        if *ok {
            println!("OK   {desc}");
        } else {
            eprintln!("FAIL {desc}");
            failures += 1;
        }
    }

    if failures > 0 {
        bail!("capability-gates: failure checks failed ({failures} failure(s))");
    }
    Ok(())
}

fn check_contracts(repo_root: &Path) -> Result<()> {
    let contracts_file = repo_root.join("rust/machine/src/runtime_contracts.rs");
    let mut failures = 0;

    println!("== Runtime Contract/Admission Conformance ==");

    let checks = &[
        ("runtime contracts file exists", contracts_file.exists()),
        (
            "admission gate assertion present",
            contracts_file.exists() && rg_contains("admission", &contracts_file),
        ),
    ];

    for (desc, ok) in checks {
        if *ok {
            println!("OK   {desc}");
        } else {
            eprintln!("FAIL {desc}");
            failures += 1;
        }
    }

    // Run cargo test for runtime contracts
    let status = Command::new("cargo")
        .args([
            "test",
            "-p",
            "telltale-machine",
            "--lib",
            "runtime_contracts",
            "--",
            "--nocapture",
        ])
        .current_dir(repo_root)
        .status()?;
    if !status.success() {
        eprintln!("FAIL runtime_contracts cargo tests");
        failures += 1;
    } else {
        println!("OK   runtime_contracts cargo tests");
    }

    if failures > 0 {
        bail!("capability-gates: contracts checks failed ({failures} failure(s))");
    }
    Ok(())
}

fn check_speculation(repo_root: &Path) -> Result<()> {
    ensure_lean_prebuilt(repo_root)?;
    let target_files = &[
        "lean/Runtime/ProgramLogic/GhostState.lean",
        "lean/Runtime/ProgramLogic/WPPair.lean",
        "lean/Runtime/ProgramLogic/SessionWP.lean",
        "lean/Runtime/ProgramLogic/FinalizationWP.lean",
        "lean/Runtime/Adequacy/Adequacy.lean",
        "lean/Runtime/Proofs/ProtocolMachine/Speculation.lean",
    ];
    let mut failures = 0;

    println!("== Speculation/WP Surface Conformance ==");

    // Check all target files exist
    for f in target_files {
        let path = repo_root.join(f);
        if !path.exists() {
            bail!("capability-gates: missing speculation target file: {f}");
        }
    }

    // Check for placeholder/stub markers in target modules
    let placeholder_pattern = r"(?i)\b(?:TODO|FIXME|TBD|placeholder|stub|unimplemented|WIP)\b";
    let mut has_placeholders = false;
    for f in target_files {
        let path = repo_root.join(f);
        if rg_contains(placeholder_pattern, &path) {
            has_placeholders = true;
            eprintln!("  placeholder found in {f}");
        }
    }
    if has_placeholders {
        eprintln!("FAIL speculation/WP target modules still contain placeholder markers");
        failures += 1;
    } else {
        println!("OK   no placeholder/stub markers in speculation/WP target modules");
    }

    // Build speculation targets with lake
    let lean_targets = &[
        "Runtime.ProgramLogic.WPPair",
        "Runtime.ProgramLogic.SessionWP",
        "Runtime.ProgramLogic.FinalizationWP",
        "Runtime.Adequacy.Adequacy",
        "Runtime.Proofs.ProtocolMachine.Speculation",
    ];
    let lean_dir = repo_root.join("lean");
    let mut lake_args = vec!["build"];
    lake_args.extend(lean_targets.iter().copied());
    let status = Command::new("lake")
        .args(&lake_args)
        .current_dir(&lean_dir)
        .status();
    match status {
        Ok(s) if s.success() => println!("OK   speculation/WP target modules build successfully"),
        Ok(_) => {
            eprintln!("FAIL speculation/WP target modules failed to build");
            failures += 1;
        }
        Err(_) => println!("WARN skipping Lean build check (no lake found)"),
    }

    if failures > 0 {
        bail!("capability-gates: speculation checks failed ({failures} failure(s))");
    }
    Ok(())
}
