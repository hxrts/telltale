use std::io::Write;
use std::path::Path;
use std::process::{Command, Stdio};

use anyhow::{bail, Result};

pub fn run(repo_root: &Path) -> Result<()> {
    let lean_dir = repo_root.join("lean");

    // Ensure lean prebuilt artifacts are available
    let bootstrap = repo_root.join("scripts/bootstrap/ensure-lean-prebuilt.sh");
    let status = Command::new(&bootstrap).current_dir(repo_root).status()?;
    if !status.success() {
        bail!("lean-bridge-strict: ensure-lean-prebuilt failed");
    }

    let lean_threads = std::env::var("LEAN_NUM_THREADS").unwrap_or_else(|_| "3".to_string());

    println!("build strict Lean verification binaries");
    let status = Command::new("lake")
        .args(["build", "telltale_validator"])
        .arg("--dir")
        .arg(&lean_dir)
        .env("LEAN_NUM_THREADS", &lean_threads)
        .current_dir(repo_root)
        .status()?;
    if !status.success() {
        bail!("lean-bridge-strict: lake build failed");
    }

    let runner_script = repo_root.join("scripts/lean/protocol-machine-runner.sh");
    if !runner_script.is_file() {
        bail!("lean-bridge-strict: protocol-machine runner fallback script missing");
    }
    prewarm_json_entrypoint(
        &runner_script,
        "{\"operation\":\"validateTrace\",\"payload\":{\"choreographies\":[],\"trace\":[]}}",
        "protocol-machine runner",
        repo_root,
    )?;

    let validator_script = repo_root.join("scripts/lean/protocol-machine-validator.sh");
    if !validator_script.is_file() {
        bail!("lean-bridge-strict: protocol-machine validator fallback script missing");
    }
    prewarm_json_entrypoint(
        &validator_script,
        "{\"operation\":\"verifyProtocolBundle\",\"payload\":{\"claims\":{}}}",
        "protocol-machine validator",
        repo_root,
    )?;

    let strict_suites: &[(&[&str], &[(&str, &str)])] = &[
        (
            &[
                "test",
                "-p",
                "telltale-bridge",
                "--test",
                "projection_runner_tests",
                "--",
                "--nocapture",
            ],
            &[("TELLTALE_REQUIRE_LEAN_VALIDATOR", "1")],
        ),
        (
            &[
                "test",
                "-p",
                "telltale-bridge",
                "--test",
                "invariant_verification",
                "--",
                "--nocapture",
            ],
            &[("TELLTALE_REQUIRE_PROTOCOL_MACHINE_RUNNER", "1")],
        ),
        (
            &[
                "test",
                "-p",
                "telltale-bridge",
                "--test",
                "property_tests",
                "--",
                "--nocapture",
            ],
            &[("TELLTALE_REQUIRE_PROTOCOL_MACHINE_RUNNER", "1")],
        ),
        (
            &[
                "test",
                "-p",
                "telltale-bridge",
                "--test",
                "protocol_bundle_admission_contracts",
                "--",
                "--nocapture",
            ],
            &[("TELLTALE_REQUIRE_PROTOCOL_MACHINE_RUNNER", "1")],
        ),
        (
            &[
                "test",
                "-p",
                "telltale-bridge",
                "--test",
                "lean_trace_validation",
                "--",
                "--nocapture",
            ],
            &[
                ("TELLTALE_REQUIRE_PROTOCOL_MACHINE_RUNNER", "1"),
                ("TELLTALE_REQUIRE_PROTOCOL_MACHINE_TRACE_VALIDATION", "1"),
            ],
        ),
        (
            &[
                "test",
                "-p",
                "telltale-simulator",
                "--test",
                "lean_reference_parity",
                "--",
                "--nocapture",
            ],
            &[
                ("TELLTALE_REQUIRE_PROTOCOL_MACHINE_RUNNER", "1"),
                ("TELLTALE_REQUIRE_SIMULATION_TRACE_VALIDATION", "1"),
            ],
        ),
        (
            &[
                "test",
                "-p",
                "telltale-bridge",
                "--test",
                "protocol_machine_correspondence_tests",
                "--",
                "--nocapture",
            ],
            &[("TELLTALE_REQUIRE_PROTOCOL_MACHINE_RUNNER", "1")],
        ),
        (
            &[
                "test",
                "-p",
                "telltale-bridge",
                "--test",
                "protocol_machine_differential_steps",
                "--",
                "--nocapture",
            ],
            &[("TELLTALE_REQUIRE_PROTOCOL_MACHINE_RUNNER", "1")],
        ),
        (
            &[
                "test",
                "-p",
                "telltale-bridge",
                "--test",
                "capability_model_correspondence",
                "--",
                "--nocapture",
            ],
            &[("TELLTALE_REQUIRE_PROTOCOL_MACHINE_RUNNER", "1")],
        ),
    ];

    for (cargo_args, envs) in strict_suites {
        let suite = cargo_args[4]; // test name
        println!("run strict {suite} corpus");
        let mut cmd = Command::new("cargo");
        cmd.args(*cargo_args)
            .envs(envs.iter().copied())
            .current_dir(repo_root);
        let status = cmd.status()?;
        if !status.success() {
            bail!("lean-bridge-strict: {suite} failed");
        }
    }

    println!("lean-bridge-strict: ok");
    Ok(())
}

fn prewarm_json_entrypoint(
    script: &Path,
    payload: &str,
    name: &str,
    repo_root: &Path,
) -> Result<()> {
    println!("prewarm {name}");
    let mut child = Command::new(script)
        .current_dir(repo_root)
        .stdin(Stdio::piped())
        .stdout(Stdio::null())
        .stderr(Stdio::inherit())
        .spawn()?;
    if let Some(stdin) = child.stdin.as_mut() {
        stdin.write_all(payload.as_bytes())?;
    }
    let status = child.wait()?;
    if !status.success() {
        bail!("lean-bridge-strict: {name} prewarm failed");
    }
    Ok(())
}
