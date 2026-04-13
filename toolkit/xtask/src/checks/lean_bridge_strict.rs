use std::path::Path;
use std::process::Command;

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
        .args(["build", "telltale_validator", "protocol_machine_runner"])
        .arg("--dir")
        .arg(&lean_dir)
        .env("LEAN_NUM_THREADS", &lean_threads)
        .current_dir(repo_root)
        .status()?;
    if !status.success() {
        bail!("lean-bridge-strict: lake build failed");
    }

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
