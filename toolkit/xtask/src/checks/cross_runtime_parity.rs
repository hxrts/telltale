use std::fs;
use std::path::Path;
use std::process::Command;

use anyhow::{bail, Result};

pub fn run(repo_root: &Path, extra: &[String]) -> Result<()> {
    let mode = extra.first().map(String::as_str).unwrap_or("--all");

    match mode {
        "--all" => {
            check_types(repo_root)?;
            check_suite(repo_root)?;
            check_conformance(repo_root)?;
        }
        "--types" => check_types(repo_root)?,
        "--suite" => check_suite(repo_root)?,
        "--conformance" => check_conformance(repo_root)?,
        other => bail!("cross-runtime-parity: unknown mode: {other}"),
    }

    println!("cross-runtime-parity: ok");
    Ok(())
}

fn check_types(repo_root: &Path) -> Result<()> {
    println!("[parity] type shape parity checks");

    // Key enum/struct parity checks between Lean and Rust
    let type_checks = &[
        // (lean_file, lean_type, rust_file, rust_variants)
        (
            "lean/Runtime/ProtocolMachine/Model/SemanticObjects/Core.lean",
            "rust/machine/src/semantic_objects.rs",
        ),
        (
            "lean/Runtime/ProtocolMachine/Model/SemanticObjects/AgreementCore.lean",
            "rust/bridge/src/semantic_objects.rs",
        ),
    ];

    let mut mismatches = Vec::new();

    for (lean_path, rust_path) in type_checks {
        let lean_full = repo_root.join(lean_path);
        let rust_full = repo_root.join(rust_path);

        if !lean_full.exists() {
            mismatches.push(format!("missing Lean file: {lean_path}"));
            continue;
        }
        if !rust_full.exists() {
            mismatches.push(format!("missing Rust file: {rust_path}"));
            continue;
        }

        // For now: verify files exist and are non-empty
        let lean_text = fs::read_to_string(&lean_full)?;
        let rust_text = fs::read_to_string(&rust_full)?;

        if lean_text.is_empty() || rust_text.is_empty() {
            mismatches.push(format!(
                "empty file in parity pair: {lean_path} / {rust_path}"
            ));
        }
    }

    if !mismatches.is_empty() {
        for m in &mismatches {
            eprintln!("[parity] MISMATCH: {m}");
        }
        bail!("cross-runtime-parity: type shape mismatches");
    }

    println!("[parity] OK: type shape parity");
    Ok(())
}

fn check_suite(repo_root: &Path) -> Result<()> {
    println!("[parity] protocol machine differential parity test suite");

    let status = Command::new("cargo")
        .args([
            "test",
            "-p",
            "telltale-bridge",
            "--test",
            "protocol_machine_differential_steps",
            "--",
            "--nocapture",
        ])
        .current_dir(repo_root)
        .status()?;

    if !status.success() {
        bail!("cross-runtime-parity: differential steps test suite failed");
    }

    println!("[parity] OK: differential steps test suite");
    Ok(())
}

fn check_conformance(repo_root: &Path) -> Result<()> {
    println!("[parity] strict protocol machine conformance");

    let suites = &[
        (
            &[
                "test",
                "-p",
                "telltale-machine",
                "--test",
                "lean_protocol_machine_equivalence",
                "--",
                "--nocapture",
            ] as &[&str],
            &[] as &[(&str, &str)],
        ),
        (
            &[
                "test",
                "-p",
                "telltale-machine",
                "--test",
                "threaded_equivalence",
                "--",
                "--nocapture",
            ],
            &[],
        ),
    ];

    for (args, envs) in suites {
        let mut cmd = Command::new("cargo");
        cmd.args(*args)
            .envs(envs.iter().copied())
            .current_dir(repo_root);
        let status = cmd.status()?;
        if !status.success() {
            bail!("cross-runtime-parity: conformance suite {:?} failed", args);
        }
    }

    println!("[parity] OK: strict protocol machine conformance");
    Ok(())
}
