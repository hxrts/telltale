use std::path::Path;
use std::process::Command;

use anyhow::{bail, Result};

fn allowed_path_inner(path: &str) -> bool {
    path.starts_with("rust/simulator/")
        || path == "docs/501_simulation_overview.md"
        || path == "docs/502_simulation_runner.md"
        || path == "docs/503_simulation_scenarios.md"
        || path == "docs/504_simulation_fields.md"
        || path == "docs/902_verification_inventory.md"
        || path == "toolkit/xtask/src/checks/simulator_subsystem.rs"
}

fn staged_paths(repo_root: &Path) -> Result<Vec<String>> {
    let output = Command::new("git")
        .args(["diff", "--cached", "--name-only", "--diff-filter=ACMR"])
        .current_dir(repo_root)
        .output()?;
    if !output.status.success() {
        bail!("simulator-subsystem: git diff --cached failed");
    }
    let paths: Vec<String> = String::from_utf8_lossy(&output.stdout)
        .lines()
        .filter(|l| !l.is_empty())
        .map(String::from)
        .collect();
    Ok(paths)
}

fn subsystem_applies_to_paths(paths: &[String]) -> bool {
    if paths.is_empty() {
        return false;
    }
    paths.iter().all(|p| allowed_path_inner(p))
}

pub fn run(repo_root: &Path, extra: &[String]) -> Result<()> {
    let mode = extra.first().map(String::as_str).unwrap_or("");

    match mode {
        "--applies-to-staged" => {
            let paths = staged_paths(repo_root)?;
            if subsystem_applies_to_paths(&paths) {
                // Exit 0 = applies
                return Ok(());
            }
            // Exit non-zero = does not apply
            bail!("simulator-subsystem: does not apply to staged paths");
        }
        "--self-test" => {
            // Self-test: verify the subsystem detection logic works
            let test_paths = vec![
                "rust/simulator/src/runner.rs".to_string(),
                "docs/501_simulation_overview.md".to_string(),
            ];
            assert!(
                subsystem_applies_to_paths(&test_paths),
                "self-test: expected simulator-only paths to apply"
            );
            let mixed_paths = vec![
                "rust/simulator/src/runner.rs".to_string(),
                "rust/machine/src/lib.rs".to_string(),
            ];
            assert!(
                !subsystem_applies_to_paths(&mixed_paths),
                "self-test: expected mixed paths to not apply"
            );
            println!("simulator-subsystem self-test: ok");
            return Ok(());
        }
        "" => {
            // Run subsystem checks (called directly, not from pre-commit)
            run_subsystem_checks(repo_root)?;
        }
        other => bail!("simulator-subsystem: unknown mode: {other}"),
    }

    println!("simulator-subsystem: ok");
    Ok(())
}

fn run_subsystem_checks(repo_root: &Path) -> Result<()> {
    let status = Command::new("cargo")
        .args(["fmt", "-p", "telltale-simulator", "--", "--check"])
        .current_dir(repo_root)
        .status()?;
    if !status.success() {
        bail!("simulator-subsystem: cargo fmt check failed");
    }

    let status = Command::new("cargo")
        .args([
            "check",
            "-p",
            "telltale-simulator",
            "--all-targets",
            "--all-features",
        ])
        .current_dir(repo_root)
        .status()?;
    if !status.success() {
        bail!("simulator-subsystem: cargo check failed");
    }

    let tmpdir = std::env::var("TMPDIR").unwrap_or_else(|_| "/tmp".to_string());
    let status = Command::new("cargo")
        .args([
            "test",
            "-p",
            "telltale-simulator",
            "--all-targets",
            "--all-features",
        ])
        .env("TMPDIR", &tmpdir)
        .current_dir(repo_root)
        .status()?;
    if !status.success() {
        bail!("simulator-subsystem: cargo test failed");
    }

    // Check staged docs if any
    let paths = staged_paths(repo_root)?;
    let doc_paths: Vec<_> = paths
        .iter()
        .filter(|p| p.starts_with("docs/") && p.ends_with(".md"))
        .collect();
    if !doc_paths.is_empty() {
        let config = repo_root.join(".github/config/markdown-link-check.json");
        if config.exists() {
            let mut cmd = Command::new("npx");
            cmd.args([
                "--yes",
                "markdown-link-check",
                "--config",
                config.to_str().unwrap(),
            ]);
            for p in &doc_paths {
                cmd.arg(repo_root.join(p));
            }
            let status = cmd.current_dir(repo_root).status()?;
            if !status.success() {
                bail!("simulator-subsystem: markdown-link-check failed");
            }
        }
    }

    Ok(())
}
