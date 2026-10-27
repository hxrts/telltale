use std::path::Path;
use std::process::Command;

use anyhow::{bail, Context, Result};

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

// Negative admission only: a readable directory does not prove any Lean artifact exists.
fn check_local_lean_prerequisite(repo_root: &Path) -> Result<()> {
    let path = repo_root.join("lean/.lake");
    let metadata = std::fs::metadata(&path)
        .with_context(|| format!("simulator-subsystem: inspecting {}", path.display()))?;
    if !metadata.is_dir() {
        bail!("simulator-subsystem: {} is not a directory", path.display());
    }
    let mut entries = std::fs::read_dir(&path)
        .with_context(|| format!("simulator-subsystem: reading {}", path.display()))?;
    if let Some(entry) = entries.next() {
        entry
            .with_context(|| format!("simulator-subsystem: reading entry in {}", path.display()))?;
    }
    Ok(())
}

fn run_subsystem_checks(repo_root: &Path) -> Result<()> {
    check_local_lean_prerequisite(repo_root)?;
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn missing_local_lean_fails_before_cargo_and_retains_native_cause() {
        let root = tempfile::tempdir().unwrap();
        let error = run(root.path(), &[]).unwrap_err();
        assert!(format!("{error:#}").contains("lean/.lake"));
        let native = error.downcast_ref::<std::io::Error>().unwrap();
        assert_eq!(native.kind(), std::io::ErrorKind::NotFound);
    }

    #[test]
    fn wrong_type_local_lean_refuses_and_readable_directory_is_only_a_precondition() {
        let root = tempfile::tempdir().unwrap();
        let lean = root.path().join("lean");
        std::fs::create_dir(&lean).unwrap();
        let lake = lean.join(".lake");
        std::fs::write(&lake, "not a directory").unwrap();
        let error = run(root.path(), &[]).unwrap_err();
        assert!(error.to_string().contains("not a directory"));
        std::fs::remove_file(&lake).unwrap();
        std::fs::create_dir(&lake).unwrap();
        check_local_lean_prerequisite(root.path()).unwrap();
        assert!(!lake.join("build/bin/protocol_machine_runner").exists());
    }

    #[cfg(unix)]
    #[test]
    fn permission_errors_follow_native_directory_access() {
        use std::os::unix::fs::PermissionsExt;
        let root = tempfile::tempdir().unwrap();
        let lake = root.path().join("lean/.lake");
        std::fs::create_dir_all(&lake).unwrap();
        let original = std::fs::metadata(&lake).unwrap().permissions();
        std::fs::set_permissions(&lake, std::fs::Permissions::from_mode(0)).unwrap();
        let native = std::fs::read_dir(&lake).err();
        let observed = check_local_lean_prerequisite(root.path());
        std::fs::set_permissions(&lake, original).unwrap();
        if let Some(native) = native {
            let error = observed.unwrap_err();
            let retained = error.downcast_ref::<std::io::Error>().unwrap();
            assert_eq!(retained.kind(), native.kind());
            assert_eq!(retained.raw_os_error(), native.raw_os_error());
            println!("native directory access refused; original permission cause retained");
        } else {
            // Privileged callers can legitimately read mode-000 directories.
            observed.unwrap();
            println!("native directory access permitted for this caller");
        }
    }

    #[test]
    fn applicability_and_cli_modes_do_not_claim_lean_readiness() {
        assert!(subsystem_applies_to_paths(&[
            "docs/902_verification_inventory.md".into()
        ]));
        assert!(!subsystem_applies_to_paths(&[
            "docs/902_verification_inventory.md".into(),
            "rust/machine/src/lib.rs".into(),
        ]));
        assert!(!subsystem_applies_to_paths(&[]));
        let root = tempfile::tempdir().unwrap();
        run(root.path(), &["--self-test".into()]).unwrap();
        assert!(run(root.path(), &["--unknown".into()]).is_err());
    }
}
