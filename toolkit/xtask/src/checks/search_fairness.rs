use std::path::Path;
use std::process::Command;

use anyhow::{bail, Result};

pub fn run(repo_root: &Path) -> Result<()> {
    let artifact_output = Command::new("./scripts/ops/export-search-theorem-pack.sh")
        .current_dir(repo_root)
        .output()?;
    if !artifact_output.status.success() {
        bail!("search-fairness: export-search-theorem-pack.sh failed");
    }
    let artifact_path = String::from_utf8_lossy(&artifact_output.stdout)
        .trim()
        .to_string();
    if artifact_path.is_empty() || !repo_root.join(&artifact_path).exists() {
        bail!("search-fairness: missing search theorem-pack export {artifact_path}");
    }

    let vector_output = Command::new("./scripts/ops/export-search-vectors.sh")
        .current_dir(repo_root)
        .output()?;
    if !vector_output.status.success() {
        bail!("search-fairness: export-search-vectors.sh failed");
    }
    let vector_path = String::from_utf8_lossy(&vector_output.stdout)
        .trim()
        .to_string();
    if vector_path.is_empty() || !repo_root.join(&vector_path).exists() {
        bail!("search-fairness: missing search vector export {vector_path}");
    }

    let recovery_output = Command::new("./scripts/ops/export-search-recovery-vectors.sh")
        .current_dir(repo_root)
        .output()?;
    if !recovery_output.status.success() {
        bail!("search-fairness: export-search-recovery-vectors.sh failed");
    }
    let recovery_path = String::from_utf8_lossy(&recovery_output.stdout)
        .trim()
        .to_string();
    if recovery_path.is_empty() || !repo_root.join(&recovery_path).exists() {
        bail!("search-fairness: missing search recovery vector export {recovery_path}");
    }

    let lean_dir = repo_root.join("lean");
    let status = Command::new("lake")
        .args(["build", "Runtime.Proofs.Search.API", "search_parity_runner"])
        .arg("--dir")
        .arg(&lean_dir)
        .current_dir(repo_root)
        .status()?;
    if !status.success() {
        bail!("search-fairness: lake build failed");
    }

    for (pkg, test) in &[
        ("telltale-search", "search_lean"),
        ("telltale-search", "search_vectors"),
    ] {
        let status = Command::new("cargo")
            .args(["test", "-p", pkg, "--test", test, "--", "--nocapture"])
            .current_dir(repo_root)
            .status()?;
        if !status.success() {
            bail!("search-fairness: cargo test {pkg}:{test} failed");
        }
    }

    let status = Command::new("cargo")
        .args([
            "test",
            "-p",
            "telltale-search",
            "--test",
            "search_vectors",
            "--features",
            "multi-thread",
            "--",
            "--nocapture",
        ])
        .current_dir(repo_root)
        .status()?;
    if !status.success() {
        bail!("search-fairness: cargo test search_vectors (multi-thread) failed");
    }

    let status = Command::new("cargo")
        .args([
            "test",
            "-p",
            "telltale-search",
            "--test",
            "search_recovery_vectors",
            "--",
            "--nocapture",
        ])
        .current_dir(repo_root)
        .status()?;
    if !status.success() {
        bail!("search-fairness: cargo test search_recovery_vectors failed");
    }

    // Run verification-inventory as a sub-check
    super::verification_inventory::run(repo_root)?;

    println!("search-fairness: clean");
    Ok(())
}
