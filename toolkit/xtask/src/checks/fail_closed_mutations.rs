use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{bail, Context, Result};

struct FileGuard {
    path: PathBuf,
    original: String,
}

impl FileGuard {
    fn new(path: PathBuf) -> Result<Self> {
        let original =
            fs::read_to_string(&path).with_context(|| format!("reading {}", path.display()))?;
        Ok(Self { path, original })
    }

    fn restore(&self) -> Result<()> {
        fs::write(&self.path, &self.original)
            .with_context(|| format!("restoring {}", self.path.display()))
    }
}

fn replace_once(path: &Path, old: &str, new: &str) -> Result<()> {
    let text = fs::read_to_string(path)?;
    if !text.contains(old) {
        bail!("missing mutation target in {}: {}", path.display(), old);
    }
    let replaced = text.replacen(old, new, 1);
    fs::write(path, replaced)?;
    Ok(())
}

/// Run a Rust check function and verify it fails with the expected error message.
fn assert_rust_check_fails<F>(label: &str, expected: &str, f: F) -> Result<()>
where
    F: FnOnce() -> Result<()>,
{
    match f() {
        Ok(()) => bail!("error: expected {label} to fail closed"),
        Err(e) => {
            let msg = format!("{e:#}");
            if !msg.contains(expected) {
                bail!(
                    "error: {label} failed, but not with the expected diagnostic\nexpected substring: {expected}\nactual: {msg}"
                );
            }
            Ok(())
        }
    }
}

/// Run an external command and verify it fails with the expected message.
fn assert_cmd_fails(
    label: &str,
    expected: &str,
    repo_root: &Path,
    cmd: &str,
    args: &[&str],
) -> Result<()> {
    let output = Command::new(cmd)
        .args(args)
        .current_dir(repo_root)
        .output()
        .with_context(|| format!("running {cmd}"))?;
    if output.status.success() {
        bail!("error: expected {label} to fail closed");
    }
    let combined = format!(
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
    if !combined.contains(expected) {
        bail!(
            "error: {label} failed, but not with the expected diagnostic\nexpected substring: {expected}\n{combined}"
        );
    }
    Ok(())
}

pub fn run(repo_root: &Path) -> Result<()> {
    // Mutation 1: bridge normalization ledger drift
    {
        let doc_path = repo_root.join("docs/902_verification_inventory.md");
        let guard = FileGuard::new(doc_path.clone())?;
        replace_once(
            &doc_path,
            "semantic-audit tick normalization",
            "semantic-audit tick mutation",
        )?;
        let rr = repo_root.to_path_buf();
        let result = assert_rust_check_fails(
            "bridge normalization ledger mutation",
            "missing bridge normalization ledger row for 'semantic-audit tick normalization'",
            move || super::bridge_normalization_ledger::run(&rr),
        );
        guard.restore()?;
        result?;
    }

    // Mutation 2: capability admission docs row mutation
    {
        let doc_path = repo_root.join("docs/702_capability_admission.md");
        let guard = FileGuard::new(doc_path.clone())?;
        replace_once(
            &doc_path,
            "| `protocol_envelope_bridge` |",
            "| `phase16_mutation_boundary` |",
        )?;
        let result = assert_cmd_fails(
            "capability admission docs row mutation",
            "missing expected docs row:",
            repo_root,
            "just",
            &["check-docs-as-contract"],
        );
        guard.restore()?;
        result?;
    }

    // Mutation 3: authority language docs row mutation
    {
        let doc_path = repo_root.join("docs/703_authority_language_surface.md");
        let guard = FileGuard::new(doc_path.clone())?;
        replace_once(
            &doc_path,
            "| `par` with observational binding |",
            "| `phase16_parallel_mutation` |",
        )?;
        let result = assert_cmd_fails(
            "authority language docs row mutation",
            "missing expected docs row:",
            repo_root,
            "just",
            &["check-docs-as-contract"],
        );
        guard.restore()?;
        result?;
    }

    // Mutation 4: verification inventory metric mutation
    {
        let doc_path = repo_root.join("docs/902_verification_inventory.md");
        let guard = FileGuard::new(doc_path.clone())?;
        replace_once(
            &doc_path,
            "| Handler contract boundary assurance suites | 2 |",
            "| Handler contract boundary assurance suites | 999 |",
        )?;
        let rr = repo_root.to_path_buf();
        let result = assert_rust_check_fails(
            "verification inventory metric mutation",
            "metric `Handler contract boundary assurance suites` documents 999 but actual is 2",
            move || super::verification_inventory::run(&rr),
        );
        guard.restore()?;
        result?;
    }

    // Mutation 5: package resource escape mutation
    {
        let probe_path = repo_root.join("rust/runtime/src/__phase10_package_resource_probe.rs");
        fs::write(
            &probe_path,
            "const _: &str = include_str!(\"../Cargo.toml\");\n",
        )?;
        let result = assert_cmd_fails(
            "package resource escape mutation",
            "forbidden pattern",
            repo_root,
            "just",
            &["_toolkit-check", "durable_boundaries"],
        );
        let _ = fs::remove_file(&probe_path);
        result?;
    }

    // Mutation 6: package manifest readme mutation
    {
        let manifest_path = repo_root.join("rust/runtime/Cargo.toml");
        let guard = FileGuard::new(manifest_path.clone())?;
        replace_once(
            &manifest_path,
            "readme = \"../../README.md\"",
            "readme = \"../../PHASE16_MISSING_README.md\"",
        )?;
        let rr = repo_root.to_path_buf();
        let result = assert_rust_check_fails(
            "package manifest readme mutation",
            "error: telltale-runtime: manifest readme path missing: ../../PHASE16_MISSING_README.md",
            move || super::package_artifacts::run(&rr),
        );
        guard.restore()?;
        result?;
    }

    // Mutation 7: release package registry mutation
    {
        let packages_path = repo_root.join("scripts/lib/release-packages.sh");
        let guard = FileGuard::new(packages_path.clone())?;
        replace_once(
            &packages_path,
            "RELEASE_PACKAGES=(\n",
            "RELEASE_PACKAGES=(\n  \"telltale-phase10-missing\"\n",
        )?;
        let rr = repo_root.to_path_buf();
        let result = assert_rust_check_fails(
            "release package registry mutation",
            "unknown package: telltale-phase10-missing",
            move || super::release_recovery::run(&rr),
        );
        guard.restore()?;
        result?;
    }

    println!("fail-closed-mutations: ok");
    Ok(())
}
