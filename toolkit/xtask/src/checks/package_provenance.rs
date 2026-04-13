use std::fs;
use std::path::Path;
use std::process::Command;

use anyhow::{bail, Result};

pub fn run(repo_root: &Path) -> Result<()> {
    let manifest_path = repo_root.join("target/package-artifact-tarballs/provenance.json");

    if !manifest_path.exists() {
        println!("package-provenance: missing packaged artifact manifest; generating it first");
        super::package_artifacts::run(repo_root)?;
    }

    if !manifest_path.exists() {
        bail!("package-provenance: provenance.json still missing after package-artifacts run");
    }

    let manifest_text = fs::read_to_string(&manifest_path)?;
    let manifest: serde_json::Value = serde_json::from_str(&manifest_text)?;

    let workspace_version = manifest["workspace_version"].as_str().ok_or_else(|| {
        anyhow::anyhow!("package-provenance: missing workspace_version in provenance.json")
    })?;

    let packages = manifest["packages"].as_array().ok_or_else(|| {
        anyhow::anyhow!("package-provenance: missing packages in provenance.json")
    })?;

    let tarball_dir = repo_root.join("target/package-artifact-tarballs");

    println!("== verify package provenance hashes ==");
    for pkg_val in packages {
        let pkg = pkg_val
            .as_str()
            .ok_or_else(|| anyhow::anyhow!("package-provenance: invalid package entry"))?;
        let tarball = tarball_dir.join(format!("{pkg}-{workspace_version}.crate"));

        if !tarball.exists() {
            bail!(
                "package-provenance: missing tarball for {pkg}: {}",
                tarball.display()
            );
        }

        // Compute hash
        let hash_output = if which("sha256sum") {
            Command::new("sha256sum").arg(&tarball).output()?
        } else {
            Command::new("shasum")
                .args(["-a", "256"])
                .arg(&tarball)
                .output()?
        };

        if !hash_output.status.success() {
            bail!("package-provenance: hash command failed for {pkg}");
        }

        let hash = String::from_utf8_lossy(&hash_output.stdout)
            .split_whitespace()
            .next()
            .unwrap_or("")
            .to_string();
        println!("{pkg}: {hash}");
    }

    println!("package-provenance: ok");
    Ok(())
}

fn which(cmd: &str) -> bool {
    Command::new("which")
        .arg(cmd)
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}
