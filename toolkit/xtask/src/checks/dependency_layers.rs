use std::collections::BTreeMap;
use std::path::Path;
use std::process::Command;

use anyhow::{bail, Result};

fn crate_layer(name: &str) -> Option<u8> {
    match name {
        "telltale-types" => Some(1),
        "telltale-theory" | "telltale-language" | "telltale-macros" => Some(2),
        "telltale-machine" | "telltale-search" => Some(3),
        "telltale-runtime" | "telltale-bridge" | "telltale-simulator" | "telltale-transport"
        | "telltale" | "telltale-lints" => Some(4),
        "telltale-viewer" | "telltale-ui" | "telltale-web" => Some(5),
        _ => None,
    }
}

pub fn run(repo_root: &Path) -> Result<()> {
    println!("Checking TellTale dependency-layer ordering...");

    let output = Command::new("cargo")
        .args(["metadata", "--no-deps", "--format-version", "1"])
        .current_dir(repo_root)
        .output()?;
    if !output.status.success() {
        bail!("dependency-layers: cargo metadata failed");
    }

    let meta: serde_json::Value = serde_json::from_slice(&output.stdout)?;
    let members: std::collections::HashSet<String> = meta["workspace_members"]
        .as_array()
        .ok_or_else(|| anyhow::anyhow!("no workspace_members"))?
        .iter()
        .filter_map(|v| v.as_str().map(String::from))
        .collect();

    let packages = meta["packages"]
        .as_array()
        .ok_or_else(|| anyhow::anyhow!("no packages"))?;

    // Build name -> layer map for workspace packages
    let mut name_to_layer: BTreeMap<String, u8> = BTreeMap::new();
    let mut unknown: Vec<String> = Vec::new();
    let mut pkg_count = 0u32;

    for pkg in packages {
        let id = pkg["id"].as_str().unwrap_or_default();
        if !members.contains(id) {
            continue;
        }
        let name = pkg["name"].as_str().unwrap_or_default();
        pkg_count += 1;
        match crate_layer(name) {
            Some(layer) => {
                name_to_layer.insert(name.to_string(), layer);
            }
            None => {
                unknown.push(format!("package_not_layered={name}"));
            }
        }
    }

    // Check dependency edges
    let mut errors: Vec<String> = Vec::new();

    for pkg in packages {
        let id = pkg["id"].as_str().unwrap_or_default();
        if !members.contains(id) {
            continue;
        }
        let pkg_name = pkg["name"].as_str().unwrap_or_default();
        let Some(&pkg_layer) = name_to_layer.get(pkg_name) else {
            continue;
        };

        let deps = pkg["dependencies"]
            .as_array()
            .map(Vec::as_slice)
            .unwrap_or(&[]);
        for dep in deps {
            // Skip non-local (has a source) and dev deps
            if dep["source"].is_string() {
                continue;
            }
            let kind = dep["kind"].as_str().unwrap_or("none");
            if kind != "null" && kind != "none" && dep["kind"] != serde_json::Value::Null {
                continue;
            }
            let dep_name = dep["name"].as_str().unwrap_or_default();
            match name_to_layer.get(dep_name) {
                Some(&dep_layer) if dep_layer > pkg_layer => {
                    errors.push(format!(
                        "{pkg_name}(L{pkg_layer}) -> {dep_name}(L{dep_layer})"
                    ));
                }
                None if crate_layer(dep_name).is_none() => {
                    // Only report if it looks like a workspace dep
                    // (dep.source is null means it's local)
                    unknown.push(format!("{pkg_name} -> {dep_name}"));
                }
                _ => {}
            }
        }
    }

    // Deduplicate and sort
    unknown.sort();
    unknown.dedup();
    errors.sort();

    let mut failed = false;

    if !unknown.is_empty() {
        println!("Dependency layer check failed: unmapped local dependencies detected.");
        println!("Add these crates to the layer map:");
        for item in &unknown {
            println!("  - {item}");
        }
        println!();
        failed = true;
    }

    if !errors.is_empty() {
        println!("Dependency layer check failed: forbidden upward dependency found.");
        for item in &errors {
            println!("  - {item}");
        }
        println!();
        failed = true;
    }

    if failed {
        let total = errors.len() + unknown.len();
        println!("dependency-layer violations: {total}");
        bail!("dependency-layers failed");
    }

    println!("dependency-layer check passed");
    println!("checked {pkg_count} workspace packages");
    Ok(())
}
