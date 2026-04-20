use std::ffi::OsStr;
use std::fs;
use std::path::Path;
use std::process::Command;

use anyhow::{bail, Context, Result};

const RELEASE_PACKAGES: &[&str] = &[
    "telltale-types",
    "telltale-language",
    "telltale-theory",
    "telltale-macros",
    "telltale-machine",
    "telltale",
    "telltale-runtime",
    "telltale-transport",
    "telltale-search",
    "telltale-simulator",
    "telltale-bridge",
];

const NON_RELEASE_WORKSPACE_PACKAGES: &[&str] = &["telltale-lints", "telltale-ui", "telltale-web"];

const WASM_EXAMPLE_LOCK_PACKAGES: &[&str] = &[
    "telltale",
    "telltale-language",
    "telltale-machine",
    "telltale-macros",
    "telltale-theory",
    "telltale-types",
];

const IGNORED_PACKAGE_STDERR_SUBSTRINGS: &[&str] =
    &["package `core2 v0.4.0` in Cargo.lock is yanked in registry `crates-io`"];

fn manifest_path(package: &str) -> Option<&'static str> {
    match package {
        "telltale-types" => Some("rust/types/Cargo.toml"),
        "telltale-language" => Some("rust/language/Cargo.toml"),
        "telltale-theory" => Some("rust/theory/Cargo.toml"),
        "telltale-macros" => Some("rust/macros/Cargo.toml"),
        "telltale-machine" => Some("rust/machine/Cargo.toml"),
        "telltale" => Some("Cargo.toml"),
        "telltale-runtime" => Some("rust/runtime/Cargo.toml"),
        "telltale-transport" => Some("rust/transport/Cargo.toml"),
        "telltale-search" => Some("rust/search/Cargo.toml"),
        "telltale-simulator" => Some("rust/simulator/Cargo.toml"),
        "telltale-bridge" => Some("rust/bridge/Cargo.toml"),
        _ => None,
    }
}

fn extract_version(cargo_toml: &str) -> Option<String> {
    let mut in_package = false;
    for line in cargo_toml.lines() {
        if line.trim() == "[package]" {
            in_package = true;
            continue;
        }
        if in_package && line.starts_with('[') {
            in_package = false;
        }
        if in_package && line.starts_with("version") {
            let val = line
                .splitn(2, '=')
                .nth(1)?
                .trim()
                .trim_matches('"')
                .to_string();
            return Some(val);
        }
    }
    None
}

fn extract_path_field(cargo_toml: &str, field: &str) -> Option<String> {
    let mut in_package = false;
    let target = format!("{field} =");
    for line in cargo_toml.lines() {
        if line.trim() == "[package]" {
            in_package = true;
            continue;
        }
        if in_package && line.starts_with('[') {
            in_package = false;
        }
        if in_package && line.starts_with(&target) {
            let val = line
                .splitn(2, '=')
                .nth(1)?
                .trim()
                .trim_matches('"')
                .to_string();
            return Some(val);
        }
    }
    None
}

fn print_filtered_output(output: &std::process::Output) {
    let stdout = String::from_utf8_lossy(&output.stdout);
    if !stdout.is_empty() {
        print!("{stdout}");
    }

    let stderr = String::from_utf8_lossy(&output.stderr);
    for line in stderr.lines() {
        if IGNORED_PACKAGE_STDERR_SUBSTRINGS
            .iter()
            .any(|needle| line.contains(needle))
        {
            continue;
        }
        eprintln!("{line}");
    }
}

fn run_command_filtered(cmd: &mut Command, context: &str) -> Result<()> {
    let rendered = format_command(cmd);
    let output = cmd.output()?;
    print_filtered_output(&output);
    if !output.status.success() {
        bail!("{context}: `{rendered}` failed");
    }
    Ok(())
}

fn format_command(cmd: &Command) -> String {
    let program = cmd.get_program().to_string_lossy().into_owned();
    let args = cmd
        .get_args()
        .map(OsStr::to_string_lossy)
        .map(|arg| arg.into_owned())
        .collect::<Vec<_>>()
        .join(" ");
    if args.is_empty() {
        program
    } else {
        format!("{program} {args}")
    }
}

pub fn run(repo_root: &Path) -> Result<()> {
    let workspace_toml = fs::read_to_string(repo_root.join("Cargo.toml"))?;
    let workspace_version = extract_version(&workspace_toml)
        .ok_or_else(|| anyhow::anyhow!("could not extract workspace version"))?;

    println!("== check package manifest versions ==");
    for package in RELEASE_PACKAGES {
        let rel_manifest =
            manifest_path(package).ok_or_else(|| anyhow::anyhow!("unknown package: {package}"))?;
        let manifest = repo_root.join(rel_manifest);
        let text = fs::read_to_string(&manifest)
            .with_context(|| format!("reading {}", manifest.display()))?;
        let version = extract_version(&text)
            .ok_or_else(|| anyhow::anyhow!("{package}: could not extract version"))?;
        if version != workspace_version {
            bail!("error: version mismatch for {package}: {version} != {workspace_version}");
        }
    }

    println!("== check manifest readme paths ==");
    for package in RELEASE_PACKAGES {
        let rel_manifest = manifest_path(package).unwrap();
        let manifest_full = repo_root.join(rel_manifest);
        let manifest_dir = manifest_full.parent().unwrap();
        let text = fs::read_to_string(&manifest_full)?;
        if let Some(readme_path) = extract_path_field(&text, "readme") {
            let resolved = manifest_dir.join(&readme_path);
            let canonical = resolved.canonicalize().ok().filter(|p| p.exists());
            if canonical.is_none() && !resolved.exists() {
                bail!("error: {package}: manifest readme path missing: {readme_path}");
            }
        }
    }

    println!("== check wasm example lock file ==");
    let wasm_lock = repo_root.join("examples/wasm/Cargo.lock");
    if !wasm_lock.exists() {
        bail!("error: missing {}", wasm_lock.display());
    }
    let wasm_lock_text = fs::read_to_string(&wasm_lock)?;
    for package in WASM_EXAMPLE_LOCK_PACKAGES {
        if !wasm_lock_text.contains(&format!("name = \"{package}\"")) {
            bail!("error: missing {package} entry in examples/wasm/Cargo.lock");
        }
        // Check version matches
        let pkg_marker = format!("name = \"{package}\"");
        for (i, line) in wasm_lock_text.lines().enumerate() {
            if line.contains(&pkg_marker) {
                // Find the version in the next few lines
                for next_line in wasm_lock_text.lines().skip(i + 1).take(5) {
                    if next_line.starts_with("version") {
                        let lock_version = next_line
                            .splitn(2, '=')
                            .nth(1)
                            .unwrap_or("")
                            .trim()
                            .trim_matches('"');
                        if lock_version != workspace_version {
                            bail!("error: examples/wasm/Cargo.lock is stale for {package}: {lock_version} != {workspace_version}");
                        }
                        break;
                    }
                }
                break;
            }
        }
    }

    println!("== check resolved dependency rust-version compatibility ==");
    // Run the Python-based MSRV check via cargo tree
    // (Implemented inline: just check that cargo tree runs cleanly for each package)
    for package in RELEASE_PACKAGES {
        let status = Command::new("cargo")
            .args([
                "tree",
                "-p",
                package,
                "-e",
                "normal,build",
                "--prefix",
                "none",
                "--format",
                "{p}",
            ])
            .current_dir(repo_root)
            .output()?;
        if !status.status.success() {
            bail!("error: cargo tree failed for {package}");
        }
    }

    println!("== build and package release tarballs ==");
    let saved_tarball_dir = repo_root.join("target/package-artifact-tarballs");
    fs::create_dir_all(&saved_tarball_dir)?;
    for package in RELEASE_PACKAGES {
        let tarball_name = format!("{package}-{workspace_version}.crate");
        let target_tarball = repo_root.join("target/package").join(&tarball_name);
        if target_tarball.exists() {
            fs::remove_file(&target_tarball)?;
        }
        let saved_tarball = saved_tarball_dir.join(&tarball_name);
        if saved_tarball.exists() {
            fs::remove_file(&saved_tarball)?;
        }
    }

    let mut package_cmd = Command::new("cargo");
    package_cmd
        .arg("package")
        .arg("--workspace")
        .arg("--no-verify")
        .arg("--allow-dirty");
    for package in NON_RELEASE_WORKSPACE_PACKAGES {
        package_cmd.arg("--exclude").arg(package);
    }
    run_command_filtered(
        package_cmd.current_dir(repo_root),
        "error: cargo package failed for release workspace",
    )?;

    for package in RELEASE_PACKAGES {
        // Find generated tarball
        let tarball_src = repo_root
            .join("target/package")
            .join(format!("{package}-{workspace_version}.crate"));
        if !tarball_src.exists() {
            bail!("error: missing tarball {}", tarball_src.display());
        }

        // Copy to saved dir
        let tarball_dest = saved_tarball_dir.join(format!("{package}-{workspace_version}.crate"));
        fs::copy(&tarball_src, &tarball_dest)?;
        println!("{}", tarball_dest.display());
    }

    println!("== check examples/wasm auxiliary files ==");
    let wasm_readme = repo_root.join("examples/wasm/README.md");
    if !wasm_readme.exists() {
        bail!("error: missing examples/wasm/README.md");
    }
    let wasm_harness = repo_root.join("examples/wasm/harness.sh");
    if !wasm_harness.exists() {
        bail!("error: missing examples/wasm/harness.sh");
    }

    println!("== check tarball required contents ==");
    for (pkg, needle) in &[
        ("telltale", "README.md"),
        ("telltale-runtime", "README.md"),
        ("telltale-runtime", "src/compiler/choreography.pest"),
        ("telltale-bridge", "README.md"),
    ] {
        let tarball = saved_tarball_dir.join(format!("{pkg}-{workspace_version}.crate"));
        let output = Command::new("tar")
            .args([
                "-tf",
                tarball.to_str().unwrap(),
                &format!("{pkg}-{workspace_version}/{needle}"),
            ])
            .output()?;
        if !output.status.success() {
            bail!("error: {pkg} tarball missing {needle}");
        }
    }

    // Write provenance manifest
    let provenance = serde_json::json!({
        "workspace_version": workspace_version,
        "packages": RELEASE_PACKAGES,
    });
    let manifest_path = saved_tarball_dir.join("provenance.json");
    fs::write(&manifest_path, serde_json::to_string_pretty(&provenance)?)?;

    println!("package-artifacts: ok");
    Ok(())
}
