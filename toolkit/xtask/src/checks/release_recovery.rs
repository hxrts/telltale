use std::fs;
use std::os::unix::fs::PermissionsExt;
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

fn workspace_version(repo_root: &Path) -> Result<String> {
    let cargo_toml = fs::read_to_string(repo_root.join("Cargo.toml"))?;
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
                .nth(1)
                .unwrap_or("")
                .trim()
                .trim_matches('"');
            return Ok(val.to_string());
        }
    }
    bail!("release-recovery: could not extract workspace version from Cargo.toml");
}

fn write_executable(path: &Path, content: &str) -> Result<()> {
    fs::write(path, content).with_context(|| format!("writing {}", path.display()))?;
    let mut perms = fs::metadata(path)?.permissions();
    perms.set_mode(0o755);
    fs::set_permissions(path, perms)?;
    Ok(())
}

fn validate_release_packages_script(repo_root: &Path) -> Result<()> {
    let script = fs::read_to_string(repo_root.join("scripts/lib/release-packages.sh"))
        .context("reading scripts/lib/release-packages.sh")?;
    // Extract quoted package names from the RELEASE_PACKAGES=( ... ) block
    let mut in_array = false;
    for line in script.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with("RELEASE_PACKAGES=(") {
            in_array = true;
            continue;
        }
        if in_array {
            if trimmed == ")" {
                break;
            }
            // strip surrounding quotes and whitespace
            let name = trimmed.trim_matches('"').trim_matches('\'');
            if name.is_empty() || name.starts_with('#') {
                continue;
            }
            if !RELEASE_PACKAGES.contains(&name) {
                bail!("unknown package: {name}");
            }
        }
    }
    Ok(())
}

pub fn run(repo_root: &Path) -> Result<()> {
    validate_release_packages_script(repo_root)?;
    let version = workspace_version(repo_root)?;
    let tmpdir = tempfile::Builder::new()
        .prefix("telltale-release-recovery")
        .tempdir()
        .context("creating tmpdir")?;
    let fakebin = tmpdir.path().join("bin");
    fs::create_dir_all(&fakebin)?;

    let published_file = tmpdir.path().join("published.txt");
    let publish_log = tmpdir.path().join("publish.log");
    fs::write(&published_file, "")?;
    fs::write(&publish_log, "")?;

    // Create fake cargo binary
    write_executable(
        &fakebin.join("cargo"),
        r#"#!/usr/bin/env bash
set -euo pipefail
published_file="${TELLTALE_FAKE_PUBLISHED_FILE:?}"
publish_log="${TELLTALE_FAKE_PUBLISH_LOG:?}"
version="${TELLTALE_FAKE_VERSION:?}"
fail_pkg="${TELLTALE_FAKE_FAIL_PACKAGE:-}"
fail_marker="${TELLTALE_FAKE_FAIL_MARKER:?}"

cmd="${1:-}"
shift || true

case "${cmd}" in
  search)
    package="${1:-}"
    if grep -qx "${package}" "${published_file}"; then
      echo "${package} = \"${version}\" # fake-index"
    else
      echo "${package} = \"0.0.0\" # fake-index"
    fi
    ;;
  publish)
    package=""
    while [[ "$#" -gt 0 ]]; do
      case "$1" in
        -p) package="$2"; shift 2 ;;
        *) shift ;;
      esac
    done
    [[ -n "${package}" ]] || { echo "fake cargo publish missing -p <package>" >&2; exit 2; }
    echo "${package}" >> "${publish_log}"
    if [[ -n "${fail_pkg}" && "${package}" == "${fail_pkg}" && ! -f "${fail_marker}" ]]; then
      touch "${fail_marker}"
      echo "simulated publish failure for ${package}" >&2
      exit 1
    fi
    if ! grep -qx "${package}" "${published_file}"; then
      echo "${package}" >> "${published_file}"
    fi
    ;;
  *) echo "unexpected fake cargo command: ${cmd}" >&2; exit 2 ;;
esac
"#,
    )?;

    write_executable(
        &fakebin.join("git"),
        r#"#!/usr/bin/env bash
set -euo pipefail
cmd="${1:-}"
shift || true
case "${cmd}" in
  diff) exit 0 ;;
  status) exit 0 ;;
  rev-parse)
    if [[ "${1:-}" == "--abbrev-ref" ]]; then echo "main"
    else echo "deadbeefdeadbeefdeadbeefdeadbeefdeadbeef"
    fi
    ;;
  *) echo "unexpected fake git command: ${cmd}" >&2; exit 2 ;;
esac
"#,
    )?;

    write_executable(
        &fakebin.join("just"),
        r#"#!/usr/bin/env bash
set -euo pipefail
echo "unexpected just invocation during release recovery test" >&2
exit 2
"#,
    )?;

    let fail_package = "telltale-runtime";
    let fail_marker = tmpdir.path().join("fail-once.marker");

    let base_path = std::env::var("PATH").unwrap_or_default();
    let injected_path = format!("{}:{base_path}", fakebin.display());

    let common_envs = &[
        ("CARGO_REGISTRY_TOKEN", "fake-token"),
        (
            "TELLTALE_FAKE_PUBLISHED_FILE",
            published_file.to_str().unwrap(),
        ),
        ("TELLTALE_FAKE_PUBLISH_LOG", publish_log.to_str().unwrap()),
        ("TELLTALE_FAKE_VERSION", version.as_str()),
        ("TELLTALE_FAKE_FAIL_MARKER", fail_marker.to_str().unwrap()),
        ("PATH", injected_path.as_str()),
    ];

    let release_cmd_args = &[
        "./scripts/ops/release.sh",
        "--version",
        &version,
        "--skip-ci",
        "--no-tag",
        "--allow-dirty",
        "--no-require-main",
    ];

    // Phase 1: simulate partial failure
    println!("== simulate partial release failure ==");
    let mut cmd = Command::new(release_cmd_args[0]);
    cmd.args(&release_cmd_args[1..])
        .env("TELLTALE_FAKE_FAIL_PACKAGE", fail_package)
        .current_dir(repo_root);
    for (k, v) in common_envs {
        cmd.env(k, v);
    }
    let status = cmd.status()?;
    if status.success() {
        bail!("release-recovery: expected first release run to fail on {fail_package}");
    }

    let published = fs::read_to_string(&published_file)?;
    if !published.lines().any(|l| l == "telltale") {
        bail!(
            "release-recovery: expected earlier packages to be published before simulated failure"
        );
    }
    if published.lines().any(|l| l == fail_package) {
        bail!("release-recovery: failed package {fail_package} should not be marked published after first run");
    }

    // Phase 2: simulate resume
    println!("== simulate release resume ==");
    let mut cmd = Command::new(release_cmd_args[0]);
    cmd.args(&release_cmd_args[1..])
        .env("TELLTALE_FAKE_FAIL_PACKAGE", "")
        .current_dir(repo_root);
    for (k, v) in common_envs {
        cmd.env(k, v);
    }
    let status = cmd.status()?;
    if !status.success() {
        bail!("release-recovery: resume run failed");
    }

    let published = fs::read_to_string(&published_file)?;
    for pkg in RELEASE_PACKAGES {
        if !published.lines().any(|l| l == *pkg) {
            bail!("release-recovery: resumed release never published {pkg}");
        }
    }

    let log = fs::read_to_string(&publish_log)?;
    for pkg in RELEASE_PACKAGES {
        let count = log.lines().filter(|l| *l == *pkg).count();
        if *pkg == fail_package {
            if count != 2 {
                bail!("release-recovery: expected failed package {pkg} to be attempted twice, saw {count}");
            }
        } else if count != 1 {
            bail!("release-recovery: expected package {pkg} to be published once across resume, saw {count}");
        }
    }

    println!("release-recovery: ok");
    Ok(())
}
