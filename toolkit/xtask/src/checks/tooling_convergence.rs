use std::fs;
use std::path::Path;
use std::process::Command;

use anyhow::{bail, Result};

fn normalize_manifest_path<'a>(raw: &'a str, _repo_root: &Path) -> Option<String> {
    if let Some(rest) = raw.strip_prefix("../../../") {
        return Some(rest.to_string());
    }
    if let Some(rest) = raw.strip_prefix("../../choreography/") {
        return Some(format!("rust/choreography/{rest}"));
    }
    if let Some(rest) = raw.strip_prefix("../../runtime/") {
        return Some(format!("rust/runtime/{rest}"));
    }
    if let Some(rest) = raw.strip_prefix("../examples/") {
        return Some(format!("rust/machine/examples/{rest}"));
    }
    if let Some(rest) = raw.strip_prefix("../benches/") {
        return Some(format!("rust/machine/benches/{rest}"));
    }
    None
}

struct Expectation {
    kind: String,
    path: String,
    pattern: String,
}

fn parse_manifest_expectations(manifest_text: &str, repo_root: &Path) -> Vec<Expectation> {
    let mut expectations = Vec::new();
    let mut section = "";
    let mut pending_path: Option<String> = None;

    for line in manifest_text.lines() {
        if line.contains("const REQUIRED_PATTERNS") {
            section = "required";
            continue;
        }
        if line.contains("const FORBIDDEN_PATTERNS") {
            section = "forbidden";
            continue;
        }
        if section.is_empty() {
            continue;
        }
        if line.trim() == "];" {
            section = "";
            pending_path = None;
            continue;
        }

        if let Some(i) = line.find("path:") {
            let after = &line[i + 5..];
            if let Some(start) = after.find('"') {
                if let Some(end) = after[start + 1..].find('"') {
                    let raw_path = &after[start + 1..start + 1 + end];
                    pending_path = normalize_manifest_path(raw_path, repo_root);
                }
            }
            continue;
        }

        if let Some(i) = line.find("pattern:") {
            if let Some(path) = pending_path.take() {
                let after = &line[i + 8..];
                if let Some(start) = after.find('"') {
                    if let Some(end) = after[start + 1..].find('"') {
                        let pattern = after[start + 1..start + 1 + end].to_string();
                        if !pattern.is_empty() && !section.is_empty() {
                            expectations.push(Expectation {
                                kind: section.to_string(),
                                path,
                                pattern,
                            });
                        }
                    }
                }
            }
            continue;
        }
    }

    expectations
}

pub fn run(repo_root: &Path) -> Result<()> {
    let manifest_path =
        repo_root.join("rust/machine/tests/support/tooling_convergence_manifest.rs");
    if !manifest_path.exists() {
        bail!(
            "tooling-convergence: manifest not found: {}",
            manifest_path.display()
        );
    }
    let manifest_text = fs::read_to_string(&manifest_path)?;

    let expectations = parse_manifest_expectations(&manifest_text, repo_root);
    let mut violations = 0;

    for exp in &expectations {
        let path = repo_root.join(&exp.path);
        if !path.exists() {
            eprintln!(
                "tooling-convergence: manifest path does not exist: {}",
                exp.path
            );
            bail!("tooling-convergence: missing manifest path");
        }

        if exp.kind == "required" {
            let text = fs::read_to_string(&path)?;
            if !text.contains(&exp.pattern) {
                eprintln!("{}: missing required pattern `{}`", exp.path, exp.pattern);
                violations += 1;
            }
        } else {
            // forbidden - use rg to find matches with line numbers
            let output = Command::new("rg")
                .args(["-Fn", "--", &exp.pattern, path.to_str().unwrap()])
                .output()?;
            if !output.stdout.is_empty() {
                let found = String::from_utf8_lossy(&output.stdout);
                eprint!("{found}");
                eprintln!("{}: found forbidden pattern `{}`", exp.path, exp.pattern);
                violations += 1;
            }
        }
    }

    if violations > 0 {
        bail!("tooling-convergence: manifest-backed tooling/docs convergence checks failed");
    }

    // Deprecated scaffold flags
    let checks: &[(&str, &[&str])] = &[
        ("effect-scaffold out=", &["justfile"]),
        (
            "--name",
            &["justfile", "rust/runtime/src/bin/effect_scaffold.rs"],
        ),
        (
            r"\bThreadedVM\b",
            &["rust/machine/examples", "rust/machine/benches"],
        ),
        (
            r"\bVM::new\b",
            &["rust/machine/examples", "rust/machine/benches"],
        ),
        (
            r"\bVMConfig\b",
            &["rust/machine/examples", "rust/machine/benches"],
        ),
        (
            "load_choreography(",
            &["rust/machine/examples", "rust/machine/benches"],
        ),
        (
            "EffectHandler stubs plus simulator harness test templates",
            &["justfile"],
        ),
        (
            r"Program::new\(",
            &[
                "docs/201_getting_started.md",
                "docs/104_architecture.md",
                "docs/204_extensions.md",
                "docs/301_effect_handlers.md",
                "docs/205_examples.md",
                "docs/206_wasm_guide.md",
            ],
        ),
        (r"compose race\b", &["docs", "examples"]),
        (r"compose fallback\b", &["docs", "examples"]),
        (r"compose quorum\(", &["docs", "examples"]),
    ];

    for (pattern, paths) in checks {
        let resolved: Vec<_> = paths
            .iter()
            .map(|p| repo_root.join(p))
            .filter(|p| p.exists())
            .collect();
        if resolved.is_empty() {
            continue;
        }
        let mut cmd = Command::new("rg");
        cmd.arg("-n").arg(pattern);
        for p in &resolved {
            cmd.arg(p);
        }
        cmd.arg("-g").arg("!target");
        let output = cmd.output()?;
        if !output.stdout.is_empty() {
            let found = String::from_utf8_lossy(&output.stdout);
            eprint!("{found}");
            bail!("tooling-convergence: found forbidden pattern: {pattern}");
        }
    }

    println!("tooling-convergence: ok");
    Ok(())
}
