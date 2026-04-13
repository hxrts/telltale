use std::fs;
use std::path::Path;
use std::process::Command;

use anyhow::{bail, Result};

pub fn run(repo_root: &Path) -> Result<()> {
    let mut errors: Vec<String> = Vec::new();

    // Run bridge normalization contract tests
    let status = Command::new("cargo")
        .args([
            "test",
            "-p",
            "telltale-bridge",
            "--lib",
            "bridge_normalization_contract_",
            "--",
            "--nocapture",
        ])
        .current_dir(repo_root)
        .status()?;
    if !status.success() {
        bail!("bridge-normalization-ledger: cargo test bridge_normalization_contract_ failed");
    }

    let json_parsing = repo_root.join("rust/bridge/src/protocol_machine_runner_json_parsing.rs");
    let json_parsing_text = fs::read_to_string(&json_parsing)?;

    // Extract inject_field_if_missing keys
    let injected: Vec<&str> = json_parsing_text
        .lines()
        .filter_map(|line| {
            let i = line.find("inject_field_if_missing(")?;
            let after = &line[i + "inject_field_if_missing(".len()..];
            let start = after.find('"')? + 1;
            let end = after[start..].find('"')?;
            Some(&after[start..start + end])
        })
        .collect::<std::collections::BTreeSet<_>>()
        .into_iter()
        .collect();

    if injected.len() != 1 || injected[0] != "schema_version" {
        errors.push(format!(
            "protocol_machine_runner_json_parsing.rs: schema-compatibility backfill must only inject schema_version, found [{:?}]",
            injected
        ));
    }

    // Check test-only helpers
    let test_only_checks = &[
        (
            "#[cfg(test)]\nfn inject_field_if_missing",
            "schema backfill helper must be test-only",
        ),
        (
            "#[cfg(test)]\nfn backfill_protocol_machine_run_output_schema_versions",
            "schema-version backfill must be test-only",
        ),
        (
            "#[cfg(test)]\npub(super) fn parse_protocol_machine_run_output_with_schema_backfill",
            "compatibility parser must be test-only",
        ),
    ];

    for (pattern, msg) in test_only_checks {
        if !json_parsing_text.contains(pattern) {
            // Use rg for multi-line pattern check
            let output = Command::new("rg")
                .args(["-q", "-U", pattern, json_parsing.to_str().unwrap()])
                .status();
            if output.map(|s| !s.success()).unwrap_or(true) {
                errors.push(format!(
                    "rust/bridge/src/protocol_machine_runner_json_parsing.rs: {msg}"
                ));
            }
        }
    }

    let runner = repo_root.join("rust/bridge/src/protocol_machine_runner.rs");
    let runner_text = fs::read_to_string(&runner)?;
    if !runner_text.contains("parse_protocol_machine_run_output_strict") {
        errors.push(
            "rust/bridge/src/protocol_machine_runner.rs: strict runner path must use parse_protocol_machine_run_output_strict".to_string(),
        );
    }

    let inventory = repo_root.join("docs/902_verification_inventory.md");
    let inventory_text = fs::read_to_string(&inventory)?;

    if !inventory_text.contains("## Bridge Normalization Trust Surface") {
        errors.push(
            "docs/902_verification_inventory.md: missing 'Bridge Normalization Trust Surface' section".to_string(),
        );
    }

    for needle in &["semantic-audit tick normalization"] {
        if !inventory_text.contains(needle) {
            errors.push(format!(
                "docs/902_verification_inventory.md: missing bridge normalization ledger row for '{needle}'"
            ));
        }
    }

    for needle in &["irreducible trusted comparison logic"] {
        if !inventory_text.contains(needle) {
            errors.push(format!(
                "docs/902_verification_inventory.md: missing bridge normalization classification '{needle}'"
            ));
        }
    }

    if inventory_text.contains("| runner JSON schema backfill |") {
        errors.push(
            "docs/902_verification_inventory.md: compatibility-only schema backfill must stay outside the trusted bridge ledger".to_string(),
        );
    }

    if inventory_text.contains("session-status ordering") {
        errors.push(
            "docs/902_verification_inventory.md: session-status ordering should no longer be listed as trusted normalization".to_string(),
        );
    }

    if runner_text.contains("fn normalized_session_statuses") {
        errors.push(
            "rust/bridge/src/protocol_machine_runner.rs: session-status comparison must be exact; normalized_session_statuses should not exist".to_string(),
        );
    }

    let lean_runner_test = repo_root.join("lean/Runtime/Tests/ProtocolMachineRunner.lean");
    let lean_runner_text = fs::read_to_string(&lean_runner_test)?;
    if !lean_runner_text.contains("sortedSessionStatusesJson") {
        errors.push(
            "lean/Runtime/Tests/ProtocolMachineRunner.lean: missing canonical source-side session-status ordering helper".to_string(),
        );
    }

    if !errors.is_empty() {
        let detail = errors.join("\n  - ");
        bail!(
            "bridge-normalization-ledger found {} issue(s)\n  - {detail}",
            errors.len()
        );
    }

    println!("bridge-normalization-ledger: ok");
    Ok(())
}
