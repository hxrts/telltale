mod checks;

use std::{env, path::PathBuf, process};

use anyhow::{bail, Result};

fn main() {
    if let Err(err) = run() {
        eprintln!("{err:#}");
        process::exit(1);
    }
}

fn run() -> Result<()> {
    let args: Vec<String> = env::args().skip(1).collect();
    match args.first().map(String::as_str) {
        Some("check") => run_check(&args[1..]),
        Some("--help") | Some("-h") | Some("help") => {
            println!(
                "telltale-xtask: usage: check <name> [--repo-root <path>] [-- <extra args>...]"
            );
            Ok(())
        }
        Some(other) => bail!("telltale-xtask: unknown command: {other}"),
        None => bail!("telltale-xtask: usage: check <name> [--repo-root <path>]"),
    }
}

fn run_check(args: &[String]) -> Result<()> {
    let name = args.first().cloned().ok_or_else(|| {
        anyhow::anyhow!(
            "telltale-xtask: usage: check <name> [--repo-root <path>] [-- <extra args>...]"
        )
    })?;

    let mut repo_root = env::current_dir()?;
    let mut extra: Vec<String> = Vec::new();
    let mut i = 1;
    let mut past_sep = false;
    while i < args.len() {
        if args[i] == "--" {
            past_sep = true;
            i += 1;
            continue;
        }
        if past_sep {
            extra.push(args[i].clone());
        } else if args[i] == "--repo-root" {
            i += 1;
            let v = args
                .get(i)
                .ok_or_else(|| anyhow::anyhow!("telltale-xtask: missing value for --repo-root"))?;
            repo_root = PathBuf::from(v)
                .canonicalize()
                .map_err(|e| anyhow::anyhow!("telltale-xtask: --repo-root {v}: {e}"))?;
        } else {
            extra.push(args[i].clone());
        }
        i += 1;
    }

    let norm = name.replace('_', "-");
    match norm.as_str() {
        "architecture-lean" => checks::architecture_lean::run(&repo_root),
        "architecture-rust" => checks::architecture_rust::run(&repo_root),
        "bridge-normalization-ledger" => checks::bridge_normalization_ledger::run(&repo_root),
        "capability-gates" => checks::capability_gates::run(&repo_root, &extra),
        "cross-runtime-parity" => checks::cross_runtime_parity::run(&repo_root, &extra),
        "dependency-layers" => checks::dependency_layers::run(&repo_root),
        "docs-prose-quality" => checks::docs_prose_quality::run(&repo_root),
        "fail-closed-mutations" => checks::fail_closed_mutations::run(&repo_root),
        "lean-bridge-strict" => checks::lean_bridge_strict::run(&repo_root),
        "lean-rust-semantic-name-parity" => checks::lean_rust_semantic_name_parity::run(&repo_root),
        "package-artifacts" => checks::package_artifacts::run(&repo_root),
        "package-provenance" => checks::package_provenance::run(&repo_root),
        "release-conformance" => checks::release_conformance::run(&repo_root),
        "release-recovery" => checks::release_recovery::run(&repo_root),
        "scale-budgets" => checks::scale_budgets::run(&repo_root),
        "search-fairness" => checks::search_fairness::run(&repo_root),
        "simulator-subsystem" => checks::simulator_subsystem::run(&repo_root, &extra),
        "tooling-convergence" => checks::tooling_convergence::run(&repo_root),
        "verification-inventory" => checks::verification_inventory::run(&repo_root),
        _ => bail!("telltale-xtask: unknown check: {name}"),
    }
}
