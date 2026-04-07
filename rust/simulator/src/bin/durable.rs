//! Inspect persisted durable WAL and evidence-cache artifacts.
//!
//! This CLI is intentionally inspection-only. It projects durable artifacts into
//! an observed report rather than exposing backend-specific storage internals.

use std::path::PathBuf;

use telltale_machine::model::durability::PersistedDurabilityArtifact;
use telltale_simulator::handler_from_field;
use telltale_simulator::inspect_durable_artifacts;
use telltale_simulator::resume_with_durable_checkpoint_artifact;
use telltale_simulator::scenario::Scenario;
use telltale_simulator::{DurableResumeArtifacts, PersistedReplayArtifact};

struct DurableArgs {
    wal_path: PathBuf,
    cache_path: PathBuf,
    checkpoint_path: Option<PathBuf>,
    scenario_path: Option<PathBuf>,
    output_path: Option<PathBuf>,
    json: bool,
    pretty: bool,
}

fn main() {
    let raw_args: Vec<String> = std::env::args().skip(1).collect();
    let durable_args = parse_args(&raw_args).unwrap_or_else(|e| usage(&format!("{e}\n")));

    let wal = PersistedDurabilityArtifact::from_path(&durable_args.wal_path)
        .and_then(PersistedDurabilityArtifact::into_agreement_wal)
        .unwrap_or_else(|e| fatal(&e));
    let evidence_cache = PersistedDurabilityArtifact::from_path(&durable_args.cache_path)
        .and_then(PersistedDurabilityArtifact::into_evidence_outcome_cache)
        .unwrap_or_else(|e| fatal(&e));

    let recovery = match (
        durable_args.checkpoint_path.as_ref(),
        durable_args.scenario_path.as_ref(),
    ) {
        (Some(checkpoint_path), Some(scenario_path)) => {
            let scenario = Scenario::from_file(scenario_path).unwrap_or_else(|e| fatal(&e));
            let checkpoint = PersistedReplayArtifact::from_path(checkpoint_path)
                .and_then(PersistedReplayArtifact::into_checkpoint_artifact)
                .unwrap_or_else(|e| fatal(&e));
            let field = scenario
                .field
                .as_ref()
                .unwrap_or_else(|| fatal("scenario is missing built-in field parameters"));
            let handler = handler_from_field(field);
            let result = resume_with_durable_checkpoint_artifact(
                &scenario,
                &checkpoint,
                &DurableResumeArtifacts {
                    wal: wal.clone(),
                    evidence_cache: evidence_cache.clone(),
                },
                handler.as_ref(),
                None,
                None,
            )
            .unwrap_or_else(|e| fatal(&e));
            result.stats.durable_recovery
        }
        (None, None) => None,
        _ => fatal("use --checkpoint and --scenario together when requesting recovery decisions"),
    };

    let report = inspect_durable_artifacts(&wal, &evidence_cache, recovery.as_ref());

    if durable_args.json {
        let json = if durable_args.pretty {
            serde_json::to_string_pretty(&report)
        } else {
            serde_json::to_string(&report)
        }
        .unwrap_or_else(|e| fatal(&format!("serialize durable inspection report: {e}")));

        if let Some(path) = durable_args.output_path {
            std::fs::write(&path, format!("{json}\n"))
                .unwrap_or_else(|e| fatal(&format!("write {}: {e}", path.display())));
        } else {
            println!("{json}");
        }
        return;
    }

    println!(
        "durable inspection: {} wal entries, {} cache entries",
        report.wal_entries.len(),
        report.evidence_cache_entries.len()
    );
    for entry in &report.wal_entries {
        println!(
            "wal tick={} op={} kind={:?} {}",
            entry.tick, entry.operation_id, entry.kind, entry.detail
        );
    }
    for entry in &report.evidence_cache_entries {
        println!(
            "cache evidence={} {}.{} status={}",
            entry.evidence_id, entry.interface_name, entry.operation_name, entry.outcome_status
        );
    }
    if let Some(recovery) = &report.recovery {
        println!(
            "recovery regime={:?} theorem={:?} decisions={}",
            recovery.execution_regime,
            recovery.theorem_profile.scheduler_profile,
            recovery.decisions.len()
        );
    }
}

fn parse_args(args: &[String]) -> Result<DurableArgs, String> {
    let mut wal_path: Option<PathBuf> = None;
    let mut cache_path: Option<PathBuf> = None;
    let mut checkpoint_path: Option<PathBuf> = None;
    let mut scenario_path: Option<PathBuf> = None;
    let mut output_path: Option<PathBuf> = None;
    let mut json = false;
    let mut pretty = false;

    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--wal" => {
                let Some(path) = args.get(i + 1) else {
                    return Err("missing value after --wal".to_string());
                };
                wal_path = Some(PathBuf::from(path));
                i += 2;
            }
            "--cache" => {
                let Some(path) = args.get(i + 1) else {
                    return Err("missing value after --cache".to_string());
                };
                cache_path = Some(PathBuf::from(path));
                i += 2;
            }
            "--checkpoint" => {
                let Some(path) = args.get(i + 1) else {
                    return Err("missing value after --checkpoint".to_string());
                };
                checkpoint_path = Some(PathBuf::from(path));
                i += 2;
            }
            "--scenario" => {
                let Some(path) = args.get(i + 1) else {
                    return Err("missing value after --scenario".to_string());
                };
                scenario_path = Some(PathBuf::from(path));
                i += 2;
            }
            "--output" => {
                let Some(path) = args.get(i + 1) else {
                    return Err("missing value after --output".to_string());
                };
                output_path = Some(PathBuf::from(path));
                i += 2;
            }
            "--json" => {
                json = true;
                i += 1;
            }
            "--pretty" => {
                pretty = true;
                i += 1;
            }
            flag => return Err(format!("unknown argument: {flag}")),
        }
    }

    Ok(DurableArgs {
        wal_path: wal_path.ok_or_else(|| "missing --wal <file>".to_string())?,
        cache_path: cache_path.ok_or_else(|| "missing --cache <file>".to_string())?,
        checkpoint_path,
        scenario_path,
        output_path,
        json,
        pretty,
    })
}

fn usage(msg: &str) -> ! {
    eprintln!("{msg}");
    eprintln!(
        "usage: telltale-simulator-durable --wal <file> --cache <file> [--checkpoint <file> --scenario <file>] [--json] [--pretty] [--output <file>]"
    );
    std::process::exit(1);
}

fn fatal(msg: &str) -> ! {
    eprintln!("{msg}");
    std::process::exit(1);
}
