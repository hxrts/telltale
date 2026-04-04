//! Replay a simulation run from a checkpoint.
//!
//! This compatibility CLI keeps a terse textual summary for terminal use.
//! Rich human-facing inspection should prefer the shared viewer/webapp layers.

use std::path::PathBuf;

use telltale_simulator::handler_from_field;
use telltale_simulator::resume_with_checkpoint_artifact;
use telltale_simulator::scenario::Scenario;
use telltale_simulator::PersistedReplayArtifact;

struct ReplayArgs {
    checkpoint_path: PathBuf,
    scenario_path: PathBuf,
    rounds: Option<u64>,
    output_path: Option<PathBuf>,
    json: bool,
    pretty: bool,
}

fn main() {
    let raw_args: Vec<String> = std::env::args().skip(1).collect();
    let replay_args = parse_args(&raw_args).unwrap_or_else(|e| usage(&format!("{e}\n")));
    eprintln!(
        "warning: `telltale-simulator-replay` is a compatibility summary CLI; prefer the shared viewer/webapp for graph, time-travel, and run-insight debugging"
    );

    let scenario =
        Scenario::from_file(&replay_args.scenario_path).unwrap_or_else(|e| fatal(&e.to_string()));

    let checkpoint = PersistedReplayArtifact::from_path(&replay_args.checkpoint_path)
        .and_then(PersistedReplayArtifact::into_checkpoint_artifact)
        .unwrap_or_else(|e| fatal(&e));

    let field = scenario
        .field
        .as_ref()
        .unwrap_or_else(|| fatal("scenario is missing built-in field parameters"));
    let handler = handler_from_field(field);
    let result = resume_with_checkpoint_artifact(
        &scenario,
        &checkpoint,
        handler.as_ref(),
        None,
        replay_args.rounds,
    )
    .unwrap_or_else(|e| fatal(&e));

    if replay_args.json {
        let output = ReplayOutput {
            scenario: scenario.name.clone(),
            stats: ReplayStatsOutput {
                execution_regime: result.stats.execution_regime,
                theorem_profile: result.stats.theorem_profile,
                final_tick: result.stats.final_tick,
                rounds_executed: result.stats.rounds_executed,
            },
            replay: ReplayArtifactOutput {
                checkpoint_tick: checkpoint.tick,
                obs_events: u64::try_from(result.replay.obs_trace.len()).unwrap_or(u64::MAX),
                effect_events: u64::try_from(result.replay.effect_trace.len()).unwrap_or(u64::MAX),
                reconfiguration_events: u64::try_from(result.replay.reconfiguration_trace.len())
                    .unwrap_or(u64::MAX),
            },
            analysis: ReplayAnalysisOutput {
                normalized_observability: result.analysis.normalized_observability,
            },
            violations: result.violations.clone(),
        };

        let json = if replay_args.pretty {
            serde_json::to_string_pretty(&output)
        } else {
            serde_json::to_string(&output)
        }
        .unwrap_or_else(|e| fatal(&format!("serialize replay output: {e}")));

        if let Some(path) = replay_args.output_path {
            std::fs::write(&path, format!("{json}\n"))
                .unwrap_or_else(|e| fatal(&format!("write {}: {e}", path.display())));
        } else {
            println!("{json}");
        }
    } else if result.violations.is_empty() {
        println!("replay completed (tick {})", result.stats.final_tick);
    } else {
        println!(
            "replay completed with {} violations",
            result.violations.len()
        );
        for v in &result.violations {
            println!("{} @ tick {}: {}", v.property_name, v.tick, v.details);
        }
        std::process::exit(2);
    }
}

fn parse_args(args: &[String]) -> Result<ReplayArgs, String> {
    let mut checkpoint_path: Option<PathBuf> = None;
    let mut scenario_path: Option<PathBuf> = None;
    let mut rounds: Option<u64> = None;
    let mut output_path: Option<PathBuf> = None;
    let mut json = false;
    let mut pretty = false;

    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
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
            "--rounds" => {
                let Some(value) = args.get(i + 1) else {
                    return Err("missing value after --rounds".to_string());
                };
                rounds = Some(
                    value
                        .parse::<u64>()
                        .map_err(|_| format!("invalid --rounds value: {value}"))?,
                );
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
            flag => {
                return Err(format!("unknown argument: {flag}"));
            }
        }
    }

    let checkpoint_path =
        checkpoint_path.ok_or_else(|| "missing --checkpoint <path>".to_string())?;
    let scenario_path = scenario_path.ok_or_else(|| "missing --scenario <path>".to_string())?;
    Ok(ReplayArgs {
        checkpoint_path,
        scenario_path,
        rounds,
        output_path,
        json,
        pretty,
    })
}

#[derive(Debug, serde::Serialize)]
struct ReplayOutput {
    scenario: String,
    stats: ReplayStatsOutput,
    replay: ReplayArtifactOutput,
    analysis: ReplayAnalysisOutput,
    violations: Vec<telltale_simulator::property::PropertyViolation>,
}

#[derive(Debug, serde::Serialize)]
struct ReplayStatsOutput {
    execution_regime: telltale_simulator::scenario::ExecutionRegime,
    theorem_profile: telltale_simulator::scenario::ResolvedTheoremProfile,
    final_tick: u64,
    rounds_executed: u64,
}

#[derive(Debug, serde::Serialize)]
struct ReplayArtifactOutput {
    checkpoint_tick: u64,
    obs_events: u64,
    effect_events: u64,
    reconfiguration_events: u64,
}

#[derive(Debug, serde::Serialize)]
struct ReplayAnalysisOutput {
    normalized_observability: telltale_simulator::analysis::NormalizedObservability,
}

fn usage(msg: &str) -> ! {
    eprintln!("{msg}");
    eprintln!(
        "usage: telltale-simulator-replay --checkpoint <file> --scenario <file> [--rounds N] [--json] [--pretty] [--output <file>]"
    );
    std::process::exit(1);
}

fn fatal(msg: &str) -> ! {
    eprintln!("{msg}");
    std::process::exit(1);
}
