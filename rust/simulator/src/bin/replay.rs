//! Replay a simulation run from a checkpoint.
//!
//! This compatibility CLI keeps a terse textual summary for terminal use.
//! Rich human-facing inspection should prefer the shared viewer/webapp layers.

use std::path::PathBuf;

use telltale_machine::ProtocolMachine;
use telltale_simulator::handler_from_field;
use telltale_simulator::resume_with_scenario_from_checkpoint;
use telltale_simulator::scenario::Scenario;

struct ReplayArgs {
    checkpoint_path: PathBuf,
    scenario_path: PathBuf,
    rounds: Option<u64>,
}

fn main() {
    let raw_args: Vec<String> = std::env::args().skip(1).collect();
    let replay_args = parse_args(&raw_args).unwrap_or_else(|e| usage(&format!("{e}\n")));
    eprintln!(
        "warning: `telltale-simulator-replay` is a compatibility summary CLI; prefer the shared viewer/webapp for graph, time-travel, and run-insight debugging"
    );

    let scenario =
        Scenario::from_file(&replay_args.scenario_path).unwrap_or_else(|e| fatal(&e.to_string()));

    let checkpoint =
        std::fs::read(&replay_args.checkpoint_path).unwrap_or_else(|e| fatal(&e.to_string()));
    let machine: ProtocolMachine =
        serde_cbor::from_slice(&checkpoint).unwrap_or_else(|e| fatal(&e.to_string()));

    let field = scenario
        .field
        .as_ref()
        .unwrap_or_else(|| fatal("scenario is missing built-in field parameters"));
    let handler = handler_from_field(field);
    let result = resume_with_scenario_from_checkpoint(
        &scenario,
        machine,
        handler.as_ref(),
        None,
        replay_args.rounds,
    )
    .unwrap_or_else(|e| fatal(&e));

    if result.violations.is_empty() {
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
    })
}

fn usage(msg: &str) -> ! {
    eprintln!("{msg}");
    eprintln!(
        "usage: telltale-simulator-replay --checkpoint <file> --scenario <file> [--rounds N]"
    );
    std::process::exit(1);
}

fn fatal(msg: &str) -> ! {
    eprintln!("{msg}");
    std::process::exit(1);
}
