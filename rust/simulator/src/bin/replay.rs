//! Replay a simulation run from a checkpoint.

use std::path::PathBuf;

use telltale_machine::ProtocolMachine;
use telltale_simulator::backend::SimulationMachine;
use telltale_simulator::execution::{execute_scenario_rounds, ScenarioMiddleware};
use telltale_simulator::handler_from_material;
use telltale_simulator::property::{PropertyContext, PropertyMonitor};
use telltale_simulator::scenario::Scenario;

struct ReplayArgs {
    checkpoint_path: PathBuf,
    scenario_path: PathBuf,
    rounds: Option<u64>,
}

#[allow(clippy::too_many_lines)]
fn main() {
    let raw_args: Vec<String> = std::env::args().skip(1).collect();
    let replay_args = parse_args(&raw_args).unwrap_or_else(|e| usage(&format!("{e}\n")));

    let scenario =
        Scenario::from_file(&replay_args.scenario_path).unwrap_or_else(|e| fatal(&e.to_string()));

    let checkpoint =
        std::fs::read(&replay_args.checkpoint_path).unwrap_or_else(|e| fatal(&e.to_string()));
    let machine: ProtocolMachine =
        serde_json::from_slice(&checkpoint).unwrap_or_else(|e| fatal(&e.to_string()));
    let mut machine = SimulationMachine::Canonical(machine);

    let material = scenario
        .material
        .as_ref()
        .unwrap_or_else(|| fatal("scenario is missing built-in material parameters"));
    let handler = handler_from_material(material);
    let max_rounds = replay_args.rounds.unwrap_or(scenario.steps);
    let concurrency = usize::try_from(
        scenario
            .resolved_execution()
            .unwrap_or_else(|e| fatal(&e))
            .scheduler_concurrency,
    )
    .unwrap_or_else(|_| fatal("scenario.execution.scheduler_concurrency exceeds usize"));

    let mut monitor = scenario
        .property_monitor()
        .unwrap_or_else(|e| fatal(&format!("properties: {e}")))
        .unwrap_or_else(|| PropertyMonitor::new(Vec::new()));
    let middleware = ScenarioMiddleware::from_scenario(
        &scenario,
        handler.as_ref(),
        machine.clock().tick_duration,
    )
    .unwrap_or_else(|e| fatal(&format!("middleware setup: {e}")));

    let _execution = execute_scenario_rounds(
        &mut machine,
        &scenario,
        &middleware,
        concurrency,
        max_rounds,
        |machine, _completed_rounds| {
            let session_snapshots = machine.session_snapshots();
            let coroutine_snapshots = machine.coroutines();
            let ctx = PropertyContext {
                tick: machine.clock().tick,
                trace: machine.trace(),
                sessions: &session_snapshots,
                coroutines: &coroutine_snapshots,
            };
            monitor.check(&ctx);
            Ok(())
        },
    )
    .unwrap_or_else(|e| fatal(&e));

    if monitor.violations().is_empty() {
        println!("replay completed (tick {})", machine.clock().tick);
    } else {
        println!(
            "replay completed with {} violations",
            monitor.violations().len()
        );
        for v in monitor.violations() {
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
