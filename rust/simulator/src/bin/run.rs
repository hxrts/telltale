//! Run one simulator harness config file.

use serde::Serialize;
use std::path::PathBuf;

use telltale_simulator::contracts::evaluate_contracts;
use telltale_simulator::harness::{HarnessConfig, MaterialAdapter, SimulationHarness};

struct RunArgs {
    config_path: PathBuf,
    output_path: Option<PathBuf>,
    pretty: bool,
}

fn main() {
    let raw_args: Vec<String> = std::env::args().skip(1).collect();
    let args = parse_args(&raw_args).unwrap_or_else(|e| usage(&e));

    let config_path = args.config_path;
    let config = HarnessConfig::from_file(&config_path).unwrap_or_else(|e| fatal(&e));

    let adapter = MaterialAdapter::from_scenario(&config.spec.scenario);
    let harness = SimulationHarness::new(&adapter);

    let result = harness.run(&config.spec).unwrap_or_else(|e| fatal(&e));
    let contracts = evaluate_contracts(&result, &config.contracts);

    let output = RunOutput {
        scenario: config.spec.scenario.name.clone(),
        trace: result.trace,
        violations: result
            .violations
            .into_iter()
            .map(|violation| ViolationOutput {
                property_name: violation.property_name,
                tick: violation.tick,
                details: violation.details,
            })
            .collect(),
        stats: StatsOutput {
            seed: result.stats.seed,
            concurrency: result.stats.concurrency,
            rounds_executed: result.stats.rounds_executed,
            final_tick: result.stats.final_tick,
            total_obs_events: result.stats.total_obs_events,
            total_invoked_events: result.stats.total_invoked_events,
            checkpoint_writes: result.stats.checkpoint_writes,
        },
        replay: ReplayOutput {
            obs_events: result.replay.obs_trace.len(),
            effect_events: result.replay.effect_trace.len(),
            output_condition_checks: result.replay.output_condition_trace.len(),
        },
        contracts,
    };

    let json = if args.pretty {
        serde_json::to_string_pretty(&output)
    } else {
        serde_json::to_string(&output)
    }
    .unwrap_or_else(|e| fatal(&format!("serialize output: {e}")));

    if let Some(path) = args.output_path {
        std::fs::write(&path, format!("{json}\n"))
            .unwrap_or_else(|e| fatal(&format!("write {}: {e}", path.display())));
    } else {
        println!("{json}");
    }

    if !output.contracts.passed {
        std::process::exit(2);
    }
}

fn parse_args(args: &[String]) -> Result<RunArgs, String> {
    let mut config_path: Option<PathBuf> = None;
    let mut output_path: Option<PathBuf> = None;
    let mut pretty = false;

    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--config" => {
                let Some(path) = args.get(i + 1) else {
                    return Err("missing value after --config".to_string());
                };
                config_path = Some(PathBuf::from(path));
                i += 2;
            }
            "--output" => {
                let Some(path) = args.get(i + 1) else {
                    return Err("missing value after --output".to_string());
                };
                output_path = Some(PathBuf::from(path));
                i += 2;
            }
            "--pretty" => {
                pretty = true;
                i += 1;
            }
            flag => return Err(format!("unknown argument: {flag}")),
        }
    }

    let config_path = config_path.ok_or_else(|| "missing --config <path>".to_string())?;
    Ok(RunArgs {
        config_path,
        output_path,
        pretty,
    })
}

#[derive(Debug, Serialize)]
struct RunOutput {
    scenario: String,
    trace: telltale_simulator::trace::Trace,
    violations: Vec<ViolationOutput>,
    stats: StatsOutput,
    replay: ReplayOutput,
    contracts: telltale_simulator::contracts::ContractCheckReport,
}

#[derive(Debug, Serialize)]
struct ViolationOutput {
    property_name: String,
    tick: u64,
    details: String,
}

#[derive(Debug, Serialize)]
struct StatsOutput {
    seed: u64,
    concurrency: u64,
    rounds_executed: u64,
    final_tick: u64,
    total_obs_events: usize,
    total_invoked_events: usize,
    checkpoint_writes: usize,
}

#[derive(Debug, Serialize)]
struct ReplayOutput {
    obs_events: usize,
    effect_events: usize,
    output_condition_checks: usize,
}

fn usage(msg: &str) -> ! {
    eprintln!("{msg}");
    eprintln!("usage: telltale-simulator-run --config <file> [--output <file>] [--pretty]");
    std::process::exit(1);
}

fn fatal(msg: &str) -> ! {
    eprintln!("{msg}");
    std::process::exit(1);
}
