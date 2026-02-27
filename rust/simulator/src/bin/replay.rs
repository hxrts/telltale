//! Replay a simulation run from a checkpoint.

use std::path::PathBuf;

use telltale_simulator::fault::FaultInjector;
use telltale_simulator::handler_from_material;
use telltale_simulator::network::NetworkModel;
use telltale_simulator::property::{PropertyContext, PropertyMonitor};
use telltale_simulator::rng::SimRng;
use telltale_simulator::scenario::Scenario;
use telltale_vm::vm::{StepResult, VM};

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
    let mut vm: VM = serde_json::from_slice(&checkpoint).unwrap_or_else(|e| fatal(&e.to_string()));

    let handler = handler_from_material(&scenario.material);
    let max_rounds = replay_args.rounds.unwrap_or(scenario.steps);
    let concurrency = usize::try_from(scenario.concurrency)
        .unwrap_or_else(|_| fatal("scenario.concurrency exceeds usize"));

    let mut rng = SimRng::new(scenario.seed);
    let mut monitor = scenario
        .property_monitor()
        .unwrap_or_else(|e| fatal(&format!("properties: {e}")))
        .unwrap_or_else(|| PropertyMonitor::new(Vec::new()));
    let schedule = scenario
        .fault_schedule()
        .unwrap_or_else(|e| fatal(&format!("fault schedule: {e}")));
    let fault = FaultInjector::new(handler.as_ref(), schedule, rng.fork());

    let mut fault_only = None;
    let mut network = None;
    if let Some(cfg) = scenario.network_config() {
        network = Some(NetworkModel::new(
            fault,
            cfg,
            rng.fork(),
            vm.clock().tick_duration,
        ));
    } else {
        fault_only = Some(fault);
    }

    let mut rounds_executed = 0_u64;
    for _ in 0..max_rounds {
        let next_tick = vm.clock().tick + 1;
        let next_logical_step = rounds_executed.saturating_add(1);
        if let Some(net) = &network {
            net.inner()
                .tick(next_tick, next_logical_step, vm.trace())
                .unwrap_or_else(|e| fatal(&format!("fault middleware tick: {e}")));
            net.inner()
                .deliver(next_tick, |sid, from, to, val| {
                    vm.inject_message(sid, from, to, val)
                        .map_err(|e| e.to_string())
                })
                .unwrap_or_else(|e| fatal(&format!("fault middleware deliver: {e}")));
            net.set_tick(next_tick);
            net.deliver(next_tick, |sid, from, to, val| {
                vm.inject_message(sid, from, to, val)
                    .map_err(|e| e.to_string())
            })
            .unwrap_or_else(|e| fatal(&format!("network middleware deliver: {e}")));
            let paused_roles = net
                .inner()
                .crashed_roles()
                .unwrap_or_else(|e| fatal(&format!("fault middleware crashed_roles: {e}")));
            vm.set_paused_roles(&paused_roles);
            match vm.step_round(net, concurrency) {
                Ok(StepResult::AllDone | StepResult::Stuck) => break,
                Ok(StepResult::Continue) => {}
                Err(e) => fatal(&format!("vm error: {e}")),
            }
        } else {
            let fault = fault_only
                .as_ref()
                .unwrap_or_else(|| fatal("internal replay error: missing fault middleware"));
            fault
                .tick(next_tick, next_logical_step, vm.trace())
                .unwrap_or_else(|e| fatal(&format!("fault middleware tick: {e}")));
            fault
                .deliver(next_tick, |sid, from, to, val| {
                    vm.inject_message(sid, from, to, val)
                        .map_err(|e| e.to_string())
                })
                .unwrap_or_else(|e| fatal(&format!("fault middleware deliver: {e}")));
            let paused_roles = fault
                .crashed_roles()
                .unwrap_or_else(|e| fatal(&format!("fault middleware crashed_roles: {e}")));
            vm.set_paused_roles(&paused_roles);
            match vm.step_round(fault, concurrency) {
                Ok(StepResult::AllDone | StepResult::Stuck) => break,
                Ok(StepResult::Continue) => {}
                Err(e) => fatal(&format!("vm error: {e}")),
            }
        }
        rounds_executed = rounds_executed.saturating_add(1);

        let ctx = PropertyContext {
            tick: vm.clock().tick,
            trace: vm.trace(),
            sessions: vm.sessions(),
            coroutines: vm.coroutines(),
        };
        monitor.check(&ctx);
    }

    if monitor.violations().is_empty() {
        println!("replay completed (tick {})", vm.clock().tick);
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
