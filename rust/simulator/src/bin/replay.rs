//! Replay a simulation run from a checkpoint.

use std::path::PathBuf;

use telltale_simulator::fault::FaultInjector;
use telltale_simulator::network::NetworkModel;
use telltale_simulator::property::{PropertyContext, PropertyMonitor};
use telltale_simulator::rng::SimRng;
use telltale_simulator::scenario::Scenario;
use telltale_simulator::{continuum::ContinuumFieldHandler, hamiltonian::HamiltonianHandler};
use telltale_simulator::{ising::IsingHandler, material::MaterialParams};
use telltale_vm::effect::EffectHandler;
use telltale_vm::vm::{StepResult, VM};

fn main() {
    let mut args = std::env::args().skip(1);
    let mut checkpoint_path: Option<PathBuf> = None;
    let mut scenario_path: Option<PathBuf> = None;
    let mut rounds: Option<usize> = None;

    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--checkpoint" => checkpoint_path = args.next().map(PathBuf::from),
            "--scenario" => scenario_path = args.next().map(PathBuf::from),
            "--rounds" => {
                rounds = args.next().and_then(|s| s.parse::<usize>().ok());
            }
            _ => {}
        }
    }

    let checkpoint_path = checkpoint_path.unwrap_or_else(|| usage("missing --checkpoint <path>"));
    let scenario_path = scenario_path.unwrap_or_else(|| usage("missing --scenario <path>"));

    let scenario = Scenario::from_file(&scenario_path).unwrap_or_else(|e| fatal(&e.to_string()));

    let checkpoint = std::fs::read(&checkpoint_path).unwrap_or_else(|e| fatal(&e.to_string()));
    let mut vm: VM = serde_json::from_slice(&checkpoint).unwrap_or_else(|e| fatal(&e.to_string()));

    let handler = build_handler(&scenario.material);
    let max_rounds = rounds.unwrap_or(scenario.steps);

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

    for _ in 0..max_rounds {
        let next_tick = vm.clock().tick + 1;
        if let Some(net) = &network {
            net.inner().tick(next_tick, vm.trace());
            net.inner().deliver(next_tick, |sid, from, to, val| {
                vm.inject_message(sid, from, to, val)
                    .map_err(|e| e.to_string())
            });
            net.set_tick(next_tick);
            net.deliver(next_tick, |sid, from, to, val| {
                vm.inject_message(sid, from, to, val)
                    .map_err(|e| e.to_string())
            });
            vm.set_paused_roles(&net.inner().crashed_roles());
            match vm.step_round(net, scenario.concurrency) {
                Ok(StepResult::AllDone | StepResult::Stuck) => break,
                Ok(StepResult::Continue) => {}
                Err(e) => fatal(&format!("vm error: {e}")),
            }
        } else {
            let fault = fault_only.as_ref().expect("fault injector");
            fault.tick(next_tick, vm.trace());
            fault.deliver(next_tick, |sid, from, to, val| {
                vm.inject_message(sid, from, to, val)
                    .map_err(|e| e.to_string())
            });
            vm.set_paused_roles(&fault.crashed_roles());
            match vm.step_round(fault, scenario.concurrency) {
                Ok(StepResult::AllDone | StepResult::Stuck) => break,
                Ok(StepResult::Continue) => {}
                Err(e) => fatal(&format!("vm error: {e}")),
            }
        }

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

fn build_handler(material: &MaterialParams) -> Box<dyn EffectHandler> {
    match material {
        MaterialParams::MeanField(params) => Box::new(IsingHandler::new(params.clone())),
        MaterialParams::Hamiltonian(params) => Box::new(HamiltonianHandler::new(params.clone())),
        MaterialParams::ContinuumField(params) => {
            Box::new(ContinuumFieldHandler::new(params.clone()))
        }
    }
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
