//! Shared simulator execution loop and middleware composition.

use std::time::Duration;

use telltale_machine::model::effects::EffectHandler;
use telltale_machine::{ProtocolMachine, StepResult};

use crate::fault::FaultInjector;
use crate::network::NetworkModel;
use crate::rng::SimRng;
use crate::scenario::Scenario;

/// Shared middleware stack for one scenario execution.
pub enum ScenarioMiddleware<'a> {
    Fault(FaultInjector<&'a dyn EffectHandler>),
    Network(NetworkModel<FaultInjector<&'a dyn EffectHandler>>),
}

impl<'a> ScenarioMiddleware<'a> {
    /// Build middleware from scenario config and a host effect handler.
    pub fn from_scenario(
        scenario: &Scenario,
        handler: &'a dyn EffectHandler,
        tick_duration: Duration,
    ) -> Result<Self, String> {
        let mut rng = SimRng::new(scenario.seed);
        let schedule = scenario.fault_schedule()?;
        let fault = FaultInjector::new(handler, schedule, rng.fork());

        Ok(match scenario.network_config() {
            Some(cfg) => Self::Network(NetworkModel::new(fault, cfg, rng.fork(), tick_duration)),
            None => Self::Fault(fault),
        })
    }

    fn prepare_round(
        &self,
        machine: &mut ProtocolMachine,
        next_tick: u64,
        next_logical_step: u64,
    ) -> Result<(), String> {
        match self {
            Self::Network(net) => {
                net.inner()
                    .tick(next_tick, next_logical_step, machine.trace())
                    .map_err(|e| format!("fault middleware tick: {e}"))?;
                net.inner()
                    .deliver(next_tick, |sid, from, to, val| {
                        net.route_external(next_tick, sid, from, to, val, |sid, from, to, val| {
                            machine
                                .inject_message(sid, from, to, val)
                                .map_err(|e| e.to_string())
                        })?;
                        Ok(telltale_machine::buffer::EnqueueResult::Ok)
                    })
                    .map_err(|e| format!("fault middleware deliver: {e}"))?;
                net.set_tick(next_tick);
                net.deliver(next_tick, |sid, from, to, val| {
                    machine
                        .inject_message(sid, from, to, val)
                        .map_err(|e| e.to_string())
                })
                .map_err(|e| format!("network middleware deliver: {e}"))?;
                let paused_roles = net
                    .inner()
                    .crashed_roles()
                    .map_err(|e| format!("fault middleware crashed_roles: {e}"))?;
                machine.set_paused_roles(&paused_roles);
                Ok(())
            }
            Self::Fault(fault) => {
                fault
                    .tick(next_tick, next_logical_step, machine.trace())
                    .map_err(|e| format!("fault middleware tick: {e}"))?;
                fault
                    .deliver(next_tick, |sid, from, to, val| {
                        machine
                            .inject_message(sid, from, to, val)
                            .map_err(|e| e.to_string())
                    })
                    .map_err(|e| format!("fault middleware deliver: {e}"))?;
                let paused_roles = fault
                    .crashed_roles()
                    .map_err(|e| format!("fault middleware crashed_roles: {e}"))?;
                machine.set_paused_roles(&paused_roles);
                Ok(())
            }
        }
    }

    fn step_round(
        &self,
        machine: &mut ProtocolMachine,
        concurrency: usize,
    ) -> Result<StepResult, String> {
        match self {
            Self::Network(net) => machine.step_round(net, concurrency),
            Self::Fault(fault) => machine.step_round(fault, concurrency),
        }
        .map_err(|e| format!("protocol machine error: {e}"))
    }
}

pub struct ExecutionSummary {
    pub rounds_executed: u64,
}

/// Execute scenario rounds with one shared middleware ordering.
pub fn execute_scenario_rounds(
    machine: &mut ProtocolMachine,
    _scenario: &Scenario,
    middleware: &ScenarioMiddleware<'_>,
    concurrency: usize,
    max_rounds: u64,
    mut after_round: impl FnMut(&ProtocolMachine, u64) -> Result<(), String>,
) -> Result<ExecutionSummary, String> {
    let mut rounds_executed = 0_u64;

    for _ in 0..max_rounds {
        let next_tick = machine.clock().tick + 1;
        let next_logical_step = rounds_executed.saturating_add(1);

        middleware.prepare_round(machine, next_tick, next_logical_step)?;

        match middleware.step_round(machine, concurrency)? {
            StepResult::AllDone | StepResult::Stuck => break,
            StepResult::Continue => {}
        }

        rounds_executed = rounds_executed.saturating_add(1);
        after_round(machine, rounds_executed)?;
    }
    Ok(ExecutionSummary { rounds_executed })
}
