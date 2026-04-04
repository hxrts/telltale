//! Shared simulator execution loop and middleware composition.

use std::time::Duration;

use telltale_machine::model::effects::EffectHandler;
use telltale_machine::StepResult;

use crate::backend::SimulationMachine;
use crate::fault::{
    AdversaryBudgetRecord, AdversaryCheckpointState, AdversaryInjector, AdversarySummary,
    AssumptionDiagnostic, ScheduledAdversary,
};
use crate::network::{NetworkCheckpointState, NetworkModel};
use crate::reconfiguration::{
    ReconfigurationCheckpointState, ReconfigurationController, ReconfigurationRecord,
    ReconfigurationSummary,
};
use crate::rng::SimRng;
use crate::scenario::Scenario;

#[allow(clippy::large_enum_variant)]
enum ScenarioTransport<'a> {
    Adversary(AdversaryInjector<&'a dyn EffectHandler>),
    Network(NetworkModel<AdversaryInjector<&'a dyn EffectHandler>>),
}

#[derive(Debug, Clone)]
enum ScenarioTransportCheckpoint {
    Adversary(AdversaryCheckpointState),
    Network {
        network: NetworkCheckpointState,
        adversary: Box<AdversaryCheckpointState>,
    },
}

#[derive(Debug, Clone)]
pub(crate) struct ScenarioMiddlewareCheckpoint {
    transport: ScenarioTransportCheckpoint,
    reconfiguration: ReconfigurationCheckpointState,
}

/// Shared middleware stack for one scenario execution.
pub struct ScenarioMiddleware<'a> {
    transport: ScenarioTransport<'a>,
    reconfiguration: ReconfigurationController,
}

impl<'a> ScenarioMiddleware<'a> {
    /// Build middleware from scenario config and a host effect handler.
    pub fn from_scenario(
        scenario: &Scenario,
        handler: &'a dyn EffectHandler,
        tick_duration: Duration,
    ) -> Result<Self, String> {
        let mut rng = SimRng::new(scenario.seed);
        let program = scenario.adversary_program()?;
        let adversary = AdversaryInjector::new(handler, program, rng.fork());
        let reconfiguration =
            ReconfigurationController::new(scenario.reconfiguration_schedule()?, rng.fork());

        let transport = if scenario.requires_network_model() {
            let cfg = scenario.network_config().unwrap_or_default();
            ScenarioTransport::Network(NetworkModel::new(adversary, cfg, rng.fork(), tick_duration))
        } else {
            ScenarioTransport::Adversary(adversary)
        };

        Ok(Self {
            transport,
            reconfiguration,
        })
    }

    pub(crate) fn from_checkpoint(
        scenario: &Scenario,
        handler: &'a dyn EffectHandler,
        tick_duration: Duration,
        checkpoint: &ScenarioMiddlewareCheckpoint,
    ) -> Result<Self, String> {
        let middleware = Self::from_scenario(scenario, handler, tick_duration)?;
        middleware.restore_checkpoint_state(checkpoint)?;
        Ok(middleware)
    }

    fn prepare_round(
        &self,
        machine: &mut SimulationMachine,
        next_tick: u64,
        next_logical_step: u64,
    ) -> Result<(), String> {
        match &self.transport {
            ScenarioTransport::Network(net) => {
                self.reconfiguration.tick(
                    next_tick,
                    next_logical_step,
                    machine.trace(),
                    Some(net),
                )?;
                net.inner()
                    .tick(next_tick, next_logical_step, machine.trace())
                    .map_err(|e| format!("adversary middleware tick: {e}"))?;
                net.inner()
                    .deliver(next_tick, |sid, from, to, val| {
                        net.route_external(next_tick, sid, from, to, val, |sid, from, to, val| {
                            machine
                                .inject_message(sid, from, to, val)
                                .map_err(|e| e.to_string())
                        })?;
                        Ok(telltale_machine::buffer::EnqueueResult::Ok)
                    })
                    .map_err(|e| format!("adversary middleware deliver: {e}"))?;
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
                    .map_err(|e| format!("adversary middleware crashed_roles: {e}"))?;
                machine.set_paused_roles(&paused_roles);
                Ok(())
            }
            ScenarioTransport::Adversary(adversary) => {
                self.reconfiguration.tick(
                    next_tick,
                    next_logical_step,
                    machine.trace(),
                    Option::<&NetworkModel<AdversaryInjector<&'a dyn EffectHandler>>>::None,
                )?;
                adversary
                    .tick(next_tick, next_logical_step, machine.trace())
                    .map_err(|e| format!("adversary middleware tick: {e}"))?;
                adversary
                    .deliver(next_tick, |sid, from, to, val| {
                        machine
                            .inject_message(sid, from, to, val)
                            .map_err(|e| e.to_string())
                    })
                    .map_err(|e| format!("adversary middleware deliver: {e}"))?;
                let paused_roles = adversary
                    .crashed_roles()
                    .map_err(|e| format!("adversary middleware crashed_roles: {e}"))?;
                machine.set_paused_roles(&paused_roles);
                Ok(())
            }
        }
    }

    fn step_round(
        &self,
        machine: &mut SimulationMachine,
        concurrency: usize,
    ) -> Result<StepResult, String> {
        match &self.transport {
            ScenarioTransport::Network(net) => machine.step_round(net, concurrency),
            ScenarioTransport::Adversary(adversary) => machine.step_round(adversary, concurrency),
        }
        .map_err(|e| format!("protocol machine error: {e}"))
    }

    /// Resolved adversary schedule for the run.
    pub fn adversary_schedule(&self) -> Vec<ScheduledAdversary> {
        match &self.transport {
            ScenarioTransport::Network(net) => net.inner().program(),
            ScenarioTransport::Adversary(adversary) => adversary.program(),
        }
    }

    /// Budget-consumption history recorded by the adversary middleware.
    pub fn adversary_budget_history(&self) -> Result<Vec<AdversaryBudgetRecord>, String> {
        match &self.transport {
            ScenarioTransport::Network(net) => net.inner().budget_history(),
            ScenarioTransport::Adversary(adversary) => adversary.budget_history(),
        }
    }

    /// Assumption-bundle diagnostics recorded by the adversary middleware.
    pub fn adversary_assumption_diagnostics(&self) -> Result<Vec<AssumptionDiagnostic>, String> {
        match &self.transport {
            ScenarioTransport::Network(net) => net.inner().assumption_diagnostics(),
            ScenarioTransport::Adversary(adversary) => adversary.assumption_diagnostics(),
        }
    }

    /// Adversary summary for the run.
    pub fn adversary_summary(&self) -> Result<AdversarySummary, String> {
        match &self.transport {
            ScenarioTransport::Network(net) => net.inner().summary(),
            ScenarioTransport::Adversary(adversary) => adversary.summary(),
        }
    }

    /// Canonical applied reconfiguration trace.
    pub fn reconfiguration_trace(&self) -> Result<Vec<ReconfigurationRecord>, String> {
        self.reconfiguration.trace()
    }

    /// Reconfiguration accounting summary for the run.
    pub fn reconfiguration_summary(&self) -> Result<ReconfigurationSummary, String> {
        self.reconfiguration.summary()
    }

    pub(crate) fn checkpoint_state(&self) -> Result<ScenarioMiddlewareCheckpoint, String> {
        let transport = match &self.transport {
            ScenarioTransport::Adversary(adversary) => {
                ScenarioTransportCheckpoint::Adversary(adversary.checkpoint_state()?)
            }
            ScenarioTransport::Network(net) => ScenarioTransportCheckpoint::Network {
                network: net.checkpoint_state()?,
                adversary: Box::new(net.inner().checkpoint_state()?),
            },
        };
        Ok(ScenarioMiddlewareCheckpoint {
            transport,
            reconfiguration: self.reconfiguration.checkpoint_state()?,
        })
    }

    fn restore_checkpoint_state(
        &self,
        checkpoint: &ScenarioMiddlewareCheckpoint,
    ) -> Result<(), String> {
        match (&self.transport, &checkpoint.transport) {
            (ScenarioTransport::Adversary(adversary), ScenarioTransportCheckpoint::Adversary(state)) => {
                adversary.restore_state(state)?
            }
            (
                ScenarioTransport::Network(net),
                ScenarioTransportCheckpoint::Network { network, adversary },
            ) => {
                net.restore_state(network)?;
                net.inner().restore_state(adversary)?;
            }
            (ScenarioTransport::Adversary(_), ScenarioTransportCheckpoint::Network { .. })
            | (ScenarioTransport::Network(_), ScenarioTransportCheckpoint::Adversary(_)) => {
                return Err(
                    "checkpoint transport shape does not match the scenario middleware configuration"
                        .to_string(),
                )
            }
        }
        self.reconfiguration
            .restore_state(&checkpoint.reconfiguration)?;
        Ok(())
    }
}

pub struct ExecutionSummary {
    pub rounds_executed: u64,
}

/// Execute scenario rounds with one shared middleware ordering.
pub fn execute_scenario_rounds(
    machine: &mut SimulationMachine,
    _scenario: &Scenario,
    middleware: &ScenarioMiddleware<'_>,
    concurrency: usize,
    max_rounds: u64,
    mut after_round: impl FnMut(&SimulationMachine, u64) -> Result<(), String>,
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
