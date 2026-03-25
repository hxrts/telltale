//! Deterministic protocol-machine kernel API.
//!
//! This module provides the canonical instruction-step entrypoints for the
//! cooperative protocol-machine state machine. Driver layers (native single-thread, wasm,
//! and adapter backends) should call this API instead of re-implementing
//! stepping logic.

use crate::effect::EffectHandler;
use crate::engine::{ProtocolMachineError, RunStatus, StepResult};
use crate::scheduler::Scheduler;

/// Runtime machine that can execute one kernel scheduler round.
pub trait KernelMachine {
    /// Execute one scheduler round in the machine's native state.
    ///
    /// # Errors
    ///
    /// Returns a `ProtocolMachineError` if a coroutine faults.
    fn kernel_step_round(
        &mut self,
        handler: &dyn EffectHandler,
        n: usize,
    ) -> Result<StepResult, ProtocolMachineError>;
}

/// Canonical cooperative kernel entrypoints.
#[derive(Debug, Default, Clone, Copy)]
pub struct ProtocolMachineKernel;

impl ProtocolMachineKernel {
    /// Select a ready coroutine using kernel-owned scheduler policy semantics.
    ///
    /// `has_progress` models policy-relevant progress state, while
    /// `is_eligible` is a runtime/driver eligibility gate (e.g. paused role,
    /// lane/session wave constraints). Ineligible candidates are rescheduled.
    pub fn select_ready_eligible<FProgress, FEligible>(
        scheduler: &mut Scheduler,
        has_progress: FProgress,
        mut is_eligible: FEligible,
    ) -> Option<usize>
    where
        FProgress: Fn(usize) -> bool + Copy,
        FEligible: FnMut(usize) -> bool,
    {
        let attempts = scheduler.ready_count();
        for _ in 0..attempts {
            let id = scheduler.pick_runnable(has_progress)?;
            if is_eligible(id) {
                return Some(id);
            }
            scheduler.reschedule(id);
        }
        None
    }

    /// Execute one scheduler round through the canonical kernel path.
    ///
    /// # Errors
    ///
    /// Returns a `ProtocolMachineError` if a coroutine faults.
    pub fn step_round<M: KernelMachine>(
        machine: &mut M,
        handler: &dyn EffectHandler,
        n: usize,
    ) -> Result<StepResult, ProtocolMachineError> {
        machine.kernel_step_round(handler, n)
    }

    /// Run until completion/stuck or `max_rounds` is reached via the kernel.
    ///
    /// # Errors
    ///
    /// Returns a `ProtocolMachineError` if any coroutine faults.
    pub fn run_concurrent<M: KernelMachine>(
        machine: &mut M,
        handler: &dyn EffectHandler,
        max_rounds: usize,
        concurrency: usize,
    ) -> Result<RunStatus, ProtocolMachineError> {
        for _ in 0..max_rounds {
            match Self::step_round(machine, handler, concurrency)? {
                StepResult::AllDone => return Ok(RunStatus::AllDone),
                StepResult::Stuck => return Ok(RunStatus::Stuck),
                StepResult::Continue => {}
            }
        }
        Ok(RunStatus::MaxRoundsExceeded)
    }

    /// Run with single-lane cooperative scheduling via the kernel.
    ///
    /// # Errors
    ///
    /// Returns a `ProtocolMachineError` if any coroutine faults.
    pub fn run<M: KernelMachine>(
        machine: &mut M,
        handler: &dyn EffectHandler,
        max_steps: usize,
    ) -> Result<RunStatus, ProtocolMachineError> {
        Self::run_concurrent(machine, handler, max_steps, 1)
    }
}
