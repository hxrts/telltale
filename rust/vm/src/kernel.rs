//! Deterministic VM kernel API.
//!
//! This module provides the canonical instruction-step entrypoints for the
//! cooperative VM state machine. Driver layers (native single-thread, wasm,
//! and adapter backends) should call this API instead of re-implementing
//! stepping logic.

use crate::effect::EffectHandler;
use crate::scheduler::Scheduler;
use crate::vm::{StepResult, VMError};

/// Runtime machine that can execute one kernel scheduler round.
pub trait KernelMachine {
    /// Execute one scheduler round in the machine's native state.
    ///
    /// # Errors
    ///
    /// Returns a `VMError` if a coroutine faults.
    fn kernel_step_round(
        &mut self,
        handler: &dyn EffectHandler,
        n: usize,
    ) -> Result<StepResult, VMError>;
}

/// Canonical cooperative kernel entrypoints.
#[derive(Debug, Default, Clone, Copy)]
pub struct VMKernel;

impl VMKernel {
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
            let id = scheduler.pick_runnable(&has_progress)?;
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
    /// Returns a `VMError` if a coroutine faults.
    pub fn step_round<M: KernelMachine>(
        vm: &mut M,
        handler: &dyn EffectHandler,
        n: usize,
    ) -> Result<StepResult, VMError> {
        vm.kernel_step_round(handler, n)
    }

    /// Run until completion/stuck or `max_rounds` is reached via the kernel.
    ///
    /// # Errors
    ///
    /// Returns a `VMError` if any coroutine faults.
    pub fn run_concurrent<M: KernelMachine>(
        vm: &mut M,
        handler: &dyn EffectHandler,
        max_rounds: usize,
        concurrency: usize,
    ) -> Result<(), VMError> {
        for _ in 0..max_rounds {
            match Self::step_round(vm, handler, concurrency)? {
                StepResult::AllDone | StepResult::Stuck => return Ok(()),
                StepResult::Continue => {}
            }
        }
        Ok(())
    }

    /// Run with single-lane cooperative scheduling via the kernel.
    ///
    /// # Errors
    ///
    /// Returns a `VMError` if any coroutine faults.
    pub fn run<M: KernelMachine>(
        vm: &mut M,
        handler: &dyn EffectHandler,
        max_steps: usize,
    ) -> Result<(), VMError> {
        Self::run_concurrent(vm, handler, max_steps, 1)
    }
}
