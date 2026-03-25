//! Native single-thread guest-runtime driver.

use crate::effect::EffectHandler;
use crate::engine::{
    ObsEvent, ProtocolMachine, ProtocolMachineConfig, ProtocolMachineError, RunStatus, StepResult,
};
use crate::kernel::ProtocolMachineKernel;
use crate::loader::CodeImage;
use crate::owned::OwnedSession;

/// Native cooperative guest runtime backed by the canonical protocol machine.
#[doc(alias = "GuestRuntime")]
#[derive(Debug)]
pub struct NativeSingleThreadDriver {
    machine: ProtocolMachine,
}

impl NativeSingleThreadDriver {
    /// Create a new guest runtime from protocol-machine config.
    #[must_use]
    pub fn new(config: ProtocolMachineConfig) -> Self {
        Self {
            machine: ProtocolMachine::new(config),
        }
    }

    /// Wrap an existing protocol-machine instance inside this guest runtime.
    #[must_use]
    pub fn with_vm(machine: ProtocolMachine) -> Self {
        Self { machine }
    }

    /// Access the inner protocol machine.
    #[must_use]
    pub fn machine(&self) -> &ProtocolMachine {
        &self.machine
    }

    /// Preferred choreography open path that returns an ownership-bearing handle.
    ///
    /// # Errors
    ///
    /// Returns a `ProtocolMachineError` if the choreography cannot be loaded or claimed.
    pub fn load_choreography_owned(
        &mut self,
        image: &CodeImage,
        owner_id: impl Into<String>,
    ) -> Result<OwnedSession, ProtocolMachineError> {
        self.machine.load_choreography_owned(image, owner_id)
    }

    /// Execute one scheduler round via the protocol-machine kernel.
    ///
    /// # Errors
    ///
    /// Returns a `ProtocolMachineError` if a coroutine faults.
    pub fn step_round(
        &mut self,
        handler: &dyn EffectHandler,
        n: usize,
    ) -> Result<StepResult, ProtocolMachineError> {
        ProtocolMachineKernel::step_round(&mut self.machine, handler, n)
    }

    /// Run up to `max_rounds` with concurrency `n` via the protocol-machine kernel.
    ///
    /// # Errors
    ///
    /// Returns a `ProtocolMachineError` if a coroutine faults.
    pub fn run(
        &mut self,
        handler: &dyn EffectHandler,
        max_rounds: usize,
        n: usize,
    ) -> Result<RunStatus, ProtocolMachineError> {
        ProtocolMachineKernel::run_concurrent(&mut self.machine, handler, max_rounds, n)
    }

    /// Borrow the observable trace.
    #[must_use]
    pub fn trace(&self) -> &[ObsEvent] {
        self.machine.trace()
    }
}
