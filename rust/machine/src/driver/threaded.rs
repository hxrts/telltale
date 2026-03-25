//! Native threaded guest-runtime driver.

use crate::effect::EffectHandler;
use crate::engine::{ObsEvent, ProtocolMachineConfig, ProtocolMachineError, RunStatus, StepResult};
use crate::loader::CodeImage;
use crate::owned::OwnedSession;
use crate::threaded::ThreadedProtocolMachine;

/// Native threaded guest runtime backed by the threaded protocol machine.
#[doc(alias = "ThreadedGuestRuntime")]
pub struct NativeThreadedDriver {
    machine: ThreadedProtocolMachine,
}

impl NativeThreadedDriver {
    /// Create a threaded guest runtime with explicit worker count.
    #[must_use]
    pub fn with_workers(config: ProtocolMachineConfig, workers: usize) -> Self {
        Self {
            machine: ThreadedProtocolMachine::with_workers(config, workers),
        }
    }

    /// Create a threaded guest runtime with auto worker count.
    #[must_use]
    pub fn auto(config: ProtocolMachineConfig) -> Self {
        Self {
            machine: ThreadedProtocolMachine::auto(config),
        }
    }

    /// Wrap an existing threaded protocol-machine instance.
    #[must_use]
    pub fn with_vm(machine: ThreadedProtocolMachine) -> Self {
        Self { machine }
    }

    /// Access the inner threaded protocol machine.
    #[must_use]
    pub fn machine(&self) -> &ThreadedProtocolMachine {
        &self.machine
    }

    /// Open a choreography and immediately bind host-runtime ownership.
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

    /// Execute one scheduler round in the guest runtime.
    ///
    /// # Errors
    ///
    /// Returns a `ProtocolMachineError` if a coroutine faults.
    pub fn step_round(
        &mut self,
        handler: &dyn EffectHandler,
        n: usize,
    ) -> Result<StepResult, ProtocolMachineError> {
        self.machine.step_round(handler, n)
    }

    /// Run up to `max_rounds`.
    ///
    /// # Errors
    ///
    /// Returns a `ProtocolMachineError` if a coroutine faults.
    pub fn run(
        &mut self,
        handler: &dyn EffectHandler,
        max_rounds: usize,
    ) -> Result<RunStatus, ProtocolMachineError> {
        self.machine.run(handler, max_rounds)
    }

    /// Borrow the observable trace.
    #[must_use]
    pub fn trace(&self) -> &[ObsEvent] {
        self.machine.trace()
    }
}
