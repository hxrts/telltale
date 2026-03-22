//! Native threaded guest-runtime driver.

use crate::effect::EffectHandler;
use crate::loader::CodeImage;
use crate::owned::OwnedSession;
use crate::threaded::ThreadedVM;
use crate::vm::{ObsEvent, RunStatus, StepResult, VMConfig, VMError};

/// Native threaded guest runtime backed by the threaded protocol machine.
#[doc(alias = "ThreadedGuestRuntime")]
pub struct NativeThreadedDriver {
    vm: ThreadedVM,
}

impl NativeThreadedDriver {
    /// Create a threaded guest runtime with explicit worker count.
    #[must_use]
    pub fn with_workers(config: VMConfig, workers: usize) -> Self {
        Self {
            vm: ThreadedVM::with_workers(config, workers),
        }
    }

    /// Create a threaded guest runtime with auto worker count.
    #[must_use]
    pub fn auto(config: VMConfig) -> Self {
        Self {
            vm: ThreadedVM::auto(config),
        }
    }

    /// Wrap an existing threaded protocol-machine instance.
    #[must_use]
    pub fn with_vm(vm: ThreadedVM) -> Self {
        Self { vm }
    }

    /// Access the inner threaded protocol machine.
    #[must_use]
    pub fn vm(&self) -> &ThreadedVM {
        &self.vm
    }

    /// Open a choreography and immediately bind host-runtime ownership.
    ///
    /// # Errors
    ///
    /// Returns a `VMError` if the choreography cannot be loaded or claimed.
    pub fn load_choreography_owned(
        &mut self,
        image: &CodeImage,
        owner_id: impl Into<String>,
    ) -> Result<OwnedSession, VMError> {
        self.vm.load_choreography_owned(image, owner_id)
    }

    /// Execute one scheduler round in the guest runtime.
    ///
    /// # Errors
    ///
    /// Returns a `VMError` if a coroutine faults.
    pub fn step_round(
        &mut self,
        handler: &dyn EffectHandler,
        n: usize,
    ) -> Result<StepResult, VMError> {
        self.vm.step_round(handler, n)
    }

    /// Run up to `max_rounds`.
    ///
    /// # Errors
    ///
    /// Returns a `VMError` if a coroutine faults.
    pub fn run(
        &mut self,
        handler: &dyn EffectHandler,
        max_rounds: usize,
    ) -> Result<RunStatus, VMError> {
        self.vm.run(handler, max_rounds)
    }

    /// Borrow the observable trace.
    #[must_use]
    pub fn trace(&self) -> &[ObsEvent] {
        self.vm.trace()
    }
}
