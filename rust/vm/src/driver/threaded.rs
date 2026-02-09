//! Native threaded runtime driver.

use crate::effect::EffectHandler;
use crate::loader::CodeImage;
use crate::session::SessionId;
use crate::threaded::ThreadedVM;
use crate::vm::{ObsEvent, StepResult, VMConfig, VMError};

/// Native threaded runtime driver.
pub struct NativeThreadedDriver {
    vm: ThreadedVM,
}

impl NativeThreadedDriver {
    /// Create a threaded driver with explicit worker count.
    #[must_use]
    pub fn with_workers(config: VMConfig, workers: usize) -> Self {
        Self {
            vm: ThreadedVM::with_workers(config, workers),
        }
    }

    /// Create a threaded driver with auto worker count.
    #[must_use]
    pub fn auto(config: VMConfig) -> Self {
        Self {
            vm: ThreadedVM::auto(config),
        }
    }

    /// Wrap an existing threaded VM.
    #[must_use]
    pub fn with_vm(vm: ThreadedVM) -> Self {
        Self { vm }
    }

    /// Access the inner threaded VM.
    #[must_use]
    pub fn vm(&self) -> &ThreadedVM {
        &self.vm
    }

    /// Load a choreography image.
    ///
    /// # Errors
    ///
    /// Returns a `VMError` if limits are exceeded.
    pub fn load_choreography(&mut self, image: &CodeImage) -> Result<SessionId, VMError> {
        self.vm.load_choreography(image)
    }

    /// Execute one scheduler round.
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
    pub fn run(&mut self, handler: &dyn EffectHandler, max_rounds: usize) -> Result<(), VMError> {
        self.vm.run(handler, max_rounds)
    }

    /// Borrow the observable trace.
    #[must_use]
    pub fn trace(&self) -> &[ObsEvent] {
        self.vm.trace()
    }
}
