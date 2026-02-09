//! Native single-thread runtime driver.

use crate::effect::EffectHandler;
use crate::kernel::VMKernel;
use crate::loader::CodeImage;
use crate::session::SessionId;
use crate::vm::{ObsEvent, StepResult, VMConfig, VMError, VM};

/// Native cooperative runtime driver backed by the canonical VM kernel.
#[derive(Debug)]
pub struct NativeSingleThreadDriver {
    vm: VM,
}

impl NativeSingleThreadDriver {
    /// Create a new driver from VM config.
    #[must_use]
    pub fn new(config: VMConfig) -> Self {
        Self {
            vm: VM::new(config),
        }
    }

    /// Wrap an existing VM instance.
    #[must_use]
    pub fn with_vm(vm: VM) -> Self {
        Self { vm }
    }

    /// Access the inner VM.
    #[must_use]
    pub fn vm(&self) -> &VM {
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

    /// Execute one scheduler round via the kernel.
    ///
    /// # Errors
    ///
    /// Returns a `VMError` if a coroutine faults.
    pub fn step_round(
        &mut self,
        handler: &dyn EffectHandler,
        n: usize,
    ) -> Result<StepResult, VMError> {
        VMKernel::step_round(&mut self.vm, handler, n)
    }

    /// Run up to `max_rounds` with concurrency `n` via the kernel.
    ///
    /// # Errors
    ///
    /// Returns a `VMError` if a coroutine faults.
    pub fn run(
        &mut self,
        handler: &dyn EffectHandler,
        max_rounds: usize,
        n: usize,
    ) -> Result<(), VMError> {
        VMKernel::run_concurrent(&mut self.vm, handler, max_rounds, n)
    }

    /// Borrow the observable trace.
    #[must_use]
    pub fn trace(&self) -> &[ObsEvent] {
        self.vm.trace()
    }
}
