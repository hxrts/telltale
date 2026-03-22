//! Native single-thread guest-runtime driver.

use crate::effect::EffectHandler;
use crate::kernel::VMKernel;
use crate::loader::CodeImage;
use crate::owned::OwnedSession;
use crate::vm::{ObsEvent, RunStatus, StepResult, VMConfig, VMError, VM};

/// Native cooperative guest runtime backed by the canonical protocol machine.
#[doc(alias = "GuestRuntime")]
#[derive(Debug)]
pub struct NativeSingleThreadDriver {
    vm: VM,
}

impl NativeSingleThreadDriver {
    /// Create a new guest runtime from protocol-machine config.
    #[must_use]
    pub fn new(config: VMConfig) -> Self {
        Self {
            vm: VM::new(config),
        }
    }

    /// Wrap an existing protocol-machine instance inside this guest runtime.
    #[must_use]
    pub fn with_vm(vm: VM) -> Self {
        Self { vm }
    }

    /// Access the inner protocol machine.
    #[must_use]
    pub fn vm(&self) -> &VM {
        &self.vm
    }

    /// Preferred choreography open path that returns an ownership-bearing handle.
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

    /// Execute one scheduler round via the protocol-machine kernel.
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

    /// Run up to `max_rounds` with concurrency `n` via the protocol-machine kernel.
    ///
    /// # Errors
    ///
    /// Returns a `VMError` if a coroutine faults.
    pub fn run(
        &mut self,
        handler: &dyn EffectHandler,
        max_rounds: usize,
        n: usize,
    ) -> Result<RunStatus, VMError> {
        VMKernel::run_concurrent(&mut self.vm, handler, max_rounds, n)
    }

    /// Borrow the observable trace.
    #[must_use]
    pub fn trace(&self) -> &[ObsEvent] {
        self.vm.trace()
    }
}
