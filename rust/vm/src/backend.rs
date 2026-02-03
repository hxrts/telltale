//! Backend abstraction for VM execution engines.
//!
//! Allows swapping cooperative and threaded backends behind a common API.

use crate::effect::EffectHandler;
use crate::loader::CodeImage;
use crate::session::SessionId;
use crate::vm::{ObsEvent, StepResult, VMError, VM};

/// Common VM backend interface.
pub trait VMBackend {
    /// Load a choreography into the backend, returning the session ID.
    ///
    /// # Errors
    ///
    /// Returns a `VMError` if limits are exceeded or the image is invalid.
    fn load_choreography(&mut self, image: &CodeImage) -> Result<SessionId, VMError>;

    /// Execute one scheduler round: advance up to `n` ready coroutines.
    ///
    /// # Errors
    ///
    /// Returns a `VMError` if any coroutine faults.
    fn step_round(&mut self, handler: &dyn EffectHandler, n: usize) -> Result<StepResult, VMError>;

    /// Run until completion or `max_rounds` is reached.
    ///
    /// # Errors
    ///
    /// Returns a `VMError` if any coroutine faults.
    fn run(&mut self, handler: &dyn EffectHandler, max_rounds: usize) -> Result<(), VMError>;

    /// Get the observable trace (cloned).
    #[must_use]
    fn trace(&self) -> Vec<ObsEvent>;
}

impl VMBackend for VM {
    fn load_choreography(&mut self, image: &CodeImage) -> Result<SessionId, VMError> {
        self.load_choreography(image)
    }

    fn step_round(&mut self, handler: &dyn EffectHandler, n: usize) -> Result<StepResult, VMError> {
        self.step_round(handler, n)
    }

    fn run(&mut self, handler: &dyn EffectHandler, max_rounds: usize) -> Result<(), VMError> {
        self.run_concurrent(handler, max_rounds, 1)
    }

    fn trace(&self) -> Vec<ObsEvent> {
        self.trace().to_vec()
    }
}

#[cfg(feature = "multi-thread")]
use crate::threaded::ThreadedVM;

#[cfg(feature = "multi-thread")]
impl VMBackend for ThreadedVM {
    fn load_choreography(&mut self, image: &CodeImage) -> Result<SessionId, VMError> {
        self.load_choreography(image)
    }

    fn step_round(&mut self, handler: &dyn EffectHandler, n: usize) -> Result<StepResult, VMError> {
        self.step_round(handler, n)
    }

    fn run(&mut self, handler: &dyn EffectHandler, max_rounds: usize) -> Result<(), VMError> {
        self.run(handler, max_rounds)
    }

    fn trace(&self) -> Vec<ObsEvent> {
        self.trace().to_vec()
    }
}
