//! Generic execution-result API aligned with the Lean VM execution model.

use crate::vm::ObsEvent;

/// Execution status after one step/round.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExecStatus<G = ()> {
    /// Coroutine continues execution.
    Continue,
    /// Coroutine blocked on a guard/policy reason.
    Blocked(G),
    /// Coroutine/session halted.
    Halted,
    /// Runtime detected a fault.
    Faulted,
}

/// One execution event emitted by a step.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StepEvent<E = ()> {
    /// Observable VM event.
    Obs(ObsEvent),
    /// Internal effect/policy event payload.
    Internal(E),
}

/// Structured result of one execution step.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExecResult<G = (), E = ()> {
    /// Status after applying one step.
    pub status: ExecStatus<G>,
    /// Optional emitted event.
    pub event: Option<StepEvent<E>>,
}

/// Generic execution pack carrying updated coroutine state plus step result.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StepPack<G = (), E = ()> {
    /// Coroutine identifier after the step.
    pub coro_id: usize,
    /// Step result.
    pub res: ExecResult<G, E>,
}
