//! Speculation instruction execution.

use crate::coroutine::Fault;
use crate::engine::{ProtocolMachine, StepPack};
use crate::session::SessionId;

pub(crate) fn step_fork(
    machine: &mut ProtocolMachine,
    coro_idx: usize,
    role: &str,
    sid: SessionId,
    ghost: u16,
) -> Result<StepPack, Fault> {
    machine.step_fork(coro_idx, role, sid, ghost)
}

pub(crate) fn step_join(
    machine: &mut ProtocolMachine,
    coro_idx: usize,
    role: &str,
    sid: SessionId,
) -> Result<StepPack, Fault> {
    machine.step_join(coro_idx, role, sid)
}

pub(crate) fn step_abort(
    machine: &mut ProtocolMachine,
    coro_idx: usize,
    role: &str,
    sid: SessionId,
) -> Result<StepPack, Fault> {
    machine.step_abort(coro_idx, role, sid)
}
