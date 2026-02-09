//! Speculation instruction execution.

use crate::coroutine::Fault;
use crate::session::SessionId;
use crate::vm::{StepPack, VM};

pub(crate) fn step_fork(
    vm: &mut VM,
    coro_idx: usize,
    role: &str,
    sid: SessionId,
    ghost: u16,
) -> Result<StepPack, Fault> {
    vm.step_fork(coro_idx, role, sid, ghost)
}

pub(crate) fn step_join(
    vm: &mut VM,
    coro_idx: usize,
    role: &str,
    sid: SessionId,
) -> Result<StepPack, Fault> {
    vm.step_join(coro_idx, role, sid)
}

pub(crate) fn step_abort(
    vm: &mut VM,
    coro_idx: usize,
    role: &str,
    sid: SessionId,
) -> Result<StepPack, Fault> {
    vm.step_abort(coro_idx, role, sid)
}
