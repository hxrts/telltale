//! Ownership/knowledge instruction execution.

use crate::coroutine::Fault;
use crate::session::SessionId;
use crate::vm::{StepPack, VM};

#[allow(clippy::too_many_arguments)]
pub(crate) fn step_transfer(
    vm: &mut VM,
    coro_idx: usize,
    role: &str,
    sid: SessionId,
    endpoint: u16,
    target: u16,
    bundle: u16,
) -> Result<StepPack, Fault> {
    vm.step_transfer(coro_idx, role, sid, endpoint, target, bundle)
}

pub(crate) fn step_tag(
    vm: &mut VM,
    coro_idx: usize,
    role: &str,
    sid: SessionId,
    fact: u16,
    dst: u16,
) -> Result<StepPack, Fault> {
    vm.step_tag(coro_idx, role, sid, fact, dst)
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn step_check(
    vm: &mut VM,
    coro_idx: usize,
    role: &str,
    sid: SessionId,
    knowledge: u16,
    target: u16,
    dst: u16,
) -> Result<StepPack, Fault> {
    vm.step_check(coro_idx, role, sid, knowledge, target, dst)
}
