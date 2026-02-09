//! Session lifecycle instruction execution.

use crate::coroutine::Fault;
use crate::instr::Endpoint;
use crate::session::SessionId;
use crate::vm::{StepPack, VM};

pub(crate) fn step_close(vm: &mut VM, ep: &Endpoint, sid: SessionId) -> Result<StepPack, Fault> {
    vm.step_close(ep, sid)
}

pub(crate) fn step_open(
    vm: &mut VM,
    coro_idx: usize,
    role: &str,
    roles: &[String],
    endpoints: &[(String, u16)],
) -> Result<StepPack, Fault> {
    vm.step_open(coro_idx, role, roles, endpoints)
}
