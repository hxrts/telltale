//! Session lifecycle instruction execution.

use crate::coroutine::Fault;
use crate::vm::{StepPack, VM};

pub(crate) fn step_close(vm: &mut VM, coro_idx: usize, session: u16) -> Result<StepPack, Fault> {
    vm.step_close(coro_idx, session)
}

pub(crate) fn step_open(
    vm: &mut VM,
    coro_idx: usize,
    role: &str,
    roles: &[String],
    local_types: &[(String, telltale_types::LocalTypeR)],
    handlers: &[((String, String), String)],
    dsts: &[(String, u16)],
) -> Result<StepPack, Fault> {
    vm.step_open(coro_idx, role, roles, local_types, handlers, dsts)
}
