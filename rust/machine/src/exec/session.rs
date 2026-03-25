//! Session lifecycle instruction execution.

use crate::coroutine::Fault;
use crate::engine::{ProtocolMachine, StepPack};

pub(crate) fn step_close(
    machine: &mut ProtocolMachine,
    coro_idx: usize,
    session: u16,
) -> Result<StepPack, Fault> {
    machine.step_close(coro_idx, session)
}

pub(crate) fn step_open(
    machine: &mut ProtocolMachine,
    coro_idx: usize,
    role: &str,
    roles: &[String],
    local_types: &[(String, telltale_types::LocalTypeR)],
    handlers: &[((String, String), String)],
    dsts: &[(String, u16)],
) -> Result<StepPack, Fault> {
    machine.step_open(coro_idx, role, roles, local_types, handlers, dsts)
}
