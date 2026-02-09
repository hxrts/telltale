//! Communication instruction execution.

use crate::coroutine::Fault;
use crate::effect::EffectHandler;
use crate::instr::Endpoint;
use crate::session::SessionId;
use crate::vm::{StepPack, VM};

pub(crate) fn step_send(
    vm: &mut VM,
    coro_idx: usize,
    ep: &Endpoint,
    role: &str,
    sid: SessionId,
    val_reg: u16,
    handler: &dyn EffectHandler,
) -> Result<StepPack, Fault> {
    vm.step_send(coro_idx, ep, role, sid, val_reg, handler)
}

pub(crate) fn step_receive(
    vm: &mut VM,
    coro_idx: usize,
    ep: &Endpoint,
    role: &str,
    sid: SessionId,
    dst: u16,
    handler: &dyn EffectHandler,
) -> Result<StepPack, Fault> {
    vm.step_recv(coro_idx, ep, role, sid, dst, handler)
}

pub(crate) fn step_offer(
    vm: &mut VM,
    coro_idx: usize,
    ep: &Endpoint,
    role: &str,
    sid: SessionId,
    label: &str,
    handler: &dyn EffectHandler,
) -> Result<StepPack, Fault> {
    vm.step_offer(coro_idx, ep, role, sid, label, handler)
}

pub(crate) fn step_choose(
    vm: &mut VM,
    coro_idx: usize,
    ep: &Endpoint,
    role: &str,
    sid: SessionId,
    table: &[(String, usize)],
    handler: &dyn EffectHandler,
) -> Result<StepPack, Fault> {
    vm.step_choose(coro_idx, ep, role, sid, table, handler)
}
