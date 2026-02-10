//! Communication instruction execution.

use crate::coroutine::Fault;
use crate::effect::EffectHandler;
use crate::vm::{StepPack, VM};

pub(crate) fn step_send(
    vm: &mut VM,
    coro_idx: usize,
    role: &str,
    chan: u16,
    val_reg: u16,
    handler: &dyn EffectHandler,
) -> Result<StepPack, Fault> {
    vm.step_send(coro_idx, role, chan, val_reg, handler)
}

pub(crate) fn step_receive(
    vm: &mut VM,
    coro_idx: usize,
    role: &str,
    chan: u16,
    dst: u16,
    handler: &dyn EffectHandler,
) -> Result<StepPack, Fault> {
    vm.step_recv(coro_idx, role, chan, dst, handler)
}

pub(crate) fn step_offer(
    vm: &mut VM,
    coro_idx: usize,
    role: &str,
    chan: u16,
    label: &str,
    handler: &dyn EffectHandler,
) -> Result<StepPack, Fault> {
    vm.step_offer(coro_idx, role, chan, label, handler)
}

pub(crate) fn step_choose(
    vm: &mut VM,
    coro_idx: usize,
    role: &str,
    chan: u16,
    table: &[(String, usize)],
    handler: &dyn EffectHandler,
) -> Result<StepPack, Fault> {
    vm.step_choose(coro_idx, role, chan, table, handler)
}
