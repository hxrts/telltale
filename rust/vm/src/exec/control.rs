//! Control-flow instruction execution.

use crate::coroutine::BlockReason;
use crate::coroutine::{Fault, Value};
use crate::exec::helpers::{empty_pack, write_reg_pack};
use crate::instr::{Endpoint, ImmValue, PC};
use crate::vm::{CoroUpdate, StepPack, VM};

/// Execute `set`.
#[must_use]
pub(crate) fn step_set(dst: u16, val: ImmValue) -> StepPack {
    let value = match val {
        ImmValue::Unit => Value::Unit,
        ImmValue::Nat(n) => Value::Nat(n),
        ImmValue::Bool(b) => Value::Bool(b),
        ImmValue::Str(s) => Value::Str(s),
    };
    write_reg_pack(dst, value)
}

/// Execute `move`.
#[must_use]
pub(crate) fn step_move(vm: &VM, coro_idx: usize, dst: u16, src: u16) -> StepPack {
    let value = vm.read_reg(coro_idx, src);
    write_reg_pack(dst, value)
}

/// Execute `jump`.
#[must_use]
pub(crate) fn step_jump(target: PC) -> StepPack {
    empty_pack(CoroUpdate::SetPc(target))
}

/// Execute `yield`.
#[must_use]
pub(crate) fn step_yield() -> StepPack {
    empty_pack(CoroUpdate::AdvancePcBlock(BlockReason::Spawn))
}

/// Execute `halt`.
pub(crate) fn step_halt(vm: &VM, ep: &Endpoint) -> Result<StepPack, Fault> {
    vm.step_halt(ep)
}

/// Execute `spawn`.
pub(crate) fn step_spawn(
    vm: &mut VM,
    coro_idx: usize,
    target: PC,
    args: &[u16],
) -> Result<StepPack, Fault> {
    vm.step_spawn(coro_idx, target, args)
}
