//! Instruction dispatcher split by semantic concern.

use crate::coroutine::Fault;
use crate::effect::EffectHandler;
use crate::instr::{Endpoint, Instr};
use crate::session::SessionId;
use crate::vm::{StepPack, VM};

pub(crate) mod comm;
pub(crate) mod control;
pub(crate) mod guard_effect;
pub(crate) mod helpers;
pub(crate) mod ownership;
pub(crate) mod session;
pub(crate) mod speculation;

/// Dispatch one instruction to its semantic execution module.
pub(crate) fn step_instr(
    vm: &mut VM,
    coro_idx: usize,
    ep: &Endpoint,
    role: &str,
    sid: SessionId,
    instr: Instr,
    handler: &dyn EffectHandler,
) -> Result<StepPack, Fault> {
    match instr {
        Instr::Send { val, .. } => comm::step_send(vm, coro_idx, ep, role, sid, val, handler),
        Instr::Receive { dst, .. } => comm::step_receive(vm, coro_idx, ep, role, sid, dst, handler),
        Instr::Offer { label, .. } => {
            comm::step_offer(vm, coro_idx, ep, role, sid, &label, handler)
        }
        Instr::Choose { table, .. } => {
            comm::step_choose(vm, coro_idx, ep, role, sid, &table, handler)
        }
        Instr::Open { roles, endpoints } => {
            session::step_open(vm, coro_idx, role, &roles, &endpoints)
        }
        Instr::Close { .. } => session::step_close(vm, ep, sid),
        Instr::Invoke { .. } => guard_effect::step_invoke(vm, coro_idx, role, handler),
        Instr::Acquire { layer, dst } => {
            guard_effect::step_acquire(vm, coro_idx, ep, role, sid, &layer, dst, handler)
        }
        Instr::Release { layer, evidence } => {
            guard_effect::step_release(vm, coro_idx, ep, role, sid, &layer, evidence, handler)
        }
        Instr::Fork { ghost } => speculation::step_fork(vm, coro_idx, role, sid, ghost),
        Instr::Join => speculation::step_join(vm, coro_idx, role, sid),
        Instr::Abort => speculation::step_abort(vm, coro_idx, role, sid),
        Instr::Transfer {
            endpoint,
            target,
            bundle,
        } => ownership::step_transfer(vm, coro_idx, role, sid, endpoint, target, bundle),
        Instr::Tag { fact, dst } => ownership::step_tag(vm, coro_idx, role, sid, fact, dst),
        Instr::Check {
            knowledge,
            target,
            dst,
        } => ownership::step_check(vm, coro_idx, role, sid, knowledge, target, dst),
        Instr::Set { dst, val } => Ok(control::step_set(dst, val)),
        Instr::Move { dst, src } => Ok(control::step_move(vm, coro_idx, dst, src)),
        Instr::Jump { target } => Ok(control::step_jump(target)),
        Instr::Spawn { .. } => control::step_spawn(),
        Instr::Yield => Ok(control::step_yield()),
        Instr::Halt => control::step_halt(vm, ep),
    }
}
