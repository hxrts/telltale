//! Instruction dispatcher split by semantic concern.

use crate::coroutine::Fault;
use crate::effect::EffectHandler;
use crate::engine::{ProtocolMachine, StepPack};
use crate::instr::{Endpoint, Instr};
use crate::session::SessionId;

pub(crate) mod comm;
pub(crate) mod control;
pub(crate) mod guard_effect;
pub(crate) mod helpers;
pub(crate) mod ownership;
pub(crate) mod session;
pub(crate) mod speculation;

/// Dispatch one instruction to its semantic execution module.
pub(crate) fn step_instr(
    machine: &mut ProtocolMachine,
    coro_idx: usize,
    ep: &Endpoint,
    role: &str,
    sid: SessionId,
    instr: Instr,
    handler: &dyn EffectHandler,
) -> Result<StepPack, Fault> {
    match instr {
        Instr::Send { chan, val } => comm::step_send(machine, coro_idx, role, chan, val, handler),
        Instr::Receive { chan, dst } => comm::step_receive(machine, coro_idx, role, chan, dst, handler),
        Instr::Offer { chan, label } => comm::step_offer(machine, coro_idx, role, chan, &label, handler),
        Instr::Choose { chan, table } => {
            comm::step_choose(machine, coro_idx, role, chan, &table, handler)
        }
        Instr::Open {
            roles,
            local_types,
            handlers,
            dsts,
        } => session::step_open(machine, coro_idx, role, &roles, &local_types, &handlers, &dsts),
        Instr::Close { session } => session::step_close(machine, coro_idx, session),
        Instr::Invoke { action } => guard_effect::step_invoke(machine, coro_idx, role, action, handler),
        Instr::Acquire { layer, dst } => {
            guard_effect::step_acquire(machine, coro_idx, ep, role, sid, &layer, dst, handler)
        }
        Instr::Release { layer, evidence } => {
            guard_effect::step_release(machine, coro_idx, ep, role, sid, &layer, evidence, handler)
        }
        Instr::Fork { ghost } => speculation::step_fork(machine, coro_idx, role, sid, ghost),
        Instr::Join => speculation::step_join(machine, coro_idx, role, sid),
        Instr::Abort => speculation::step_abort(machine, coro_idx, role, sid),
        Instr::Transfer {
            endpoint,
            target,
            bundle,
        } => ownership::step_transfer(machine, coro_idx, role, sid, endpoint, target, bundle),
        Instr::Tag { fact, dst } => ownership::step_tag(machine, coro_idx, role, sid, fact, dst),
        Instr::Check {
            knowledge,
            target,
            dst,
        } => ownership::step_check(machine, coro_idx, role, sid, knowledge, target, dst),
        Instr::Set { dst, val } => Ok(control::step_set(dst, val)),
        Instr::Move { dst, src } => control::step_move(machine, coro_idx, dst, src),
        Instr::Jump { target } => Ok(control::step_jump(target)),
        Instr::Spawn { target, args } => control::step_spawn(machine, coro_idx, target, &args),
        Instr::Yield => Ok(control::step_yield()),
        Instr::Halt => control::step_halt(machine, ep),
    }
}
