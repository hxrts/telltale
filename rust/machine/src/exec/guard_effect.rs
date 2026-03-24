//! Guard/effect instruction execution.

use crate::coroutine::Fault;
use crate::effect::EffectHandler;
use crate::engine::{GuardAcquireInput, GuardReleaseInput, ProtocolMachine, StepPack};
use crate::instr::Endpoint;
use crate::instr::InvokeAction;
use crate::session::SessionId;

pub(crate) fn step_invoke(
    vm: &mut ProtocolMachine,
    coro_idx: usize,
    role: &str,
    action: InvokeAction,
    handler: &dyn EffectHandler,
) -> Result<StepPack, Fault> {
    vm.step_invoke(coro_idx, role, action, handler)
}

pub(crate) fn step_acquire(
    vm: &mut ProtocolMachine,
    coro_idx: usize,
    ep: &Endpoint,
    role: &str,
    sid: SessionId,
    layer: &str,
    dst: u16,
    handler: &dyn EffectHandler,
) -> Result<StepPack, Fault> {
    vm.step_acquire(
        GuardAcquireInput {
            coro_idx,
            endpoint: ep,
            role,
            sid,
            layer,
            dst,
        },
        handler,
    )
}

pub(crate) fn step_release(
    vm: &mut ProtocolMachine,
    coro_idx: usize,
    ep: &Endpoint,
    role: &str,
    sid: SessionId,
    layer: &str,
    evidence: u16,
    handler: &dyn EffectHandler,
) -> Result<StepPack, Fault> {
    vm.step_release(
        GuardReleaseInput {
            coro_idx,
            endpoint: ep,
            role,
            sid,
            layer,
            evidence,
        },
        handler,
    )
}
