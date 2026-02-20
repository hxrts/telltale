//! Guard/effect instruction execution.

use crate::coroutine::Fault;
use crate::effect::EffectHandler;
use crate::instr::Endpoint;
use crate::instr::InvokeAction;
use crate::session::SessionId;
use crate::vm::{GuardAcquireInput, GuardReleaseInput, StepPack, VM};

pub(crate) fn step_invoke(
    vm: &mut VM,
    coro_idx: usize,
    role: &str,
    action: InvokeAction,
    dst: Option<u16>,
    handler: &dyn EffectHandler,
) -> Result<StepPack, Fault> {
    vm.step_invoke(coro_idx, role, action, dst, handler)
}

pub(crate) fn step_acquire(
    vm: &mut VM,
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
    vm: &mut VM,
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
