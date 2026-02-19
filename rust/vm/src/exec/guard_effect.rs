//! Guard/effect instruction execution.

use crate::coroutine::Fault;
use crate::effect::EffectHandler;
use crate::instr::Endpoint;
use crate::instr::InvokeAction;
use crate::session::SessionId;
use crate::vm::{StepPack, VM};

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

#[allow(clippy::too_many_arguments)]
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
    vm.step_acquire(coro_idx, ep, role, sid, layer, dst, handler)
}

#[allow(clippy::too_many_arguments)]
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
    vm.step_release(coro_idx, ep, role, sid, layer, evidence, handler)
}
