//! Shared helpers for instruction-step pack construction.

use crate::coroutine::Value;
use crate::vm::{CoroUpdate, StepPack};

/// Build an empty step pack for control-flow style updates.
#[must_use]
pub(crate) fn empty_pack(coro_update: CoroUpdate) -> StepPack {
    StepPack {
        coro_update,
        type_update: None,
        events: Vec::new(),
    }
}

/// Build a register-write step pack.
#[must_use]
pub(crate) fn write_reg_pack(reg: u16, val: Value) -> StepPack {
    StepPack {
        coro_update: CoroUpdate::AdvancePcWriteReg { reg, val },
        type_update: None,
        events: Vec::new(),
    }
}
