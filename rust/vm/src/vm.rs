//! The VM: ties coroutines, sessions, and scheduler together.
//!
//! Execution follows the Lean spec pattern:
//! - `exec_instr` fetches, dispatches to per-instruction step functions
//! - Each step function owns its type checking via `SessionStore::lookup_type`
//! - Results are bundled in `StepPack` and committed atomically via `commit_pack`
//! - Blocking never advances type state
//!
//! This module is a runtime surface over the canonical `VMKernel` execution
//! contract. Driver layers call into `VMKernel` and do not redefine instruction
//! semantics.

use serde::{Deserialize, Deserializer, Serialize, Serializer};
use serde_json::json;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::marker::PhantomData;
use std::sync::Arc;
use std::time::Duration;
use telltale_types::{LocalTypeR, ValType};

use crate::bridge::{IdentityGuardBridge, IdentityVerificationBridge};
use crate::buffer::{BufferConfig, EnqueueResult};
use crate::clock::SimClock;
use crate::commit_common::{apply_output_condition_gate, effect_trace_entry_for_event};
use crate::coroutine::{
    BlockReason, CoroStatus, Coroutine, Fault, KnowledgeFact, ProgressToken, Value,
};
use crate::determinism::{DeterminismMode, EffectDeterminismTier};
use crate::effect::{
    CorruptionType, EffectHandler, EffectTraceEntry, ReplayEffectHandler, SendDecision,
    SendDecisionFastPathInput, SendDecisionInput, TopologyPerturbation,
};
use crate::exec;
use crate::faults::{
    speculation_fault_abort_requires_active, speculation_fault_disabled,
    speculation_fault_join_requires_active, transfer_fault_delegation_guard_violation,
};
use crate::guard::{GuardLayer, InMemoryGuardLayer, LayerId};
use crate::identity::IdentityModel;
use crate::instr::{Endpoint, Instr, InvokeAction, PC};
use crate::instruction_semantics::{
    decode_endpoint_fact, endpoint_from_reg as decode_endpoint_from_reg,
};
use crate::intern::{StringId, SymbolTable};
use crate::kernel::{KernelMachine, VMKernel};
use crate::loader::CodeImage;
use crate::output_condition::{OutputConditionCheck, OutputConditionPolicy};
use crate::persistence::{NoopPersistence, PersistenceModel};
use crate::scheduler::{SchedPolicy, Scheduler};
use crate::serialization::{canonical_replay_fragment_v1, CanonicalReplayFragmentV1};
use crate::session::{unfold_if_var_with_scope, Edge, SessionId, SessionStatus, SessionStore};
use crate::transfer_semantics::{
    decode_transfer_request, endpoint_owner_ids, move_endpoint_bundle,
};
use crate::verification::{DefaultVerificationModel, VerificationModel};


include!("vm/prelude1.rs");
include!("vm/prelude2.rs");
include!("vm/prelude3.rs");
include!("vm/impl_part1.rs");
include!("vm/impl_part2.rs");
include!("vm/impl_part3.rs");
include!("vm/impl_part4.rs");
include!("vm/impl_part5.rs");
include!("vm/impl_part6.rs");
include!("vm/kernel_impl.rs");

#[cfg(test)]
mod tests {
    include!("vm/tests_support1.rs");
    include!("vm/tests_support2.rs");
    include!("vm/tests_part1.rs");
    include!("vm/tests_part2.rs");
    include!("vm/tests_part3.rs");
    include!("vm/tests_part4.rs");
}
