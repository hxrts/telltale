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


include!("vm/runtime_value_and_resource_state.rs");
include!("vm/vm_config_and_observability.rs");
include!("vm/vm_error_and_step_pack.rs");
include!("vm/runtime_and_execution.rs");
include!("vm/introspection_and_validation.rs");
include!("vm/topology_and_dispatch.rs");
include!("vm/instruction_control_and_effects.rs");
include!("vm/instruction_choice_and_session.rs");
include!("vm/open_commit_and_interning.rs");
include!("vm/kernel_impl.rs");

#[cfg(test)]
mod tests {
    include!("../tests/unit/vm/tests_effect_handlers_core.rs");
    include!("../tests/unit/vm/tests_effect_handlers_edge_cases.rs");
    include!("../tests/unit/vm/tests_runtime_progress.rs");
    include!("../tests/unit/vm/tests_monitor_and_persistence.rs");
    include!("../tests/unit/vm/tests_compiler_and_topology.rs");
    include!("../tests/unit/vm/tests_flow_policy_and_faults.rs");
}
