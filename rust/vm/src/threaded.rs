//! Threaded VM backend (feature-gated, adapter runtime).
//!
//! Executes one coroutine per session per round in parallel, preserving
//! per-session trace equivalence with the cooperative VM.
//!
//! Semantic ownership remains in the canonical `VMKernel` contract.

use rayon::prelude::*;
use rayon::{ThreadPool, ThreadPoolBuilder};
use serde::{Deserialize, Serialize};
use serde_json::json;
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, RwLock, TryLockError};
use std::time::Duration;

use telltale_types::{LocalTypeR, ValType};

use crate::buffer::{BufferConfig, EnqueueResult};
use crate::clock::SimClock;
use crate::commit_common::{apply_output_condition_gate, effect_trace_entry_for_event};
use crate::communication_replay::{
    CommunicationConsumption, CommunicationConsumptionArtifact, CommunicationReplayError,
    CommunicationStepKind, DefaultCommunicationConsumption,
};
use crate::coroutine::{BlockReason, CoroStatus, Coroutine, Fault, ProgressToken, Value};
use crate::effect::{
    CorruptionType, EffectHandler, EffectTraceEntry, ReplayEffectHandler, SendDecision,
    SendDecisionFastPathInput, SendDecisionInput, TopologyPerturbation,
};
use crate::faults::{
    speculation_fault_abort_requires_active, speculation_fault_disabled,
    speculation_fault_join_requires_active, transfer_fault_delegation_guard_violation,
};
use crate::instr::{Endpoint, Instr, InvokeAction, PC};
use crate::instruction_semantics::{
    decode_branch_label_payload, decode_endpoint_fact, endpoint_from_reg,
};
use crate::intern::{EdgeId, EdgeSymbolTable, StringId, SymbolTable};
use crate::kernel::{KernelMachine, VMKernel};
use crate::loader::CodeImage;
use crate::output_condition::{OutputConditionCheck, OutputConditionHint};
use crate::scheduler::Scheduler;
use crate::serialization::{canonical_replay_fragment_v1, CanonicalReplayFragmentV1};
use crate::session::{
    unfold_if_var_with_scope, Edge, SessionId, SessionOpenPlan, SessionState, SessionStatus,
};
use crate::transfer_semantics::{decode_transfer_request, move_endpoint_bundle};
use crate::vm::{
    runtime_value_matches_val_type, runtime_value_val_type, runtime_value_wire_size_bytes,
    EffectTraceCaptureMode, MonitorMode, ObsEvent, ProgramStore, ResourceState, RunStatus, SiteId,
    StepResult, ThreadedRoundSemantics, VMConfig, VMError,
};

// Lane identifier in the threaded runtime.

include!("threaded/prelude.rs");
include!("threaded/runtime_and_scheduling.rs");
include!("threaded/runtime_introspection.rs");
include!("threaded/topology_and_planner.rs");
include!("threaded/commit_and_handoff.rs");
include!("threaded/exec_and_validation.rs");
include!("threaded/instructions_send_recv_control.rs");
include!("threaded/instructions_guard_and_speculation.rs");
include!("threaded/instructions_choice_and_session.rs");

#[cfg(test)]
mod tests {
    include!("../tests/unit/threaded_runtime_tests.rs");
}
