//! Threaded ProtocolMachine backend (feature-gated, adapter runtime).
//!
//! Executes one coroutine per session per round in parallel, preserving
//! per-session trace equivalence with the cooperative ProtocolMachine.
//!
//! Semantic ownership remains in the canonical `ProtocolMachineKernel` contract.

use rayon::prelude::*;
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
    infer_effect_interface_and_operation, CorruptionType, EffectExchangeRecord, EffectFailure,
    EffectHandler, EffectOutcome, EffectRequest, EffectResult, EffectTraceEntry,
    ReplayEffectHandler, SendDecision, TopologyPerturbation,
};
use crate::engine::{
    runtime_value_matches_val_type, runtime_value_val_type, runtime_value_wire_size_bytes,
    EffectTraceCaptureMode, MonitorMode, ObsEvent, ProgramStore, ProtocolMachineConfig,
    ProtocolMachineError, ResourceState, RunStatus, SiteId, StepResult, ThreadedRoundSemantics,
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
use crate::kernel::{KernelMachine, ProtocolMachineKernel};
use crate::loader::CodeImage;
use crate::output_condition::{OutputConditionCheck, OutputConditionHint};
use crate::owned::OwnedSession;
use crate::refinement::{
    block_reason_tag, coro_status_tag, ProtocolMachineRefinementSlice, RefinementSliceError,
    SchedulerRefinementSlice, SessionRefinementSlice,
};
use crate::scheduler::Scheduler;
use crate::semantic_objects::{
    protocol_machine_semantic_objects, OperationInstance, OperationPhase, OutstandingEffect,
    OutstandingEffectStatus, ProgressContract, ProgressState, ProgressTransition,
    ProtocolMachineSemanticObjects,
};
use crate::serialization::{
    canonical_replay_fragment_v1, semantic_audit_log_v1, CanonicalReplayFragmentV1,
    SemanticAuditRecord,
};
use crate::session::{
    unfold_if_var_with_scope, AuthorityAuditRecord, CancellationWitness, Edge, OwnershipCapability,
    OwnershipError, OwnershipReceipt, OwnershipScope, ReadinessWitness, SessionHostMutation,
    SessionId, SessionOpenPlan, SessionState, SessionStatus,
};
use crate::transfer_semantics::{
    decode_transfer_request, delegation_receipt, move_endpoint_bundle,
    validate_delegation_coherence, DelegationAuditRecord, DelegationReceipt, DelegationStatus,
};

// Lane identifier in the threaded runtime.

struct OutputHintObservation {
    request: EffectRequest,
    outcome: EffectOutcome,
    hint: Option<OutputConditionHint>,
}

#[derive(Clone)]
struct EffectObservation {
    request: EffectRequest,
    outcome: EffectOutcome,
}

struct ThreadedExecSuccess {
    pack: StepPack,
    effect_observations: Vec<EffectObservation>,
    output_observation: Option<OutputHintObservation>,
}

struct ThreadedExecFault {
    fault: Fault,
    effect_observations: Vec<EffectObservation>,
}

impl ThreadedExecFault {
    fn new(fault: Fault) -> Self {
        Self {
            fault,
            effect_observations: Vec::new(),
        }
    }

    fn with_observation(fault: Fault, observation: EffectObservation) -> Self {
        Self {
            fault,
            effect_observations: vec![observation],
        }
    }
}

mod worker_pool;
use worker_pool::{build_owned_native_pool, OwnedNativeWorkerPool};
pub use worker_pool::{
    NativeWorkerPanic, NativeWorkerPoolBuildFailure, NativeWorkerPoolDisposal,
    NativeWorkerPoolSettlement, NativeWorkerPoolSettlementCause,
    NativeWorkerPoolSettlementProgress, NativeWorkerPoolShutdownFailure,
};
include!("threaded/prelude.rs");
include!("threaded/runtime_and_scheduling.rs");
include!("threaded/owned.rs");
include!("threaded/nominal_command.rs");
include!("threaded/operation_lifecycle.rs");
include!("threaded/semantic_state.rs");
include!("threaded/runtime_introspection.rs");
include!("threaded/session_lifecycle.rs");
include!("threaded/topology_and_planner.rs");
include!("threaded/commit_and_handoff.rs");
include!("threaded/exec_and_validation.rs");
include!("threaded/instructions_send_recv.rs");
include!("threaded/instructions_guard.rs");
include!("threaded/instructions_choice.rs");

#[cfg(test)]
mod tests {
    include!("../tests/unit/threaded_runtime_tests.rs");
}

#[cfg(all(test, not(target_arch = "wasm32")))]
mod thread_pool_error_tests {
    include!("../tests/unit/thread_pool_error_tests.rs");
}

#[cfg(all(test, not(target_arch = "wasm32")))]
mod invoke_outcome_tests {
    use super::*;
    type FixtureMachine = ThreadedProtocolMachine;
    fn make_machine() -> ThreadedProtocolMachine {
        make_machine_with_config(ProtocolMachineConfig::default())
    }
    fn make_machine_with_config(config: ProtocolMachineConfig) -> ThreadedProtocolMachine {
        ThreadedProtocolMachine::with_workers(config, 1)
    }
    fn blocked_acquire_is_fault() -> bool {
        true
    }
    fn snapshot(
        machine: &ThreadedProtocolMachine,
        sid: usize,
    ) -> (*const Value, Vec<Value>, usize, CoroStatus) {
        snapshot_role(machine, sid, "A")
    }
    fn snapshot_role(
        machine: &ThreadedProtocolMachine,
        sid: usize,
        role: &str,
    ) -> (*const Value, Vec<Value>, usize, CoroStatus) {
        let handle = machine
            .coroutines
            .iter()
            .find(|c| {
                let c = c.lock().unwrap();
                c.session_id == sid && c.role == role
            })
            .unwrap();
        let coro = handle.lock().unwrap();
        (
            coro.regs.as_ptr(),
            coro.regs.clone(),
            coro.pc,
            coro.status.clone(),
        )
    }
    include!("../tests/unit/invoke_outcome_atomicity.rs");
    include!("../tests/unit/send_capacity_fixture.rs");
    fn send_counter_dispatch_allocations() -> u64 {
        1
    }
    fn send_counter_queue_state(machine: &FixtureMachine, sid: usize) -> serde_json::Value {
        let resident = machine.sessions.get(sid).unwrap();
        let session = resident.lock().unwrap();
        let edge = Edge::new(sid, "A", "B");
        let endpoint = Endpoint {
            sid,
            role: "A".into(),
        };
        let queue = &session.buffers[&edge];
        serde_json::to_value((
            queue.len(),
            queue.capacity(),
            queue,
            &session.local_types[&endpoint].current,
        ))
        .unwrap()
    }
    fn settle_send_counter_machine(machine: FixtureMachine) {
        let disposal = machine
            .shutdown_worker_pool()
            .expect("join SAME original send counter pool");
        assert_eq!(disposal.joined_workers(), 1);
        assert!(disposal.worker_panics().is_empty());
    }
    include!("../tests/unit/send_capacity_counter.rs");
}

#[cfg(all(test, not(target_arch = "wasm32")))]
mod live_effect_retention_tests {
    use super::*;
    fn make_machine(retention: ObservabilityRetentionConfig) -> ThreadedProtocolMachine {
        ThreadedProtocolMachine::with_workers(
            ProtocolMachineConfig {
                observability_retention: retention,
                ..ProtocolMachineConfig::default()
            },
            1,
        )
    }
    include!("../tests/unit/live_effect_retention.rs");
}

#[cfg(all(test, not(target_arch = "wasm32")))]
mod clock_admission_tests {
    use super::*;
    use crate::ObservabilityRetentionConfig;
    fn make_clock_machine() -> ThreadedProtocolMachine {
        ThreadedProtocolMachine::with_workers(ProtocolMachineConfig::default(), 1)
    }
    fn settle_clock_machine(machine: ThreadedProtocolMachine) {
        let receipt = machine
            .shutdown_worker_pool()
            .expect("join SAME original clock fixture pool");
        assert_eq!(receipt.joined_workers(), 1);
    }
    fn original_round_observations(_: &ThreadedProtocolMachine) -> String {
        String::new()
    }
    fn runtime_clock_snapshot(machine: &ThreadedProtocolMachine) -> serde_json::Value {
        serde_json::to_value((
            machine.coroutines(),
            &machine.scheduler,
            machine.semantic_objects(),
            machine.refinement_slice().unwrap(),
            &machine.trace,
            &machine.effect_trace,
            &machine.effect_exchanges,
            machine.next_effect_id,
        ))
        .unwrap()
    }
    include!("../tests/unit/clock_admission.rs");
    include!("../tests/unit/effect_capacity.rs");
    type NominalCapacityMachine = ThreadedProtocolMachine;
    fn make_nominal_capacity_machine(
        retention: ObservabilityRetentionConfig,
    ) -> NominalCapacityMachine {
        let config = ProtocolMachineConfig {
            observability_retention: retention,
            output_condition_policy: crate::output_condition::OutputConditionPolicy::AllowAll,
            ..ProtocolMachineConfig::default()
        };
        ThreadedProtocolMachine::with_workers(config, 1)
    }
    fn nominal_capacity_expected_original_exchanges(_: ObservabilityRetentionConfig) -> usize {
        2 // This backend's actual diagnostic exchange stream is an unbounded Vec.
    }
    fn nominal_capacity_host_failure_outputs(failure: &EffectFailure) -> serde_json::Value {
        serde_json::to_value(EffectOutcome::failure(failure.clone())).unwrap()
    }
    include!("../tests/unit/nominal_effect_capacity.rs");
    include!("../tests/unit/nominal_effect_capacity_wave.rs");
}
