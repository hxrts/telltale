//! The ProtocolMachine: ties coroutines, sessions, and scheduler together.
//!
//! Execution follows the Lean spec pattern:
//! - `exec_instr` fetches, dispatches to per-instruction step functions
//! - Each step function owns its type checking via `SessionStore::lookup_type`
//! - Results are bundled in `StepPack` and committed atomically via `commit_pack`
//! - Blocking never advances type state
//!
//! This module is a runtime surface over the canonical `ProtocolMachineKernel` execution
//! contract. Driver layers call into `ProtocolMachineKernel` and do not redefine instruction
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
use crate::communication_replay::{
    CommunicationConsumeResult, CommunicationConsumption, CommunicationConsumptionArtifact,
    CommunicationIdentity, CommunicationNullifierIdentity, CommunicationReplayError,
    CommunicationReplayMode, CommunicationStepKind, DefaultCommunicationConsumption,
};
use crate::coroutine::{
    BlockReason, CoroStatus, Coroutine, Fault, KnowledgeFact, ProgressToken, Value,
};
use crate::determinism::{DeterminismMode, EffectDeterminismTier};
#[cfg(test)]
use crate::effect::SendDecisionInput;
use crate::effect::{
    infer_effect_interface_and_operation, CorruptionType, EffectExchangeRecord, EffectFailure,
    EffectHandler, EffectOutcome, EffectRequest, EffectResult, EffectTraceEntry,
    ReplayEffectHandler, SendDecision, TopologyPerturbation,
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
    decode_branch_label_payload, decode_endpoint_fact,
    endpoint_from_reg as decode_endpoint_from_reg,
};
use crate::intern::{EdgeId, EdgeSymbolTable, StringId, SymbolTable};
use crate::kernel::{KernelMachine, ProtocolMachineKernel};
use crate::loader::CodeImage;
use crate::output_condition::{OutputConditionCheck, OutputConditionPolicy};
use crate::persistence::{NoopPersistence, PersistenceModel};
use crate::refinement::{
    cooperative_refinement_slice, ProtocolMachineRefinementSlice, RefinementSliceError,
};
use crate::scheduler::{SchedPolicy, Scheduler};
use crate::semantic_objects::{
    protocol_machine_semantic_objects, OperationInstance, OperationPhase, OutstandingEffect,
    OutstandingEffectStatus, ProgressContract, ProgressState, ProgressTransition,
    ProtocolMachineSemanticObjects,
};
use crate::serialization::{
    canonical_replay_fragment_v1, semantic_audit_log_v1, CanonicalReplayFragmentV1,
    SemanticAuditRecord,
};
#[allow(unused_imports)]
use crate::session::SessionHostMutation;
use crate::session::{
    unfold_if_var_with_scope, AuthorityArtifact, AuthorityAuditEvent, AuthorityAuditRecord,
    AuthorityWitnessId, CancellationWitness, ClosedSessionSummary, Edge, FragmentOwnerId,
    OwnershipError, OwnershipReceipt, OwnershipScope, OwnershipTerminalReason, SessionId,
    SessionStatus, SessionStore, SessionStoreMemoryUsage, TimeoutWitness,
};
use crate::transfer_semantics::{
    decode_transfer_request, delegation_receipt, endpoint_owner_ids, move_endpoint_bundle,
    validate_delegation_coherence, DelegationAuditRecord, DelegationReceipt, DelegationStatus,
};
use crate::verification::{DefaultVerificationModel, HashModel, VerificationModel};

include!("engine/runtime_state/mod.rs");
include!("engine/protocol_machine_config.rs");
include!("engine/protocol_machine_error_and_step_pack.rs");
include!("engine/runtime_exec/mod.rs");
include!("engine/validation.rs");
include!("engine/topology_and_dispatch.rs");
include!("engine/instruction_effects.rs");
include!("engine/nominal_command.rs");
include!("engine/operation_lifecycle.rs");
include!("engine/instruction_tag.rs");
include!("engine/instruction_choice.rs");
include!("engine/open_commit.rs");
include!("engine/kernel_impl.rs");

#[cfg(test)]
mod tests {
    include!("../tests/unit/protocol_machine/tests_handlers_core.rs");
    include!("../tests/unit/protocol_machine/tests_handlers_edge.rs");
    include!("../tests/unit/protocol_machine/tests_runtime_progress.rs");
    include!("../tests/unit/protocol_machine/tests_monitor_persist.rs");
    include!("../tests/unit/protocol_machine/tests_compiler_topology.rs");
    include!("../tests/unit/protocol_machine/tests_timeout_witness_exhaustion.rs");
    include!("../tests/unit/protocol_machine/tests_flow_policy_faults.rs");
    include!("../tests/unit/protocol_machine/tests_semantic_state.rs");
}

#[cfg(all(test, not(target_arch = "wasm32")))]
mod invoke_outcome_tests {
    use super::*;
    type FixtureMachine = ProtocolMachine;
    fn make_machine() -> ProtocolMachine {
        make_machine_with_config(ProtocolMachineConfig::default())
    }
    fn make_machine_with_config(config: ProtocolMachineConfig) -> ProtocolMachine {
        ProtocolMachine::new(config)
    }
    fn blocked_acquire_is_fault() -> bool {
        false
    }
    fn snapshot(
        machine: &ProtocolMachine,
        sid: usize,
    ) -> (*const Value, Vec<Value>, usize, CoroStatus) {
        snapshot_role(machine, sid, "A")
    }
    fn snapshot_role(
        machine: &ProtocolMachine,
        sid: usize,
        role: &str,
    ) -> (*const Value, Vec<Value>, usize, CoroStatus) {
        let coro = machine
            .coroutines
            .iter()
            .find(|c| c.session_id == sid && c.role == role)
            .unwrap();
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
        2
    }
    fn send_counter_queue_state(machine: &FixtureMachine, sid: usize) -> serde_json::Value {
        let session = machine.sessions.get(sid).unwrap();
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
        drop(machine);
    }
    include!("../tests/unit/send_capacity_counter.rs");

    include!("../tests/unit/send_capacity_retention.rs");
}

#[cfg(all(test, not(target_arch = "wasm32")))]
mod live_effect_retention_tests {
    use super::*;
    fn make_machine(retention: ObservabilityRetentionConfig) -> ProtocolMachine {
        ProtocolMachine::new(ProtocolMachineConfig {
            observability_retention: retention,
            ..ProtocolMachineConfig::default()
        })
    }
    include!("../tests/unit/live_effect_retention.rs");
}

#[cfg(test)]
mod clock_admission_tests {
    use super::*;
    fn make_clock_machine() -> ProtocolMachine {
        ProtocolMachine::new(ProtocolMachineConfig::default())
    }
    fn settle_clock_machine(machine: ProtocolMachine) {
        drop(machine);
    }
    fn original_round_observations(machine: &ProtocolMachine) -> String {
        format!(
            "{:?}|{:?}",
            machine.last_sched_step, machine.last_pre_dispatch_state
        )
    }
    fn runtime_clock_snapshot(machine: &ProtocolMachine) -> serde_json::Value {
        serde_json::to_value((
            &machine.coroutines,
            &machine.sched,
            machine.semantic_objects(),
            machine.refinement_slice().unwrap(),
            &machine.obs_trace,
            &machine.effect_trace,
            &machine.effect_exchanges,
            machine.next_effect_id,
        ))
        .unwrap()
    }
    include!("../tests/unit/clock_admission.rs");
    include!("../tests/unit/effect_capacity.rs");
    type NominalCapacityMachine = ProtocolMachine;
    fn make_nominal_capacity_machine(
        retention: ObservabilityRetentionConfig,
    ) -> NominalCapacityMachine {
        let config = ProtocolMachineConfig {
            observability_retention: retention,
            output_condition_policy: crate::output_condition::OutputConditionPolicy::AllowAll,
            ..ProtocolMachineConfig::default()
        };
        ProtocolMachine::new(config)
    }
    fn nominal_capacity_expected_original_exchanges(
        retention: ObservabilityRetentionConfig,
    ) -> usize {
        match retention.mode {
            ObservabilityRetentionMode::Full => 2,
            ObservabilityRetentionMode::Disabled => 0,
            ObservabilityRetentionMode::Capped => 2.min(retention.capacity),
        }
    }
    fn nominal_capacity_host_failure_outputs(failure: &EffectFailure) -> serde_json::Value {
        serde_json::json!({"status":"failure", "failure":failure})
    }
    include!("../tests/unit/nominal_effect_capacity.rs");
}
