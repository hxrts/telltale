//! Concrete protocol-machine refinement slices.
//!
//! These snapshots expose the smallest runtime state surface that we compare
//! exactly across Rust, Lean, and threaded execution: coroutine identity/status,
//! per-session local-type and buffer occupancy counts, and scheduler-ready /
//! blocked state.

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};
use serde_json::Value;
use telltale_types::de_bruijn::LocalTypeRDB;
use thiserror::Error;

use crate::coroutine::{BlockReason, CoroStatus, Coroutine};
use crate::output_condition::OutputConditionCheck;
use crate::scheduler::Scheduler;
use crate::session::{SessionState, SessionStatus, SessionStore};
use crate::{
    protocol_machine_semantic_objects, semantic_audit_log_v1, DelegationAuditRecord,
    EffectExchangeRecord, ObsEvent, OperationInstance, OutstandingEffect, ProgressContract,
    ProgressTransition, ProtocolMachineSemanticObjects, SemanticAuditRecord,
};

// The refinement slice exports runtime counts through the Rust/Lean bridge as `u64`.
// Keep that conversion contract fail-closed at compile time for supported targets.
const _: () = assert!(usize::BITS <= u64::BITS);

/// Checked-conversion failures while exporting a refinement slice.
#[derive(Debug, Error, Clone, PartialEq, Eq)]
pub enum RefinementSliceError {
    /// A runtime count exceeded the bridge-safe `u64` range.
    #[error("refinement slice field '{field}' value {value} exceeds u64")]
    CountOverflow {
        /// Name of the exported field.
        field: &'static str,
        /// The out-of-range value.
        value: usize,
    },
}

fn checked_u64(field: &'static str, value: usize) -> Result<u64, RefinementSliceError> {
    u64::try_from(value).map_err(|_| RefinementSliceError::CountOverflow { field, value })
}

/// One coroutine-level concrete-state snapshot.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CoroutineRefinementSlice {
    /// Stable coroutine identifier.
    pub coro_id: u64,
    /// Session currently associated with the coroutine.
    pub session_id: u64,
    /// Program counter.
    pub pc: u64,
    /// Coarse coroutine status tag.
    pub status: String,
    /// Number of owned endpoints.
    pub owned_endpoints: u64,
    /// Number of progress tokens.
    pub progress_tokens: u64,
}

impl CoroutineRefinementSlice {
    pub(crate) fn from_coroutine(coro: &Coroutine) -> Result<Self, RefinementSliceError> {
        Ok(Self {
            coro_id: checked_u64("coroutine.id", coro.id)?,
            session_id: checked_u64("coroutine.session_id", coro.session_id)?,
            pc: checked_u64("coroutine.pc", coro.pc)?,
            status: coro_status_tag(&coro.status).to_string(),
            owned_endpoints: checked_u64("coroutine.owned_endpoints", coro.owned_endpoints.len())?,
            progress_tokens: checked_u64("coroutine.progress_tokens", coro.progress_tokens.len())?,
        })
    }
}

/// One session-level concrete-state snapshot.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SessionRefinementSlice {
    /// Session identifier.
    pub sid: u64,
    /// Role count.
    pub role_count: u64,
    /// Number of live local-type entries.
    pub local_type_entries: u64,
    /// Number of buffer edges tracked for the session.
    pub buffer_edges: u64,
    /// Total buffered messages across all edges.
    pub buffered_messages: u64,
    /// Session lifecycle status tag.
    pub status: String,
    /// Current session epoch.
    pub epoch: u64,
}

impl SessionRefinementSlice {
    pub(crate) fn from_session(session: &SessionState) -> Result<Self, RefinementSliceError> {
        let buffered_messages = session.buffers.values().try_fold(0_u64, |acc, buffer| {
            Ok::<_, RefinementSliceError>(
                acc + checked_u64("session.buffered_messages", buffer.len())?,
            )
        })?;
        Ok(Self {
            sid: checked_u64("session.sid", session.sid)?,
            role_count: checked_u64("session.role_count", session.roles.len())?,
            local_type_entries: checked_u64(
                "session.local_type_entries",
                session.local_types.len(),
            )?,
            buffer_edges: checked_u64("session.buffer_edges", session.buffers.len())?,
            buffered_messages,
            status: session_status_tag(&session.status).to_string(),
            epoch: checked_u64("session.epoch", session.epoch)?,
        })
    }
}

/// Scheduler-visible concrete-state snapshot.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SchedulerRefinementSlice {
    /// Global ready-queue order.
    pub ready_queue: Vec<u64>,
    /// Blocked coroutine ids mapped to coarse reason tags.
    pub blocked: BTreeMap<u64, String>,
    /// Scheduler step counter.
    pub step_count: u64,
}

impl SchedulerRefinementSlice {
    pub(crate) fn from_scheduler(scheduler: &Scheduler) -> Result<Self, RefinementSliceError> {
        let ready_queue = scheduler
            .ready_snapshot()
            .into_iter()
            .map(|id| checked_u64("scheduler.ready_queue", id))
            .collect::<Result<Vec<_>, _>>()?;
        let blocked = scheduler
            .blocked_snapshot()
            .into_iter()
            .map(|(id, reason)| {
                Ok::<_, RefinementSliceError>((
                    checked_u64("scheduler.blocked", id)?,
                    block_reason_tag(&reason).to_string(),
                ))
            })
            .collect::<Result<BTreeMap<_, _>, _>>()?;
        Ok(Self {
            ready_queue,
            blocked,
            step_count: checked_u64("scheduler.step_count", scheduler.step_count())?,
        })
    }
}

/// Concrete summary of the most recent scheduler-dispatched transition.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TransitionRefinementSummary {
    /// Coroutine selected for the most recent step, when available.
    pub selected_coro: Option<u64>,
    /// Program counter for the selected coroutine after the most recent step.
    pub selected_pc: Option<u64>,
    /// Lean-compatible local-type snapshot for the selected coroutine endpoint.
    pub selected_type: Option<Value>,
    /// Execution status tag for the most recent step, when available.
    pub exec_status: Option<String>,
    /// Per-session local-type counts after the most recent step.
    pub session_type_counts: BTreeMap<u64, u64>,
    /// Per-session buffered-message counts after the most recent step.
    pub buffered_message_counts: BTreeMap<u64, u64>,
    /// Scheduler ready queue after the most recent step.
    pub ready_queue: Vec<u64>,
    /// Blocked coroutine tags after the most recent step.
    pub blocked: BTreeMap<u64, String>,
}

impl TransitionRefinementSummary {
    pub(crate) fn from_runtime_state(
        coroutines: &[Coroutine],
        sessions: &SessionStore,
        scheduler: &Scheduler,
        last_sched_step: Option<&crate::SchedStepDebug>,
    ) -> Result<Self, RefinementSliceError> {
        let session_slices = sessions
            .iter()
            .map(SessionRefinementSlice::from_session)
            .collect::<Result<Vec<_>, _>>()?;
        let scheduler_slice = SchedulerRefinementSlice::from_scheduler(scheduler)?;
        let session_type_counts = session_slices
            .iter()
            .map(|session| (session.sid, session.local_type_entries))
            .collect();
        let buffered_message_counts = session_slices
            .iter()
            .map(|session| (session.sid, session.buffered_messages))
            .collect();
        Ok(Self {
            selected_coro: last_sched_step
                .map(|step| checked_u64("transition.selected_coro", step.selected_coro))
                .transpose()?,
            selected_pc: selected_pc(coroutines, last_sched_step)?,
            selected_type: selected_type_json(coroutines, sessions, last_sched_step)?,
            exec_status: last_sched_step
                .map(|step| sched_exec_status_tag(&step.exec_status).to_string()),
            session_type_counts,
            buffered_message_counts,
            ready_queue: scheduler_slice.ready_queue,
            blocked: scheduler_slice.blocked,
        })
    }
}

/// Canonical machine-side bundle for the currently claimed runtime refinement core.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ClaimedRuntimeCoreBundle {
    /// Concrete coroutine/session/scheduler slice.
    pub state: ProtocolMachineRefinementSlice,
    /// Most recent scheduler-transition summary.
    pub transition: TransitionRefinementSummary,
}

impl ClaimedRuntimeCoreBundle {
    pub(crate) fn from_runtime_state(
        coroutines: &[Coroutine],
        sessions: &SessionStore,
        scheduler: &Scheduler,
        last_sched_step: Option<&crate::SchedStepDebug>,
    ) -> Result<Self, RefinementSliceError> {
        let state = cooperative_refinement_slice(coroutines, sessions, scheduler)?;
        let transition = TransitionRefinementSummary::from_runtime_state(
            coroutines,
            sessions,
            scheduler,
            last_sched_step,
        )?;
        Ok(Self { state, transition })
    }
}

/// Broader machine-side observation bundle used by operational assurance suites.
///
/// This bundle is intentionally larger than the current claim-critical concrete
/// refinement core. It includes semantic-audit and semantic-object surfaces that
/// are tracked by separate theorem and runtime-assurance families.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct RuntimeObservationBundle {
    /// Concrete coroutine/session/scheduler slice for the current machine state.
    pub state: ProtocolMachineRefinementSlice,
    /// Most recent scheduler-transition summary.
    pub transition: TransitionRefinementSummary,
    /// Canonical semantic audit derived from observable runtime effects.
    pub semantic_audit: Vec<SemanticAuditRecord>,
    /// Canonical effect request/outcome exchanges.
    pub effect_exchanges: Vec<EffectExchangeRecord>,
    /// Deterministic output-condition checks.
    pub output_condition_checks: Vec<OutputConditionCheck>,
    /// Canonical semantic-object export.
    pub semantic_objects: ProtocolMachineSemanticObjects,
}

impl RuntimeObservationBundle {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn from_runtime_state(
        coroutines: &[Coroutine],
        sessions: &SessionStore,
        scheduler: &Scheduler,
        last_sched_step: Option<&crate::SchedStepDebug>,
        authority_audit_log: &[crate::AuthorityAuditRecord],
        delegation_audit_log: &[DelegationAuditRecord],
        operation_instances: &[OperationInstance],
        obs_trace: &[ObsEvent],
        outstanding_effects: &[OutstandingEffect],
        output_condition_checks: &[OutputConditionCheck],
        progress_contracts: &[ProgressContract],
        progress_transitions: &[ProgressTransition],
        effect_exchanges: &[EffectExchangeRecord],
    ) -> Result<Self, RefinementSliceError> {
        let core = ClaimedRuntimeCoreBundle::from_runtime_state(
            coroutines,
            sessions,
            scheduler,
            last_sched_step,
        )?;
        let semantic_audit = semantic_audit_log_v1(
            authority_audit_log,
            delegation_audit_log,
            operation_instances,
            obs_trace,
            outstanding_effects,
            progress_contracts,
            progress_transitions,
        );
        let semantic_objects = protocol_machine_semantic_objects(
            authority_audit_log,
            delegation_audit_log,
            operation_instances,
            outstanding_effects,
            output_condition_checks,
            progress_contracts,
            progress_transitions,
        );
        Ok(Self {
            state: core.state,
            transition: core.transition,
            semantic_audit,
            effect_exchanges: effect_exchanges.to_vec(),
            output_condition_checks: output_condition_checks.to_vec(),
            semantic_objects,
        })
    }
}

fn selected_pc(
    coroutines: &[Coroutine],
    last_sched_step: Option<&crate::SchedStepDebug>,
) -> Result<Option<u64>, RefinementSliceError> {
    let Some(step) = last_sched_step else {
        return Ok(None);
    };
    coroutines
        .iter()
        .find(|coro| coro.id == step.selected_coro)
        .map(|coro| checked_u64("transition.selected_pc", coro.pc))
        .transpose()
}

fn selected_type_json(
    coroutines: &[Coroutine],
    sessions: &SessionStore,
    last_sched_step: Option<&crate::SchedStepDebug>,
) -> Result<Option<Value>, RefinementSliceError> {
    let Some(step) = last_sched_step else {
        return Ok(None);
    };
    let Some(coro) = coroutines.iter().find(|coro| coro.id == step.selected_coro) else {
        return Ok(None);
    };
    let Some(endpoint) = coro.owned_endpoints.first() else {
        return Ok(None);
    };
    let Some(session) = sessions.get(endpoint.sid) else {
        return Ok(None);
    };
    let Some(entry) = session.local_types.get(endpoint) else {
        return Ok(None);
    };
    Ok(Some(Value::String(runtime_local_type_repr(&entry.current))))
}

fn runtime_local_type_repr(local_type: &telltale_types::LocalTypeR) -> String {
    fn render(db: &LocalTypeRDB) -> String {
        match db {
            LocalTypeRDB::End => "LocalType.end_".to_string(),
            LocalTypeRDB::Send { partner, branches } => format!(
                "LocalType.select {:?} [{}]",
                partner,
                branches
                    .iter()
                    .map(|(label, _, cont)| format!("({:?}, {})", label.name, render(cont)))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            LocalTypeRDB::Recv { partner, branches } => format!(
                "LocalType.branch {:?} [{}]",
                partner,
                branches
                    .iter()
                    .map(|(label, _, cont)| format!("({:?}, {})", label.name, render(cont)))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            LocalTypeRDB::Rec(body) => format!("LocalType.mu {}", render(body)),
            LocalTypeRDB::Var(index) => format!("LocalType.var {index}"),
        }
    }

    render(&LocalTypeRDB::from(local_type))
}

/// Concrete cooperative runtime slice used for exact refinement comparison.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProtocolMachineRefinementSlice {
    /// Coroutine snapshots in deterministic id order.
    pub coroutines: Vec<CoroutineRefinementSlice>,
    /// Session snapshots in deterministic session-id order.
    pub sessions: Vec<SessionRefinementSlice>,
    /// Scheduler-visible state.
    pub scheduler: SchedulerRefinementSlice,
}

pub(crate) fn block_reason_tag(reason: &BlockReason) -> &'static str {
    match reason {
        BlockReason::Recv { .. } => "recv_wait",
        BlockReason::Send { .. } => "send_wait",
        BlockReason::Invoke { .. } => "invoke_wait",
        BlockReason::AcquireDenied { .. } => "acquire_denied",
        BlockReason::Consensus { .. } => "consensus_wait",
        BlockReason::Spawn => "spawn_wait",
        BlockReason::Close { .. } => "close_wait",
    }
}

pub(crate) fn coro_status_tag(status: &CoroStatus) -> &'static str {
    match status {
        CoroStatus::Ready => "ready",
        CoroStatus::Blocked(_) => "blocked",
        CoroStatus::Done => "done",
        CoroStatus::Faulted(_) => "faulted",
        CoroStatus::Speculating => "speculating",
    }
}

pub(crate) fn session_status_tag(status: &SessionStatus) -> &'static str {
    match status {
        SessionStatus::Active => "active",
        SessionStatus::Draining => "draining",
        SessionStatus::Closed => "closed",
        SessionStatus::Cancelled => "cancelled",
        SessionStatus::Faulted { .. } => "faulted",
    }
}

pub(crate) fn sched_exec_status_tag(status: &crate::SchedExecStatus) -> &'static str {
    match status {
        crate::SchedExecStatus::Continue => "continue",
        crate::SchedExecStatus::Yielded => "yielded",
        crate::SchedExecStatus::Blocked => "blocked",
        crate::SchedExecStatus::Halted => "halted",
        crate::SchedExecStatus::Faulted => "faulted",
    }
}

pub(crate) fn cooperative_refinement_slice(
    coroutines: &[Coroutine],
    sessions: &SessionStore,
    scheduler: &Scheduler,
) -> Result<ProtocolMachineRefinementSlice, RefinementSliceError> {
    let coroutines = coroutines
        .iter()
        .map(CoroutineRefinementSlice::from_coroutine)
        .collect::<Result<Vec<_>, _>>()?;
    let sessions = sessions
        .iter()
        .map(SessionRefinementSlice::from_session)
        .collect::<Result<Vec<_>, _>>()?;
    let scheduler = SchedulerRefinementSlice::from_scheduler(scheduler)?;
    Ok(ProtocolMachineRefinementSlice {
        coroutines,
        sessions,
        scheduler,
    })
}

#[cfg(test)]
mod tests {
    use super::runtime_local_type_repr;
    use telltale_types::{Label, LocalTypeR};

    #[test]
    fn runtime_local_type_repr_erases_payloads_into_lean_shape() {
        let local = LocalTypeR::Recv {
            partner: "B".to_string(),
            branches: vec![(Label::new("pong"), None, LocalTypeR::End)],
        };
        assert_eq!(
            runtime_local_type_repr(&local),
            r#"LocalType.branch "B" [("pong", LocalType.end_)]"#
        );
    }

    #[test]
    fn runtime_local_type_repr_uses_de_bruijn_recursion_indices() {
        let local = LocalTypeR::mu(
            "Loop",
            LocalTypeR::send("Peer", Label::new("tick"), LocalTypeR::var("Loop")),
        );
        assert_eq!(
            runtime_local_type_repr(&local),
            r#"LocalType.mu LocalType.select "Peer" [("tick", LocalType.var 0)]"#
        );
    }
}
