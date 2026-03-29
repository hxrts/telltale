//! Concrete protocol-machine refinement slices.
//!
//! These snapshots expose the smallest runtime state surface that we compare
//! exactly across Rust, Lean, and threaded execution: coroutine identity/status,
//! per-session local-type and buffer occupancy counts, and scheduler-ready /
//! blocked state.

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::coroutine::{BlockReason, CoroStatus, Coroutine};
use crate::scheduler::Scheduler;
use crate::session::{SessionState, SessionStatus, SessionStore};

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
