//! Policy-based coroutine scheduler.
//!
//! Matches `SchedPolicy` and `schedStep` from `runtime.md §4`.
//! All policies produce observably equivalent results per the
//! `schedule_confluence` theorem.

use std::collections::{BTreeMap, VecDeque};

use serde::{Deserialize, Serialize};

use crate::coroutine::BlockReason;

/// Scheduler lane identifier.
pub type LaneId = usize;

fn default_timeslice() -> usize {
    1
}

/// Priority policy family for serialization-safe prioritized scheduling.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum PriorityPolicy {
    /// Fixed static priorities keyed by coroutine id.
    FixedMap(BTreeMap<usize, usize>),
    /// Favor older entries in the ready queue.
    Aging,
    /// Favor coroutines with progress tokens.
    TokenWeighted,
}

/// Scheduling policy.
///
/// All policies are observationally equivalent per the `schedule_confluence`
/// theorem. `Cooperative` is the WASM-compatible single-threaded policy,
/// justified by `cooperative_refines_concurrent`.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub enum SchedPolicy {
    /// Single-threaded round-robin with explicit yield. WASM-compatible.
    #[default]
    Cooperative,
    /// Basic multi-coroutine round-robin.
    RoundRobin,
    /// Priority scheduling without function pointers.
    Priority(PriorityPolicy),
    /// Prefer coroutines holding progress tokens (starvation freedom).
    ProgressAware,
}

/// Step outcome used by scheduler bookkeeping.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StepUpdate {
    /// Coroutine should remain runnable.
    Ready,
    /// Coroutine yielded and remains runnable.
    Yielded,
    /// Coroutine blocked for a reason.
    Blocked(BlockReason),
    /// Coroutine is done/faulted and removed from queues.
    Done,
}

/// Cross-lane capability-transfer record.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CrossLaneHandoff {
    /// Source coroutine id.
    pub from_coro: usize,
    /// Destination coroutine id.
    pub to_coro: usize,
    /// Source lane.
    pub from_lane: LaneId,
    /// Destination lane.
    pub to_lane: LaneId,
    /// Scheduler step where the handoff was emitted.
    pub step: usize,
    /// Free-form reason tag.
    pub reason: String,
}

/// Scheduler state.
#[derive(Debug, Serialize, Deserialize)]
pub struct Scheduler {
    policy: SchedPolicy,
    ready_queue: VecDeque<usize>,
    blocked_set: BTreeMap<usize, BlockReason>,
    #[serde(default)]
    lane_of: BTreeMap<usize, LaneId>,
    #[serde(default)]
    lane_queues: BTreeMap<LaneId, VecDeque<usize>>,
    #[serde(default)]
    lane_blocked: BTreeMap<LaneId, BTreeMap<usize, BlockReason>>,
    #[serde(default)]
    cross_lane_handoffs: Vec<CrossLaneHandoff>,
    #[serde(default = "default_timeslice")]
    timeslice: usize,
    step_count: usize,
}

/// Lean-aligned scheduler state alias.
pub type SchedState = Scheduler;

impl Scheduler {
    /// Create a scheduler with the given policy.
    #[must_use]
    pub fn new(policy: SchedPolicy) -> Self {
        let mut lane_queues = BTreeMap::new();
        lane_queues.insert(0, VecDeque::new());
        let mut lane_blocked = BTreeMap::new();
        lane_blocked.insert(0, BTreeMap::new());
        Self {
            policy,
            ready_queue: VecDeque::new(),
            blocked_set: BTreeMap::new(),
            lane_of: BTreeMap::new(),
            lane_queues,
            lane_blocked,
            cross_lane_handoffs: Vec::new(),
            timeslice: default_timeslice(),
            step_count: 0,
        }
    }

    fn lane_for_or_default(&self, coro_id: usize) -> LaneId {
        self.lane_of.get(&coro_id).copied().unwrap_or(0)
    }

    fn lane_queue_push(&mut self, lane: LaneId, coro_id: usize) {
        let queue = self.lane_queues.entry(lane).or_default();
        if !queue.contains(&coro_id) {
            queue.push_back(coro_id);
        }
    }

    fn lane_queue_remove(&mut self, lane: LaneId, coro_id: usize) {
        if let Some(queue) = self.lane_queues.get_mut(&lane) {
            queue.retain(|id| *id != coro_id);
        }
    }

    fn lane_queue_pop_front(&mut self, lane: LaneId) -> Option<usize> {
        self.lane_queues
            .get_mut(&lane)
            .and_then(VecDeque::pop_front)
    }

    fn remove_from_global_ready(&mut self, coro_id: usize) {
        self.ready_queue.retain(|id| *id != coro_id);
    }

    fn next_lane_with_ready(&self) -> Option<LaneId> {
        let lanes: Vec<LaneId> = self.lane_queues.keys().copied().collect();
        if lanes.is_empty() {
            return None;
        }
        let start = self.step_count % lanes.len();
        for offset in 0..lanes.len() {
            let lane = lanes[(start + offset) % lanes.len()];
            if self
                .lane_queues
                .get(&lane)
                .is_some_and(|queue| !queue.is_empty())
            {
                return Some(lane);
            }
        }
        None
    }

    /// Register a coroutine as ready.
    pub fn add_ready(&mut self, coro_id: usize) {
        let lane = self.lane_for_or_default(coro_id);
        self.lane_of.entry(coro_id).or_insert(lane);
        if !self.ready_queue.contains(&coro_id) {
            self.ready_queue.push_back(coro_id);
        }
        self.lane_queue_push(lane, coro_id);
        if let Some(blocked) = self.lane_blocked.get_mut(&lane) {
            blocked.remove(&coro_id);
        }
    }

    /// Mark a coroutine as blocked.
    pub fn mark_blocked(&mut self, coro_id: usize, reason: BlockReason) {
        let reason_for_lane = reason.clone();
        self.remove_from_global_ready(coro_id);
        self.blocked_set.insert(coro_id, reason);
        let lane = self.lane_for_or_default(coro_id);
        self.lane_queue_remove(lane, coro_id);
        self.lane_blocked
            .entry(lane)
            .or_default()
            .insert(coro_id, reason_for_lane);
    }

    /// Mark a coroutine as done (remove from all queues).
    pub fn mark_done(&mut self, coro_id: usize) {
        self.remove_from_global_ready(coro_id);
        self.blocked_set.remove(&coro_id);
        let lane = self.lane_for_or_default(coro_id);
        self.lane_queue_remove(lane, coro_id);
        if let Some(blocked) = self.lane_blocked.get_mut(&lane) {
            blocked.remove(&coro_id);
        }
    }

    /// Unblock a coroutine (move from blocked to ready).
    pub fn unblock(&mut self, coro_id: usize) {
        if self.blocked_set.remove(&coro_id).is_some() {
            self.ready_queue.push_back(coro_id);
            let lane = self.lane_for_or_default(coro_id);
            self.lane_queue_push(lane, coro_id);
            if let Some(blocked) = self.lane_blocked.get_mut(&lane) {
                blocked.remove(&coro_id);
            }
        }
    }

    /// Pick the next coroutine to execute, or `None` if none are ready.
    pub fn schedule(&mut self) -> Option<usize> {
        self.schedule_with(|_| false)
    }

    /// Pick the next coroutine using a progress predicate.
    pub fn schedule_with<F>(&mut self, has_progress: F) -> Option<usize>
    where
        F: Fn(usize) -> bool,
    {
        let lane = self.next_lane_with_ready()?;
        let policy = self.policy.clone();
        let picked = match policy {
            SchedPolicy::Priority(priority) => {
                self.pick_priority_candidate_in_lane(lane, &priority, has_progress)
            }
            SchedPolicy::ProgressAware => {
                if let Some(pos) = self
                    .lane_queues
                    .get(&lane)
                    .and_then(|queue| queue.iter().position(|id| has_progress(*id)))
                {
                    self.lane_queues
                        .get_mut(&lane)
                        .and_then(|queue| queue.remove(pos))
                } else {
                    self.lane_queue_pop_front(lane)
                }
            }
            SchedPolicy::Cooperative | SchedPolicy::RoundRobin => self.lane_queue_pop_front(lane),
        };
        if let Some(coro_id) = picked {
            self.step_count += 1;
            self.remove_from_global_ready(coro_id);
            Some(coro_id)
        } else {
            None
        }
    }

    /// Lean-aligned scheduler pick entrypoint.
    pub fn pick_runnable<F>(&mut self, has_progress: F) -> Option<usize>
    where
        F: Fn(usize) -> bool,
    {
        self.schedule_with(has_progress)
    }

    /// Lean-aligned scheduler state transition helper.
    pub fn update_after_step(&mut self, coro_id: usize, update: StepUpdate) {
        match update {
            StepUpdate::Ready | StepUpdate::Yielded => self.reschedule(coro_id),
            StepUpdate::Blocked(reason) => self.mark_blocked(coro_id, reason),
            StepUpdate::Done => self.mark_done(coro_id),
        }
    }

    /// Re-enqueue a coroutine that yielded or completed an instruction.
    pub fn reschedule(&mut self, coro_id: usize) {
        self.ready_queue.push_back(coro_id);
        let lane = self.lane_for_or_default(coro_id);
        self.lane_queue_push(lane, coro_id);
    }

    /// Number of ready coroutines.
    #[must_use]
    pub fn ready_count(&self) -> usize {
        self.ready_queue.len()
    }

    /// Snapshot of the current global ready queue order.
    #[must_use]
    pub fn ready_snapshot(&self) -> Vec<usize> {
        self.ready_queue.iter().copied().collect()
    }

    /// Number of blocked coroutines.
    #[must_use]
    pub fn blocked_count(&self) -> usize {
        self.blocked_set.len()
    }

    /// Whether all coroutines are either done or blocked (no progress possible).
    #[must_use]
    pub fn is_stuck(&self) -> bool {
        self.ready_queue.is_empty()
    }

    /// Total steps executed.
    #[must_use]
    pub fn step_count(&self) -> usize {
        self.step_count
    }

    /// Current policy.
    #[must_use]
    pub fn policy(&self) -> &SchedPolicy {
        &self.policy
    }

    /// Configured timeslice.
    #[must_use]
    pub fn timeslice(&self) -> usize {
        self.timeslice
    }

    /// Get the block reason for a coroutine, if blocked.
    #[must_use]
    pub fn block_reason(&self, coro_id: usize) -> Option<&BlockReason> {
        self.blocked_set.get(&coro_id)
    }

    /// All blocked coroutine IDs.
    #[must_use]
    pub fn blocked_ids(&self) -> Vec<usize> {
        self.blocked_set.keys().copied().collect()
    }

    /// Snapshot of blocked coroutine reasons.
    #[must_use]
    pub fn blocked_snapshot(&self) -> BTreeMap<usize, BlockReason> {
        self.blocked_set.clone()
    }

    fn pick_priority_candidate_in_lane<F>(
        &mut self,
        lane: LaneId,
        policy: &PriorityPolicy,
        has_progress: F,
    ) -> Option<usize>
    where
        F: Fn(usize) -> bool,
    {
        let queue = self.lane_queues.get(&lane)?;
        let mut best: Option<(usize, usize)> = None;
        for (pos, id) in queue.iter().copied().enumerate() {
            let score = match policy {
                PriorityPolicy::FixedMap(priorities) => priorities.get(&id).copied().unwrap_or(0),
                PriorityPolicy::Aging => queue.len().saturating_sub(pos),
                PriorityPolicy::TokenWeighted => {
                    let progress = usize::from(has_progress(id));
                    progress * queue.len().saturating_add(1) + queue.len().saturating_sub(pos)
                }
            };
            let replace = match best {
                None => true,
                Some((best_pos, best_score)) => {
                    score > best_score || (score == best_score && pos < best_pos)
                }
            };
            if replace {
                best = Some((pos, score));
            }
        }
        let pos = best.map(|(pos, _)| pos)?;
        self.lane_queues
            .get_mut(&lane)
            .and_then(|lane_queue| lane_queue.remove(pos))
    }

    /// Assign a coroutine to a specific lane.
    pub fn assign_lane(&mut self, coro_id: usize, lane: LaneId) {
        let prior_lane = self.lane_of.insert(coro_id, lane).unwrap_or(0);
        if prior_lane != lane {
            self.lane_queue_remove(prior_lane, coro_id);
            if let Some(reason) = self.blocked_set.get(&coro_id).cloned() {
                self.lane_blocked
                    .entry(prior_lane)
                    .or_default()
                    .remove(&coro_id);
                self.lane_blocked
                    .entry(lane)
                    .or_default()
                    .insert(coro_id, reason);
            }
        }
        if self.ready_queue.contains(&coro_id) {
            self.lane_queue_push(lane, coro_id);
        }
    }

    /// Lane assignment for a coroutine.
    #[must_use]
    pub fn lane_of(&self, coro_id: usize) -> Option<LaneId> {
        self.lane_of.get(&coro_id).copied()
    }

    /// Snapshot of per-lane ready queues.
    #[must_use]
    pub fn lane_queues_snapshot(&self) -> BTreeMap<LaneId, Vec<usize>> {
        self.lane_queues
            .iter()
            .map(|(lane, queue)| (*lane, queue.iter().copied().collect()))
            .collect()
    }

    /// Snapshot of per-lane blocked coroutines.
    #[must_use]
    pub fn lane_blocked_snapshot(&self) -> BTreeMap<LaneId, BTreeMap<usize, BlockReason>> {
        self.lane_blocked.clone()
    }

    /// Record a cross-lane handoff.
    pub fn record_cross_lane_handoff(
        &mut self,
        from_coro: usize,
        to_coro: usize,
        reason: impl Into<String>,
    ) {
        let from_lane = self.lane_for_or_default(from_coro);
        let to_lane = self.lane_for_or_default(to_coro);
        if from_lane != to_lane {
            self.cross_lane_handoffs.push(CrossLaneHandoff {
                from_coro,
                to_coro,
                from_lane,
                to_lane,
                step: self.step_count,
                reason: reason.into(),
            });
        }
    }

    /// Cross-lane handoff log.
    #[must_use]
    pub fn cross_lane_handoffs(&self) -> &[CrossLaneHandoff] {
        &self.cross_lane_handoffs
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::coroutine::ProgressToken;
    use crate::instr::Endpoint;
    use crate::session::Edge;

    #[test]
    fn test_round_robin() {
        let mut sched = Scheduler::new(SchedPolicy::Cooperative);
        sched.add_ready(0);
        sched.add_ready(1);
        sched.add_ready(2);

        assert_eq!(sched.schedule(), Some(0));
        sched.reschedule(0);
        assert_eq!(sched.schedule(), Some(1));
        sched.reschedule(1);
        assert_eq!(sched.schedule(), Some(2));
    }

    #[test]
    fn test_block_unblock() {
        let mut sched = Scheduler::new(SchedPolicy::Cooperative);
        sched.add_ready(0);
        sched.add_ready(1);

        sched.mark_blocked(
            0,
            BlockReason::RecvWait {
                edge: Edge::new(0, "B", "A"),
                token: ProgressToken::for_endpoint(Endpoint {
                    sid: 0,
                    role: "A".into(),
                }),
            },
        );
        assert_eq!(sched.ready_count(), 1);
        assert_eq!(sched.blocked_count(), 1);

        sched.unblock(0);
        assert_eq!(sched.ready_count(), 2);
        assert_eq!(sched.blocked_count(), 0);
    }

    #[test]
    fn test_progress_aware_tie_break_uses_ready_queue_order() {
        let mut sched = Scheduler::new(SchedPolicy::ProgressAware);
        sched.add_ready(3);
        sched.add_ready(1);
        sched.add_ready(2);

        assert_eq!(sched.schedule_with(|id| id % 2 == 1), Some(3));
        sched.reschedule(3);
        assert_eq!(sched.schedule_with(|id| id % 2 == 1), Some(1));
    }

    #[test]
    fn test_priority_fixed_map_prefers_higher_weight() {
        let mut priorities = BTreeMap::new();
        priorities.insert(1, 10);
        priorities.insert(2, 20);
        priorities.insert(3, 5);
        let mut sched = Scheduler::new(SchedPolicy::Priority(PriorityPolicy::FixedMap(priorities)));
        sched.add_ready(1);
        sched.add_ready(2);
        sched.add_ready(3);
        assert_eq!(sched.schedule(), Some(2));
    }

    #[test]
    fn test_update_after_step_routes_blocked_to_blocked_set() {
        let mut sched = Scheduler::new(SchedPolicy::RoundRobin);
        sched.add_ready(7);
        sched.update_after_step(
            7,
            StepUpdate::Blocked(BlockReason::InvokeWait {
                handler: "default".to_string(),
            }),
        );
        assert_eq!(sched.ready_count(), 0);
        assert_eq!(sched.blocked_count(), 1);
        assert!(matches!(
            sched.block_reason(7),
            Some(BlockReason::InvokeWait { .. })
        ));
    }

    #[test]
    fn test_scheduler_state_serde_roundtrip_preserves_lane_views() {
        let mut sched = Scheduler::new(SchedPolicy::ProgressAware);
        sched.assign_lane(0, 0);
        sched.assign_lane(1, 1);
        sched.assign_lane(2, 0);
        sched.assign_lane(3, 1);
        sched.add_ready(0);
        sched.add_ready(1);
        sched.add_ready(2);
        sched.add_ready(3);
        sched.mark_blocked(
            2,
            BlockReason::InvokeWait {
                handler: "io".to_string(),
            },
        );
        sched.record_cross_lane_handoff(0, 1, "transfer 7:A");
        let _ = sched.schedule_with(|id| id == 3);

        let encoded = serde_json::to_string(&sched).expect("serialize scheduler");
        let decoded: Scheduler = serde_json::from_str(&encoded).expect("deserialize scheduler");

        assert_eq!(decoded.policy(), sched.policy());
        assert_eq!(decoded.ready_snapshot(), sched.ready_snapshot());
        assert_eq!(decoded.blocked_snapshot(), sched.blocked_snapshot());
        assert_eq!(decoded.lane_queues_snapshot(), sched.lane_queues_snapshot());
        assert_eq!(
            decoded.lane_blocked_snapshot(),
            sched.lane_blocked_snapshot()
        );
        assert_eq!(decoded.cross_lane_handoffs(), sched.cross_lane_handoffs());
        assert_eq!(decoded.step_count(), sched.step_count());
        assert_eq!(decoded.timeslice(), sched.timeslice());
    }

    #[test]
    fn test_step_count_does_not_advance_when_no_pick() {
        let mut sched = Scheduler::new(SchedPolicy::Cooperative);
        assert_eq!(sched.step_count(), 0);
        assert_eq!(sched.schedule(), None);
        assert_eq!(sched.step_count(), 0);
    }
}
