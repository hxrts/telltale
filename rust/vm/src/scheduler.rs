//! Policy-based coroutine scheduler.
//!
//! Matches `SchedPolicy` and `schedStep` from `runtime.md §4`.
//! All policies produce observably equivalent results per the
//! `schedule_confluence` theorem.

use std::collections::{BTreeMap, VecDeque};

use serde::{Deserialize, Serialize};

use crate::coroutine::BlockReason;

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

/// Scheduler state.
#[derive(Debug, Serialize, Deserialize)]
pub struct Scheduler {
    policy: SchedPolicy,
    ready_queue: VecDeque<usize>,
    blocked_set: BTreeMap<usize, BlockReason>,
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
        Self {
            policy,
            ready_queue: VecDeque::new(),
            blocked_set: BTreeMap::new(),
            timeslice: default_timeslice(),
            step_count: 0,
        }
    }

    /// Register a coroutine as ready.
    pub fn add_ready(&mut self, coro_id: usize) {
        if !self.ready_queue.contains(&coro_id) {
            self.ready_queue.push_back(coro_id);
        }
    }

    /// Mark a coroutine as blocked.
    pub fn mark_blocked(&mut self, coro_id: usize, reason: BlockReason) {
        self.ready_queue.retain(|&id| id != coro_id);
        self.blocked_set.insert(coro_id, reason);
    }

    /// Mark a coroutine as done (remove from all queues).
    pub fn mark_done(&mut self, coro_id: usize) {
        self.ready_queue.retain(|&id| id != coro_id);
        self.blocked_set.remove(&coro_id);
    }

    /// Unblock a coroutine (move from blocked to ready).
    pub fn unblock(&mut self, coro_id: usize) {
        if self.blocked_set.remove(&coro_id).is_some() {
            self.ready_queue.push_back(coro_id);
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
        self.step_count += 1;
        let policy = self.policy.clone();
        match policy {
            SchedPolicy::Priority(priority) => {
                self.pick_priority_candidate(&priority, has_progress)
            }
            SchedPolicy::ProgressAware => {
                if let Some(pos) = self.ready_queue.iter().position(|id| has_progress(*id)) {
                    return self.ready_queue.remove(pos);
                }
                self.ready_queue.pop_front()
            }
            SchedPolicy::Cooperative | SchedPolicy::RoundRobin => self.ready_queue.pop_front(),
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

    fn pick_priority_candidate<F>(
        &mut self,
        policy: &PriorityPolicy,
        has_progress: F,
    ) -> Option<usize>
    where
        F: Fn(usize) -> bool,
    {
        let mut best: Option<(usize, usize)> = None;
        for (pos, id) in self.ready_queue.iter().copied().enumerate() {
            let score = match policy {
                PriorityPolicy::FixedMap(priorities) => priorities.get(&id).copied().unwrap_or(0),
                PriorityPolicy::Aging => self.ready_queue.len().saturating_sub(pos),
                PriorityPolicy::TokenWeighted => {
                    let progress = usize::from(has_progress(id));
                    progress * self.ready_queue.len().saturating_add(1)
                        + self.ready_queue.len().saturating_sub(pos)
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
        self.ready_queue.remove(pos)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
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
                token: Endpoint {
                    sid: 0,
                    role: "A".into(),
                },
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
}
