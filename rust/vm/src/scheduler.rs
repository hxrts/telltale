//! Policy-based coroutine scheduler.
//!
//! Matches `SchedPolicy` and `schedStep` from `runtime.md §4`.
//! All policies produce observably equivalent results per the
//! `schedule_confluence` theorem.

use std::collections::{BTreeMap, VecDeque};

use serde::{Deserialize, Serialize};

use crate::coroutine::BlockReason;

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
    /// Multi-threaded work-stealing (native only, requires `multi-thread` feature).
    WorkStealing {
        /// Number of worker threads.
        workers: usize,
    },
    /// Prefer coroutines holding progress tokens (starvation freedom).
    ProgressAware,
}


/// Scheduler state.
#[derive(Debug)]
pub struct Scheduler {
    policy: SchedPolicy,
    ready_queue: VecDeque<usize>,
    blocked_set: BTreeMap<usize, BlockReason>,
    step_count: usize,
}

impl Scheduler {
    /// Create a scheduler with the given policy.
    #[must_use]
    pub fn new(policy: SchedPolicy) -> Self {
        Self {
            policy,
            ready_queue: VecDeque::new(),
            blocked_set: BTreeMap::new(),
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
        self.step_count += 1;
        match &self.policy {
            SchedPolicy::Cooperative | SchedPolicy::RoundRobin => {
                // Round-robin: take from front, put at back after execution.
                self.ready_queue.pop_front()
            }
            SchedPolicy::WorkStealing { .. } => {
                // Placeholder: same as round-robin for now.
                self.ready_queue.pop_front()
            }
            SchedPolicy::ProgressAware => {
                // Placeholder: same as round-robin for now.
                self.ready_queue.pop_front()
            }
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
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::instr::Endpoint;

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

        sched.mark_blocked(0, BlockReason::RecvWait { endpoint: Endpoint { sid: 0, role: "A".into() } });
        assert_eq!(sched.ready_count(), 1);
        assert_eq!(sched.blocked_count(), 1);

        sched.unblock(0);
        assert_eq!(sched.ready_count(), 2);
        assert_eq!(sched.blocked_count(), 0);
    }
}
