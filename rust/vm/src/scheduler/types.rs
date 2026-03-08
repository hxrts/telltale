// Policy-based coroutine scheduler.
//
// All policies produce observably equivalent results per the
// `schedule_confluence` theorem in `lean/Runtime/Proofs/SchedulerApi.lean`.

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

/// Cached readiness eligibility for scheduler-side filtered ready queues.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum ReadyEligibility {
    /// Coroutine is both ready and eligible for scheduling.
    Eligible,
    /// Coroutine should be removed from the eligible-ready cache.
    Ineligible,
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
    #[serde(default)]
    ready_set: BTreeSet<usize>,
    blocked_set: BTreeMap<usize, BlockReason>,
    #[serde(default)]
    lane_of: BTreeMap<usize, LaneId>,
    #[serde(default)]
    lane_queues: BTreeMap<LaneId, VecDeque<usize>>,
    #[serde(default)]
    lane_order: Vec<LaneId>,
    #[serde(default)]
    lane_cursor: usize,
    #[serde(default)]
    lane_ready_set: BTreeMap<LaneId, BTreeSet<usize>>,
    #[serde(default)]
    lane_eligible_queues: BTreeMap<LaneId, VecDeque<usize>>,
    #[serde(default)]
    lane_eligible_set: BTreeMap<LaneId, BTreeSet<usize>>,
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
            ready_set: BTreeSet::new(),
            blocked_set: BTreeMap::new(),
            lane_of: BTreeMap::new(),
            lane_queues,
            lane_order: vec![0],
            lane_cursor: 0,
            lane_ready_set: BTreeMap::new(),
            lane_eligible_queues: BTreeMap::new(),
            lane_eligible_set: BTreeMap::new(),
            lane_blocked,
            cross_lane_handoffs: Vec::new(),
            timeslice: default_timeslice(),
            step_count: 0,
        }
    }

    fn register_lane(&mut self, lane: LaneId) {
        self.lane_queues.entry(lane).or_default();
        self.lane_ready_set.entry(lane).or_default();
        self.lane_eligible_queues.entry(lane).or_default();
        self.lane_eligible_set.entry(lane).or_default();
        self.lane_blocked.entry(lane).or_default();
        if let Err(pos) = self.lane_order.binary_search(&lane) {
            self.lane_order.insert(pos, lane);
        }
    }

    fn lane_for_or_default(&self, coro_id: usize) -> LaneId {
        self.lane_of.get(&coro_id).copied().unwrap_or(0)
    }

    fn lane_queue_push(&mut self, lane: LaneId, coro_id: usize) {
        self.register_lane(lane);
        let ready = self.lane_ready_set.entry(lane).or_default();
        if ready.insert(coro_id) {
            self.lane_queues.entry(lane).or_default().push_back(coro_id);
        }
    }

    fn lane_queue_remove(&mut self, lane: LaneId, coro_id: usize) {
        if let Some(ready) = self.lane_ready_set.get_mut(&lane) {
            ready.remove(&coro_id);
        }
    }

    fn lane_eligible_queue_push(&mut self, lane: LaneId, coro_id: usize) {
        self.register_lane(lane);
        let eligible = self.lane_eligible_set.entry(lane).or_default();
        if eligible.insert(coro_id) {
            self.lane_eligible_queues
                .entry(lane)
                .or_default()
                .push_back(coro_id);
        }
    }

    fn lane_eligible_queue_remove(&mut self, lane: LaneId, coro_id: usize) {
        if let Some(eligible) = self.lane_eligible_set.get_mut(&lane) {
            eligible.remove(&coro_id);
        }
    }

    fn lane_queue_pop_front(&mut self, lane: LaneId) -> Option<usize> {
        loop {
            // bounded: queue drains until empty or ready element found
            let coro_id = self
                .lane_queues
                .get_mut(&lane)
                .and_then(VecDeque::pop_front)?;
            if self
                .lane_ready_set
                .get_mut(&lane)
                .is_some_and(|ready| ready.remove(&coro_id))
            {
                return Some(coro_id);
            }
        }
    }

    fn lane_eligible_queue_pop_front(&mut self, lane: LaneId) -> Option<usize> {
        loop {
            // bounded: queue drains until empty or eligible element found
            let coro_id = self
                .lane_eligible_queues
                .get_mut(&lane)
                .and_then(VecDeque::pop_front)?;
            if self
                .lane_eligible_set
                .get_mut(&lane)
                .is_some_and(|eligible| eligible.remove(&coro_id))
            {
                return Some(coro_id);
            }
        }
    }

    fn remove_from_global_ready(&mut self, coro_id: usize) {
        self.ready_set.remove(&coro_id);
    }

    fn next_lane_with_ready(&mut self) -> Option<LaneId> {
        if self.lane_order.is_empty() {
            self.lane_order = self.lane_queues.keys().copied().collect();
        }
        if self.lane_order.is_empty() {
            return None;
        }
        let lane_count = self.lane_order.len();
        let start = self.lane_cursor % lane_count;
        for offset in 0..lane_count {
            let idx = (start + offset) % lane_count;
            let lane = self.lane_order[idx];
            if self
                .lane_ready_set
                .get(&lane)
                .is_some_and(|ready| !ready.is_empty())
            {
                self.lane_cursor = (idx + 1) % lane_count;
                return Some(lane);
            }
        }
        None
    }

    fn next_lane_with_eligible_ready(&mut self) -> Option<LaneId> {
        if self.lane_order.is_empty() {
            self.lane_order = self.lane_queues.keys().copied().collect();
        }
        if self.lane_order.is_empty() {
            return None;
        }
        let lane_count = self.lane_order.len();
        let start = self.lane_cursor % lane_count;
        for offset in 0..lane_count {
            let idx = (start + offset) % lane_count;
            let lane = self.lane_order[idx];
            if self
                .lane_eligible_set
                .get(&lane)
                .is_some_and(|ready| !ready.is_empty())
            {
                self.lane_cursor = (idx + 1) % lane_count;
                return Some(lane);
            }
        }
        None
    }

    /// Register a coroutine as ready.
    pub fn add_ready(&mut self, coro_id: usize) {
        let lane = self.lane_for_or_default(coro_id);
        self.lane_of.entry(coro_id).or_insert(lane);
        if self.ready_set.insert(coro_id) {
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
        self.lane_eligible_queue_remove(lane, coro_id);
    }

    /// Mark a coroutine as done (remove from all queues).
    pub fn mark_done(&mut self, coro_id: usize) {
        self.remove_from_global_ready(coro_id);
        self.blocked_set.remove(&coro_id);
        let lane = self.lane_for_or_default(coro_id);
        self.lane_queue_remove(lane, coro_id);
        self.lane_eligible_queue_remove(lane, coro_id);
        if let Some(blocked) = self.lane_blocked.get_mut(&lane) {
            blocked.remove(&coro_id);
        }
    }

    /// Unblock a coroutine (move from blocked to ready).
    pub fn unblock(&mut self, coro_id: usize) {
        if self.blocked_set.remove(&coro_id).is_some() {
            if self.ready_set.insert(coro_id) {
                self.ready_queue.push_back(coro_id);
            }
            let lane = self.lane_for_or_default(coro_id);
            self.lane_queue_push(lane, coro_id);
            if let Some(blocked) = self.lane_blocked.get_mut(&lane) {
                blocked.remove(&coro_id);
            }
        }
    }

}
