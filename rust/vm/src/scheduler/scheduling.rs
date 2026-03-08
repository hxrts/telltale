impl Scheduler {
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
                if let Some(pos) = self.lane_queues.get(&lane).and_then(|queue| {
                    queue.iter().position(|id| {
                        self.lane_ready_set
                            .get(&lane)
                            .is_some_and(|ready| ready.contains(id))
                            && has_progress(*id)
                    })
                }) {
                    let picked = self
                        .lane_queues
                        .get_mut(&lane)
                        .and_then(|queue| queue.remove(pos));
                    if let Some(coro_id) = picked {
                        self.lane_queue_remove(lane, coro_id);
                        Some(coro_id)
                    } else {
                        None
                    }
                } else {
                    self.lane_queue_pop_front(lane)
                }
            }
            SchedPolicy::Cooperative | SchedPolicy::RoundRobin => self.lane_queue_pop_front(lane),
        };
        if let Some(coro_id) = picked {
            self.step_count += 1;
            self.remove_from_global_ready(coro_id);
            self.lane_eligible_queue_remove(lane, coro_id);
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

    /// Pick the next runnable coroutine restricted to cached ready eligibility.
    pub fn pick_eligible_runnable<F>(&mut self, has_progress: F) -> Option<usize>
    where
        F: Fn(usize) -> bool + Copy,
    {
        let lane = self.next_lane_with_eligible_ready()?;
        let policy = self.policy.clone();
        let picked = match policy {
            SchedPolicy::Priority(priority) => {
                self.pick_priority_candidate_in_lane_eligible(lane, &priority, has_progress)
            }
            SchedPolicy::ProgressAware => {
                if let Some(pos) = self.lane_eligible_queues.get(&lane).and_then(|queue| {
                    queue.iter().position(|id| {
                        self.lane_eligible_set
                            .get(&lane)
                            .is_some_and(|eligible| eligible.contains(id))
                            && has_progress(*id)
                    })
                }) {
                    let picked = self
                        .lane_eligible_queues
                        .get_mut(&lane)
                        .and_then(|queue| queue.remove(pos));
                    if let Some(coro_id) = picked {
                        self.lane_eligible_queue_remove(lane, coro_id);
                        Some(coro_id)
                    } else {
                        None
                    }
                } else {
                    self.lane_eligible_queue_pop_front(lane)
                }
            }
            SchedPolicy::Cooperative | SchedPolicy::RoundRobin => {
                self.lane_eligible_queue_pop_front(lane)
            }
        };
        if let Some(coro_id) = picked {
            self.step_count += 1;
            self.remove_from_global_ready(coro_id);
            self.lane_queue_remove(lane, coro_id);
            Some(coro_id)
        } else {
            None
        }
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
        if self.ready_set.insert(coro_id) {
            self.ready_queue.push_back(coro_id);
        }
        let lane = self.lane_for_or_default(coro_id);
        self.lane_queue_push(lane, coro_id);
    }

    /// Return whether a coroutine is currently in the global ready set.
    #[must_use]
    pub fn is_ready(&self, coro_id: usize) -> bool {
        self.ready_set.contains(&coro_id)
    }

    /// Number of ready coroutines.
    #[must_use]
    pub fn ready_count(&self) -> usize {
        self.ready_set.len()
    }

    /// Snapshot of the current global ready queue order.
    #[must_use]
    pub fn ready_snapshot(&self) -> Vec<usize> {
        let mut seen = BTreeSet::new();
        self.ready_queue
            .iter()
            .filter_map(|id| {
                if self.ready_set.contains(id) && seen.insert(*id) {
                    Some(*id)
                } else {
                    None
                }
            })
            .collect()
    }

    /// Snapshot of current ready coroutine IDs as a set.
    #[must_use]
    pub fn ready_set_snapshot(&self) -> BTreeSet<usize> {
        self.ready_set.clone()
    }

    /// Return whether any ready coroutine satisfies `predicate`.
    pub fn any_ready<F>(&self, mut predicate: F) -> bool
    where
        F: FnMut(usize) -> bool,
    {
        let mut seen = BTreeSet::new();
        self.ready_queue.iter().copied().any(|coro_id| {
            self.ready_set.contains(&coro_id) && seen.insert(coro_id) && predicate(coro_id)
        })
    }

    /// Number of blocked coroutines.
    #[must_use]
    pub fn blocked_count(&self) -> usize {
        self.blocked_set.len()
    }

    /// Whether all coroutines are either done or blocked (no progress possible).
    #[must_use]
    pub fn is_stuck(&self) -> bool {
        self.ready_set.is_empty()
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

    /// Whether any coroutine is currently cached as both ready and eligible.
    #[must_use]
    pub fn has_eligible_ready(&self) -> bool {
        self.lane_eligible_set
            .values()
            .any(|eligible| !eligible.is_empty())
    }

    /// Update cached ready eligibility for a coroutine.
    pub fn set_ready_eligibility(&mut self, coro_id: usize, eligibility: ReadyEligibility) {
        let lane = self.lane_for_or_default(coro_id);
        if matches!(eligibility, ReadyEligibility::Eligible) && self.ready_set.contains(&coro_id) {
            self.lane_eligible_queue_push(lane, coro_id);
        } else {
            self.lane_eligible_queue_remove(lane, coro_id);
        }
    }

    /// Clear all cached ready eligibility state.
    pub fn clear_ready_eligibility(&mut self) {
        for queue in self.lane_eligible_queues.values_mut() {
            queue.clear();
        }
        for set in self.lane_eligible_set.values_mut() {
            set.clear();
        }
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
            if !self
                .lane_ready_set
                .get(&lane)
                .is_some_and(|ready| ready.contains(&id))
            {
                continue;
            }
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
        let picked = self
            .lane_queues
            .get_mut(&lane)
            .and_then(|lane_queue| lane_queue.remove(pos));
        if let Some(coro_id) = picked {
            self.lane_queue_remove(lane, coro_id);
            Some(coro_id)
        } else {
            None
        }
    }

    fn pick_priority_candidate_in_lane_eligible<FProgress>(
        &mut self,
        lane: LaneId,
        policy: &PriorityPolicy,
        has_progress: FProgress,
    ) -> Option<usize>
    where
        FProgress: Fn(usize) -> bool,
    {
        let queue = self.lane_eligible_queues.get(&lane)?;
        let mut best: Option<(usize, usize)> = None;
        for (pos, id) in queue.iter().copied().enumerate() {
            if !self
                .lane_eligible_set
                .get(&lane)
                .is_some_and(|ready| ready.contains(&id))
            {
                continue;
            }
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
        let picked = self
            .lane_eligible_queues
            .get_mut(&lane)
            .and_then(|lane_queue| lane_queue.remove(pos));
        if let Some(coro_id) = picked {
            self.lane_eligible_queue_remove(lane, coro_id);
            Some(coro_id)
        } else {
            None
        }
    }

    /// Assign a coroutine to a specific lane.
    pub fn assign_lane(&mut self, coro_id: usize, lane: LaneId) {
        self.register_lane(lane);
        let prior_lane = self.lane_of.insert(coro_id, lane).unwrap_or(0);
        if prior_lane != lane {
            self.lane_queue_remove(prior_lane, coro_id);
            let was_eligible = self
                .lane_eligible_set
                .get(&prior_lane)
                .is_some_and(|eligible| eligible.contains(&coro_id));
            self.lane_eligible_queue_remove(prior_lane, coro_id);
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
            if was_eligible && self.ready_set.contains(&coro_id) {
                self.lane_eligible_queue_push(lane, coro_id);
            }
        }
        if self.ready_set.contains(&coro_id) {
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
