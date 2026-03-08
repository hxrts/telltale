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
            BlockReason::Recv {
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
            StepUpdate::Blocked(BlockReason::Invoke {
                handler: "default".to_string(),
            }),
        );
        assert_eq!(sched.ready_count(), 0);
        assert_eq!(sched.blocked_count(), 1);
        assert!(matches!(
            sched.block_reason(7),
            Some(BlockReason::Invoke { .. })
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
            BlockReason::Invoke {
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

    #[test]
    fn test_pick_runnable_from_set_skips_ineligible_ready_entries_without_reordering() {
        let mut sched = Scheduler::new(SchedPolicy::Cooperative);
        sched.add_ready(0);
        sched.add_ready(1);
        sched.add_ready(2);

        sched.set_ready_eligibility(2, ReadyEligibility::Eligible);
        assert_eq!(sched.pick_eligible_runnable(|_| false), Some(2));
        assert_eq!(sched.ready_snapshot(), vec![0, 1]);
        assert_eq!(sched.step_count(), 1);
    }
}
