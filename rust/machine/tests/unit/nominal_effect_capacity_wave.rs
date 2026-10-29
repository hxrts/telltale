// Included only by the existing native multi-thread backend test owner.
#[test]
fn original_nominal_zero_fresh_fallback_restores_other_real_public_wave_pick() {
    for retention in nominal_boundary_retentions() {
        let config = ProtocolMachineConfig {
            observability_retention: retention,
            output_condition_policy: crate::output_condition::OutputConditionPolicy::AllowAll,
            threaded_round_semantics: crate::engine::ThreadedRoundSemantics::WaveParallelExtension,
            ..ProtocolMachineConfig::default()
        };
        let mut machine = ThreadedProtocolMachine::with_workers(config, 2);
        let handler = NominalBoundaryHandler::new(vec![
            NominalBoundaryReply::Blocked,
            NominalBoundaryReply::Blocked,
        ]);
        let original_owner = machine
            .load_choreography_owned(&nominal_boundary_image(), "actual-first-nominal-wave-owner")
            .unwrap();
        drive_nominal_boundary(&mut machine, &handler);
        machine
            .step_round(&handler, 1)
            .expect("actual first callback Blocked");
        let original = nominal_boundary_original(&machine);
        assert!(original.returned.is_none());
        assert_eq!(handler.nominal_requests().len(), 1);
        // Actual loader-issued id2 shares lane0 with originalA0. It remains
        // resident and ready; the public planner must skip that conflicting pick.
        let padding_owner = machine
            .load_choreography_owned(&clock_image(), "actual-unselected-same-lane-owner")
            .unwrap();
        let padding = machine
            .session_coroutines(padding_owner.session_id())
            .into_iter()
            .next()
            .unwrap();
        let later_owner = machine
            .load_choreography_owned(&clock_image(), "actual-other-wave-owner")
            .unwrap();
        let later = machine
            .session_coroutines(later_owner.session_id())
            .into_iter()
            .next()
            .unwrap();
        assert_eq!(later.pc, 0);
        assert_eq!(later.status, crate::coroutine::CoroStatus::Ready);
        assert_ne!(original_owner.session_id(), later_owner.session_id());
        let before_trace = machine.lane_trace().len();
        let before_tick = machine.clock.tick;
        machine.next_effect_id = u64::MAX - 1;
        let result = machine.step_round(&handler, 2);
        let selected = machine.lane_trace()[before_trace..].to_vec();
        let after = machine
            .session_coroutines(later_owner.session_id())
            .into_iter()
            .next()
            .unwrap();
        let later_ready = machine.scheduler.is_ready(later.id);
        let padding_after = machine
            .session_coroutines(padding_owner.session_id())
            .into_iter()
            .next()
            .unwrap();
        let padding_ready = machine.scheduler.is_ready(padding.id);
        let retained = nominal_boundary_original(&machine);
        let next = machine.next_effect_id;
        let tick = machine.clock.tick;
        let disposal = machine
            .shutdown_worker_pool()
            .expect("join actual original two-worker pool");
        assert_eq!(disposal.joined_workers(), 2);
        assert!(disposal.worker_panics().is_empty());
        assert!(result.is_ok());
        assert_eq!(tick, before_tick + 1);
        assert_eq!(next, u64::MAX);
        assert_eq!(retained, original);
        assert_nominal_original_requests(&handler, &original, original_owner.session_id(), 2);
        assert_eq!(handler.hints(), 0);
        assert_eq!(handler.wals(), 0);
        assert_eq!(
            selected.len(),
            2,
            "actual public planner selected both before fallback"
        );
        assert_eq!(selected[0].session, original_owner.session_id());
        assert_eq!(selected[1].coro_id, later.id);
        assert_eq!(selected[1].session, later_owner.session_id());
        assert_ne!(selected[0].lane, selected[1].lane);
        assert!(selected
            .iter()
            .all(|pick| pick.tick == tick && pick.wave == 0));
        assert!(selected.iter().all(|pick| pick.coro_id != padding.id));
        assert_nominal_wave_restored(&later, &after, later_ready);
        assert_nominal_wave_restored(&padding, &padding_after, padding_ready);
    }
}

fn assert_nominal_wave_restored(before: &Coroutine, after: &Coroutine, ready: bool) {
    assert_eq!(
        (after.pc, &after.regs, after.cost_budget),
        (before.pc, &before.regs, before.cost_budget)
    );
    assert_eq!(after.status, crate::coroutine::CoroStatus::Ready);
    assert!(
        ready,
        "actual unexecuted pick remains in original scheduler ready set"
    );
}
