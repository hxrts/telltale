// Actual owned queue + successful SendDecision; never a host-Blocked substitute.
struct SendCounterHandler {
    original: OriginalReply,
    returned: Mutex<Vec<(EffectRequest, EffectOutcome)>>,
}
impl SendCounterHandler {
    fn new() -> Self {
        Self {
            original: OriginalReply(Mutex::new(None)),
            returned: Default::default(),
        }
    }
}
impl EffectHandler for SendCounterHandler {
    fn supports_wal_sync(&self) -> bool {
        true
    }
    fn handle_effect(&self, request: EffectRequest) -> EffectOutcome {
        let outcome = if matches!(&request.body, EffectRequestBody::WalSync { .. }) {
            EffectOutcome::success(EffectResponse::WalSync)
        } else {
            self.original.handle_effect(request.clone())
        };
        self.returned
            .lock()
            .unwrap()
            .push((request, outcome.clone()));
        outcome
    }
    fn handle_send(&self, _: &str, _: &str, _: &str, _: &[Value]) -> EffectResult<Value> {
        unreachable!("typed actual queue fixture")
    }
    fn handle_recv(
        &self,
        _: &str,
        _: &str,
        _: &str,
        _: &mut Vec<Value>,
        _: &Value,
    ) -> EffectResult<()> {
        unreachable!("typed actual queue fixture")
    }
    fn handle_choose(&self, _: &str, _: &str, _: &[String], _: &[Value]) -> EffectResult<String> {
        unreachable!("typed actual queue fixture")
    }
    fn step(&self, _: &str, _: &mut Vec<Value>) -> EffectResult<()> {
        unreachable!("typed actual queue fixture")
    }
}

#[test]
fn actual_queue_would_block_counts_only_original_dispatch_allocations() {
    let mut config = full_queue_config();
    config.output_condition_policy = crate::output_condition::OutputConditionPolicy::AllowAll;
    let mut machine = make_machine_with_config(config);
    let owner = machine
        .load_choreography_owned(&full_queue_image(), "queue-original")
        .unwrap();
    let sid = owner.session_id();
    machine.set_paused_roles(&std::collections::BTreeSet::from(["B".to_string()]));
    assert!(machine.crashed_sites.is_empty());
    assert!(machine.timed_out_sites.is_empty());
    assert!(machine.partitioned_edges.is_empty());
    assert_eq!(owner.capability().owner_id, "queue-original");
    let handler = SendCounterHandler::new();
    machine
        .step_round(&handler, 1)
        .expect("first actual send fills native queue");
    let before = snapshot(&machine, sid);
    let before_queue = send_counter_queue_state(&machine, sid);
    assert_eq!(before.2, 1);
    assert_eq!(before_queue[0], serde_json::json!(1));
    assert_eq!(before_queue[1], serde_json::json!(1));
    let before_calls = handler.returned.lock().unwrap().clone();
    assert_eq!(
        before_calls
            .iter()
            .filter(|(r, _)| matches!(&r.body, EffectRequestBody::OutputConditionHint { .. }))
            .count(),
        1
    );
    assert_eq!(
        before_calls
            .iter()
            .filter(|(r, _)| matches!(&r.body, EffectRequestBody::WalSync { .. }))
            .count(),
        1
    );
    let before_tick = machine.clock.tick;
    let seed = u64::MAX - 5; // poll1 + full conservative fresh dispatch bound4 admitted.
    assert!(seed > machine.next_effect_id);
    machine.next_effect_id = seed;
    let result = machine.step_round(&handler, 1);
    let after = snapshot(&machine, sid);
    let after_queue = send_counter_queue_state(&machine, sid);
    let calls = handler.returned.lock().unwrap()[before_calls.len()..].to_vec();
    let records: Vec<_> = machine
        .outstanding_effects()
        .iter()
        .filter(|effect| effect.session == Some(sid) && effect.effect_id >= seed)
        .cloned()
        .collect();
    let next = machine.next_effect_id;
    let tick = machine.clock.tick;
    settle_send_counter_machine(machine);
    assert!(result.is_ok());
    assert_eq!(tick, before_tick + 1);
    assert_eq!(next - seed, 1 + send_counter_dispatch_allocations());
    assert_eq!(
        (after.0, &after.1, after.2),
        (before.0, &before.1, before.2)
    );
    assert_eq!(
        after_queue, before_queue,
        "same queued bytes and exact local type remain"
    );
    assert!(
        matches!(after.3, CoroStatus::Blocked(BlockReason::Send { edge })
        if edge == Edge::new(sid, "A", "B"))
    );
    assert_send_counter_observations(&calls, &records, sid, seed, tick);
}

fn assert_send_counter_observations(
    calls: &[(EffectRequest, EffectOutcome)],
    records: &[crate::semantic_objects::OutstandingEffect],
    sid: usize,
    seed: u64,
    tick: u64,
) {
    assert_eq!(
        calls.len(),
        2,
        "poll and successful SendDecision only: no hint/WAL callback"
    );
    assert!(
        matches!(&calls[0].0.body, EffectRequestBody::TopologyEvents { tick: original } if *original == tick)
    );
    assert_eq!(
        calls[0].1,
        EffectOutcome::success(EffectResponse::TopologyEvents { events: vec![] })
    );
    let (request, outcome) = &calls[1];
    assert_eq!(request.tick, tick);
    assert_eq!(request.session, Some(sid));
    assert_eq!(request.effect_id, None);
    assert!(
        matches!(&request.body, EffectRequestBody::SendDecision { role, partner, label, payload, .. }
        if role == "A" && partner == "B" && label == "m" && payload == &Some(Value::Unit))
    );
    assert_eq!(
        outcome,
        &EffectOutcome::success(EffectResponse::SendDecision {
            decision: SendDecision::Deliver(Value::Unit)
        })
    );
    assert_eq!(
        records.len(),
        usize::try_from(send_counter_dispatch_allocations()).unwrap()
    );
    assert!(records
        .iter()
        .all(|record| record.effect_kind == "send_decision"));
    assert!(records.iter().all(|record| record.session == Some(sid)
        && record.owner_id.as_deref() == Some("queue-original")));
    let decision = &records[0];
    assert_eq!(decision.effect_id, seed + 1);
    assert_eq!(decision.status, OutstandingEffectStatus::Succeeded);
    let mut assigned = request.clone();
    assigned.effect_id = Some(seed + 1);
    assert_eq!(decision.inputs, serde_json::to_value(assigned).unwrap());
    assert_eq!(decision.outputs, serde_json::to_value(outcome).unwrap());
    if send_counter_dispatch_allocations() == 2 {
        let blocked = &records[1];
        assert_eq!(blocked.effect_id, seed + 2);
        assert_eq!(blocked.status, OutstandingEffectStatus::Blocked);
        assert_eq!(blocked.completed_at_tick, None);
        assert_eq!(
            blocked.inputs,
            serde_json::json!({"session":sid,"from":"A","to":"B","label":"m"})
        );
        assert_eq!(
            blocked.outputs,
            serde_json::json!({"status":"blocked","reason":"buffer would block"})
        );
    }
}
