// Composite-only regression for the cooperative queue-capacity producer.
#[test]
fn actual_full_send_queue_keeps_original_capacity_obligation_with_disabled_history() {
    use crate::engine::LiveEffectRecord;
    let mut machine = make_machine_with_config(full_queue_config());
    let owner = machine
        .load_choreography_owned(&full_queue_image(), "queue-original")
        .unwrap();
    let sid = owner.session_id();
    machine.pause_role("B");
    let handler = OriginalReply(Mutex::new(None));
    machine.step_round(&handler, 1).unwrap();
    let edge = Edge::new(sid, "A", "B");
    let queue = &machine.sessions.get(sid).unwrap().buffers[&edge];
    assert_eq!(
        (queue.len(), queue.capacity()),
        (1, 1),
        "actual first send filled the original queue"
    );
    let before = snapshot(&machine, sid);
    assert_eq!(before.2, 1);
    let first_records = capacity_send_records(&machine, sid);
    let first_classes = classify_capacity_send_records(&first_records, sid);
    assert_eq!(
        (
            first_classes.0.len(),
            first_classes.1.len(),
            first_classes.2.len()
        ),
        (1, 1, 0)
    );
    machine.step_round(&handler, 1).unwrap();
    let after = snapshot(&machine, sid);
    assert_eq!(
        (after.0, &after.1, after.2),
        (before.0, &before.1, before.2)
    );
    assert!(matches!(
        after.3,
        CoroStatus::Blocked(BlockReason::Send { .. })
    ));
    let records = capacity_send_records(&machine, sid);
    let classes = assert_capacity_send_delta(&first_records, &records, sid);
    let blocked = records
        .iter()
        .find(|record| record.effect_id == classes.2[0])
        .unwrap();
    assert!(blocked.is_live());
    assert_eq!(blocked.completed_at_tick, None);
    // Actual next-round topology cannot create a new send or reset this occurrence.
    machine.step_round(&handler, 1).unwrap();
    let after_topology = capacity_send_records(&machine, sid);
    assert_capacity_topology_records(&records, &after_topology, sid, blocked.effect_id);
    let final_state = snapshot(&machine, sid);
    assert_eq!(
        (final_state.0, &final_state.1, final_state.2),
        (after.0, &after.1, after.2)
    );
    assert_eq!(machine.sessions.get(sid).unwrap().buffers[&edge].len(), 1);
    machine.close_and_reap_session(sid).unwrap();
    assert!(machine
        .outstanding_effects()
        .iter()
        .all(|effect| effect.session != Some(sid)));
}

fn full_queue_config() -> ProtocolMachineConfig {
    use crate::buffer::{BackpressurePolicy, BufferConfig, BufferMode};
    ProtocolMachineConfig {
        buffer_config: BufferConfig {
            mode: BufferMode::Fifo,
            initial_capacity: 1,
            policy: BackpressurePolicy::Block,
        },
        observability_retention: crate::ObservabilityRetentionConfig {
            mode: crate::ObservabilityRetentionMode::Disabled,
            ..crate::ObservabilityRetentionConfig::default()
        },
        ..ProtocolMachineConfig::default()
    }
}

fn assert_capacity_send_delta(
    first_records: &[crate::semantic_objects::OutstandingEffect],
    records: &[crate::semantic_objects::OutstandingEffect],
    sid: usize,
) -> (Vec<u64>, Vec<u64>, Vec<u64>) {
    let first_classes = classify_capacity_send_records(first_records, sid);
    let classes = classify_capacity_send_records(records, sid);
    assert_eq!(
        (classes.0.len(), classes.1.len(), classes.2.len()),
        (2, 1, 1)
    );
    assert_eq!(
        classes.0[0], first_classes.0[0],
        "original first host decision retained"
    );
    assert_eq!(
        classes.1, first_classes.1,
        "only first send committed queue admission"
    );
    for original in first_records {
        assert_eq!(
            records
                .iter()
                .find(|record| record.effect_id == original.effect_id),
            Some(original)
        );
    }
    let new_ids: Vec<_> = records
        .iter()
        .filter(|record| {
            !first_records
                .iter()
                .any(|original| original.effect_id == record.effect_id)
        })
        .map(|record| record.effect_id)
        .collect();
    assert_eq!(
        new_ids,
        vec![classes.0[1], classes.2[0]],
        "second host decision then distinct live capacity obligation"
    );
    classes
}

fn assert_capacity_topology_records(
    records: &[crate::semantic_objects::OutstandingEffect],
    after_topology: &[crate::semantic_objects::OutstandingEffect],
    sid: usize,
    blocked_id: u64,
) {
    use crate::engine::LiveEffectRecord;
    let blocked = records
        .iter()
        .find(|record| record.effect_id == blocked_id)
        .unwrap();
    let retained = after_topology
        .iter()
        .find(|record| record.effect_id == blocked_id)
        .unwrap();
    assert_eq!(
        retained, blocked,
        "original owner, reason, token, issue tick and budget remain unchanged"
    );
    assert!(retained.is_live());
    let original_send_ids: Vec<_> = records.iter().map(|record| record.effect_id).collect();
    let after_topology_send_ids: Vec<_> = after_topology
        .iter()
        .map(|record| record.effect_id)
        .collect();
    assert_eq!(
        after_topology_send_ids, original_send_ids,
        "no new send or capacity occurrence"
    );
    assert_eq!(
        classify_capacity_send_records(after_topology, sid),
        classify_capacity_send_records(records, sid)
    );
}

fn capacity_send_records(
    machine: &FixtureMachine,
    sid: usize,
) -> Vec<crate::semantic_objects::OutstandingEffect> {
    machine
        .outstanding_effects()
        .iter()
        .filter(|effect| effect.session == Some(sid) && effect.effect_kind == "send_decision")
        .cloned()
        .collect()
}

fn classify_capacity_send_records(
    records: &[crate::semantic_objects::OutstandingEffect],
    sid: usize,
) -> (Vec<u64>, Vec<u64>, Vec<u64>) {
    let (mut host, mut committed, mut blocked) = (Vec::new(), Vec::new(), Vec::new());
    let mut identities = std::collections::BTreeSet::new();
    for record in records {
        assert!(
            identities.insert(record.effect_id),
            "each actual occurrence appears once"
        );
        assert_eq!(record.owner_id.as_deref(), Some("queue-original"));
        if let Ok(request) = serde_json::from_value::<EffectRequest>(record.inputs.clone()) {
            assert_eq!(request.effect_id, Some(record.effect_id));
            assert_eq!(request.session, Some(sid));
            assert!(
                matches!(&request.body, EffectRequestBody::SendDecision { role, partner, label, .. } if role == "A" && partner == "B" && label == "m")
            );
            let outcome: EffectOutcome = serde_json::from_value(record.outputs.clone()).unwrap();
            assert_eq!(
                outcome.accepted_status(&request.body),
                EffectOutcomeStatus::Success
            );
            assert_eq!(record.status, OutstandingEffectStatus::Succeeded);
            host.push(record.effect_id);
        } else {
            assert_eq!(
                record.inputs,
                serde_json::json!({"session":sid,"from":"A","to":"B","label":"m"})
            );
            if record.outputs == serde_json::json!({"committed":true}) {
                assert_eq!(record.status, OutstandingEffectStatus::Succeeded);
                committed.push(record.effect_id);
            } else {
                assert_eq!(
                    record.outputs,
                    serde_json::json!({"status":"blocked","reason":"buffer would block"})
                );
                assert_eq!(record.status, OutstandingEffectStatus::Blocked);
                blocked.push(record.effect_id);
            }
        }
    }
    assert_eq!(
        records.len(),
        host.len() + committed.len() + blocked.len(),
        "complete producer classes"
    );
    assert_eq!(
        records
            .iter()
            .filter(|record| record.status == OutstandingEffectStatus::Succeeded)
            .count(),
        host.len() + committed.len(),
        "host success is distinct from queue commitment"
    );
    (host, committed, blocked)
}

fn full_queue_image() -> CodeImage {
    use telltale_types::Label;
    let mut image = receive_image();
    image.programs.insert(
        "A".into(),
        vec![
            Instr::Send { chan: 0, val: 1 },
            Instr::Send { chan: 0, val: 1 },
            Instr::Halt,
        ],
    );
    image.programs.insert(
        "B".into(),
        vec![
            Instr::Receive { chan: 0, dst: 1 },
            Instr::Receive { chan: 0, dst: 1 },
            Instr::Halt,
        ],
    );
    image.global_type = GlobalType::send(
        "A",
        "B",
        Label::new("m"),
        GlobalType::send("A", "B", Label::new("m"), GlobalType::End),
    );
    image.local_types.insert(
        "A".into(),
        LocalTypeR::send(
            "B",
            Label::new("m"),
            LocalTypeR::send("B", Label::new("m"), LocalTypeR::End),
        ),
    );
    image.local_types.insert(
        "B".into(),
        LocalTypeR::recv(
            "A",
            Label::new("m"),
            LocalTypeR::recv("A", Label::new("m"), LocalTypeR::End),
        ),
    );
    image
}
