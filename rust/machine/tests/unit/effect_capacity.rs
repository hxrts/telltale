// Shared real backend fixtures; included beside the original clock owner tests.
struct CapacityCallbacks {
    calls: std::sync::Mutex<Vec<EffectRequest>>,
    topology: Vec<TopologyPerturbation>,
}

impl EffectHandler for CapacityCallbacks {
    fn handle_effect(&self, request: EffectRequest) -> EffectOutcome {
        self.calls.lock().unwrap().push(request.clone());
        match request.body {
            crate::effect::EffectRequestBody::TopologyEvents { .. } => {
                EffectOutcome::success(crate::effect::EffectResponse::TopologyEvents {
                    events: self.topology.clone(),
                })
            }
            crate::effect::EffectRequestBody::InvokeStep { state, .. } => {
                EffectOutcome::success(crate::effect::EffectResponse::InvokeStep { state })
            }
            crate::effect::EffectRequestBody::OutputConditionHint { .. } => {
                EffectOutcome::success(crate::effect::EffectResponse::OutputConditionHint {
                    hint: None,
                })
            }
            _ => panic!("unexpected actual capacity fixture request"),
        }
    }
    fn handle_send(&self, _: &str, _: &str, _: &str, _: &[Value]) -> EffectResult<Value> {
        unreachable!()
    }
    fn handle_recv(
        &self,
        _: &str,
        _: &str,
        _: &str,
        _: &mut Vec<Value>,
        _: &Value,
    ) -> EffectResult<()> {
        unreachable!()
    }
    fn handle_choose(&self, _: &str, _: &str, _: &[String], _: &[Value]) -> EffectResult<String> {
        unreachable!()
    }
    fn step(&self, _: &str, _: &mut Vec<Value>) -> EffectResult<()> {
        unreachable!()
    }
}

fn assert_original_capacity_refusal(error: &ProtocolMachineError) {
    let expected =
        EffectFailure::contract_violation("canonical effect occurrence identifiers exhausted");
    match error {
        ProtocolMachineError::HandlerError(failure)
        | ProtocolMachineError::Fault {
            fault: Fault::Invoke { failure },
            ..
        } => {
            assert_eq!(failure, &expected);
        }
        other => panic!("expected exact original effect-capacity refusal, got {other:?}"),
    }
}

#[test]
fn exhausted_effect_ids_refuse_before_original_topology_callback() {
    let mut machine = make_clock_machine();
    let owner = machine
        .load_choreography_owned(&clock_image(), "original-capacity-owner")
        .unwrap();
    let handler = CapacityCallbacks {
        calls: Default::default(),
        topology: vec![],
    };
    machine.next_effect_id = u64::MAX;
    let before = runtime_clock_snapshot(&machine);
    let error = machine.step_round(&handler, 1).unwrap_err();
    let after = runtime_clock_snapshot(&machine);
    let calls = handler.calls.into_inner().unwrap();
    let counter = machine.next_effect_id;
    let no_exchanges = machine.effect_exchanges().is_empty();
    let sid = owner.session_id();
    settle_clock_machine(machine);
    assert_original_capacity_refusal(&error);
    assert!(calls.is_empty());
    assert!(no_exchanges);
    assert_eq!(counter, u64::MAX);
    // Round admission owns the scheduler/model tick; the refusal promises no
    // instruction/host mutation, not rollback of the already admitted round.
    assert_eq!(
        before[0], after[0],
        "original session {sid} coroutine remains unchanged"
    );
}

#[test]
fn complete_instruction_capacity_precedes_real_callback_and_register_mutation() {
    for enough in [false, true] {
        let mut machine = make_clock_machine();
        let mut image = clock_image();
        image.programs.get_mut("A").unwrap()[0] = Instr::Invoke {
            action: crate::instr::InvokeAction::Named("original-capacity-step".into()),
        };
        let owner = machine
            .load_choreography_owned(&image, "original-capacity-owner")
            .unwrap();
        let handler = CapacityCallbacks {
            calls: Default::default(),
            topology: vec![],
        };
        // Public round first records its original topology poll. Successful
        // dispatch must hold all four possible subsequent occurrences.
        machine.next_effect_id = if enough { u64::MAX - 5 } else { u64::MAX - 1 };
        let before: Vec<_> = machine
            .coroutines()
            .iter()
            .map(|c| (c.id, c.pc, c.regs.clone(), c.cost_budget))
            .collect();
        let result = machine.step_round(&handler, 1);
        let after: Vec<_> = machine
            .coroutines()
            .iter()
            .map(|c| (c.id, c.pc, c.regs.clone(), c.cost_budget))
            .collect();
        let calls = handler.calls.into_inner().unwrap();
        let exchanges = machine.effect_exchanges().to_vec();
        let canonical = machine.outstanding_effects().to_vec();
        let publications = machine
            .trace()
            .iter()
            .filter(|event| matches!(event, ObsEvent::Invoked { .. }))
            .count();

        let sid = owner.session_id();
        let tick = machine.clock.tick;
        settle_clock_machine(machine);
        let invokes = calls
            .iter()
            .filter(|r| matches!(r.body, crate::effect::EffectRequestBody::InvokeStep { .. }))
            .count();
        if enough {
            assert!(result.is_ok());
            assert_eq!(invokes, 1);
            assert_eq!(after[0].1, 1);
            assert_capacity_original_invoke(&calls, &exchanges, sid, tick);
        } else {
            assert_original_capacity_refusal(&result.unwrap_err());
            assert_eq!(invokes, 0);
            assert_eq!(
                before, after,
                "original session {sid} instruction state untouched"
            );
            assert_eq!(
                exchanges.len(),
                1,
                "only actual admitted topology poll exists"
            );
        }

        assert_capacity_occurrence_ids(&canonical, &exchanges, publications);
    }
}

#[test]
fn complete_topology_capacity_refuses_before_preceding_crash_mutation() {
    for enough in [false, true] {
        let mut machine = make_clock_machine();
        machine
            .load_choreography_owned(&clock_image(), "original-topology-capacity-owner")
            .unwrap();
        let mut events = vec![TopologyPerturbation::Crash { site: "A".into() }];
        if !enough {
            events.push(TopologyPerturbation::Timeout {
                site: "A".into(),
                duration: Duration::from_secs(1),
            });
        }
        events.sort_by_key(TopologyPerturbation::ordering_key);
        let handler = CapacityCallbacks {
            calls: Default::default(),
            topology: events.clone(),
        };
        machine.next_effect_id = u64::MAX - 2;
        let result = machine.step_round(&handler, 1);
        let crash = machine.crashed_sites.clone();
        let timeouts = machine.timed_out_sites.clone();
        let calls = handler.calls.into_inner().unwrap();
        let exchanges = machine.effect_exchanges().to_vec();
        let applied = machine
            .effect_trace()
            .iter()
            .filter(|entry| entry.effect_kind == "topology_event")
            .cloned()
            .collect::<Vec<_>>();
        let counter = machine.next_effect_id;
        settle_clock_machine(machine);
        if enough {
            assert!(result.is_ok());
            assert!(crash.contains("A"));
            assert_eq!(applied.len(), 1);
            assert_eq!(applied[0].effect_id, u64::MAX - 1);
            assert_eq!(applied[0].topology, Some(events[0].clone()));
            assert_eq!(counter, u64::MAX);
        } else {
            assert_original_capacity_refusal(&result.unwrap_err());
            assert!(crash.is_empty());
            assert!(applied.is_empty());
            assert_eq!(
                counter,
                u64::MAX - 1,
                "actual original poll alone consumes one occurrence"
            );
        }
        assert!(timeouts.is_empty());
        assert_eq!(calls.len(), 1);
        assert_eq!(exchanges.len(), 1);
        assert_eq!(exchanges[0].effect_id, u64::MAX - 2);
        assert_eq!(
            exchanges[0].outcome.clone().into_topology().unwrap(),
            EffectResult::Success(events)
        );
    }
}

fn assert_capacity_original_invoke(
    calls: &[EffectRequest],
    exchanges: &[crate::effect::EffectExchangeRecord],
    sid: crate::session::SessionId,
    tick: u64,
) {
    let invoked = calls
        .iter()
        .find(|request| {
            matches!(
                request.body,
                crate::effect::EffectRequestBody::InvokeStep { .. }
            )
        })
        .unwrap();
    assert_eq!(invoked.session, Some(sid));
    assert_eq!(invoked.tick, tick);
    let retained: Vec<_> = exchanges
        .iter()
        .filter(|record| {
            let mut issued = invoked.clone();
            issued.effect_id = Some(record.effect_id);
            record.request == issued
        })
        .collect();
    assert_eq!(retained.len(), 1);
    let crate::effect::EffectRequestBody::InvokeStep { state, .. } = &invoked.body else {
        unreachable!()
    };
    assert_eq!(
        retained[0]
            .outcome
            .clone()
            .into_invoke_state_for(&invoked.body)
            .unwrap(),
        EffectResult::Success(state.clone())
    );
}

fn assert_capacity_occurrence_ids(
    canonical: &[crate::semantic_objects::OutstandingEffect],
    exchanges: &[crate::effect::EffectExchangeRecord],
    publications: usize,
) {
    let canonical_ids: std::collections::BTreeSet<_> =
        canonical.iter().map(|effect| effect.effect_id).collect();
    assert_eq!(canonical_ids.len(), canonical.len());
    assert_eq!(
        canonical.len(),
        exchanges.len() + publications,
        "every actual callback and derived invocation has its own canonical occurrence"
    );
    assert!(exchanges
        .iter()
        .all(|exchange| canonical_ids.contains(&exchange.effect_id)));
    assert!(canonical_ids.iter().all(|id| *id < u64::MAX));
    let ids: std::collections::BTreeSet<_> = exchanges.iter().map(|e| e.effect_id).collect();
    assert_eq!(ids.len(), exchanges.len());
    assert!(ids.iter().all(|id| *id < u64::MAX));
}
