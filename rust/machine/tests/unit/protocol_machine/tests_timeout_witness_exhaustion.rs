#[test]
fn timeout_witness_exhaustion_preserves_original_timeout_and_evidence() {
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    let image = CodeImage {
        programs: BTreeMap::from([("A".into(), vec![Instr::Halt])]),
        global_type: GlobalType::End,
        local_types: BTreeMap::from([("A".into(), LocalTypeR::End)]),
    };
    let owner = machine
        .load_choreography_owned(&image, "original/owner")
        .unwrap();
    machine.next_authority_witness_id = u64::MAX - 1;
    let event = TopologyPerturbation::Timeout {
        site: "A".into(),
        duration: Duration::from_millis(20),
    };
    machine.apply_topology_event(&event).unwrap();
    assert_eq!(machine.next_authority_witness_id, u64::MAX);
    let original = machine.timed_out_sites["A"].clone();
    assert_eq!(original.witness_id, u64::MAX - 1);
    let audit = serde_json::to_value(&machine.authority_audit_log).unwrap();
    let trace = serde_json::to_value(&machine.obs_trace).unwrap();
    let eligibility = machine.timed_out_coro_ids.clone();
    let clock = serde_json::to_value(&machine.clock).unwrap();
    let error = machine.apply_topology_event(&event).unwrap_err();
    assert!(matches!(error, ProtocolMachineError::HandlerError(_)));
    assert_eq!(machine.next_authority_witness_id, u64::MAX);
    assert_eq!(machine.timed_out_sites["A"], original);
    assert_eq!(
        serde_json::to_value(&machine.authority_audit_log).unwrap(),
        audit
    );
    assert_eq!(serde_json::to_value(&machine.obs_trace).unwrap(), trace);
    assert_eq!(machine.timed_out_coro_ids, eligibility);
    assert_eq!(serde_json::to_value(&machine.clock).unwrap(), clock);
    assert!(machine.apply_topology_event(&event).is_err());
    assert_eq!(machine.timed_out_sites["A"], original);
    // Global timeout evidence exhaustion does not revoke a real session owner
    // or consume its separate session-local witness inventory.
    let readiness = owner
        .issue_readiness_witness(&mut machine, "original/still-live")
        .unwrap();
    owner
        .consume_readiness_witness(&mut machine, &readiness)
        .unwrap();
}

#[test]
fn timeout_witness_batch_exhaustion_refuses_preceding_topology_mutations() {
    // Enforced Full determinism admits the canonically ordered Crash/Timeout
    // batch. Exhaustion must refuse before applying even the preceding Crash.
    let config = ProtocolMachineConfig::default();
    assert_eq!(config.determinism_mode, DeterminismMode::Full);
    assert_eq!(config.host_contract_assertions, HostContractMode::Enforced);
    let expected = sorted_timeout_capacity_events();
    assert!(expected
        .windows(2)
        .all(|pair| pair[0].ordering_key() <= pair[1].ordering_key()));
    let mut machine = ProtocolMachine::new(config);
    machine.clock.tick = 1;
    machine.next_authority_witness_id = u64::MAX;
    let error = machine
        .ingest_topology_events(&SortedTimeoutCapacityHandler)
        .unwrap_err();
    let ProtocolMachineError::HandlerError(failure) = error else {
        panic!("expected original timeout-capacity failure");
    };
    assert_eq!(
        failure,
        EffectFailure::contract_violation("timeout witness counter exhausted")
    );
    assert!(machine.crashed_sites.is_empty());
    assert!(machine.timed_out_sites.is_empty());
    assert!(machine.authority_audit_log.as_slice().is_empty());
    assert_eq!(machine.next_authority_witness_id, u64::MAX);
    // The host's already-returned batch observation is retained; exhaustion
    // does not pretend the callback was never invoked or roll its cause back.
    let exchanges = machine.effect_exchanges.as_slice();
    assert_eq!(exchanges.len(), 1);
    assert_eq!(exchanges[0].request.tick, 1);
    assert_eq!(
        exchanges[0].outcome.clone().into_topology().unwrap(),
        EffectResult::success(expected)
    );
    assert!(!machine
        .obs_trace
        .as_slice()
        .iter()
        .any(|event| matches!(event, ObsEvent::TimeoutIssued { .. })));
}

fn sorted_timeout_capacity_events() -> Vec<TopologyPerturbation> {
    vec![
        TopologyPerturbation::Crash { site: "A".into() },
        TopologyPerturbation::Timeout {
            site: "B".into(),
            duration: Duration::from_millis(1),
        },
    ]
}

struct SortedTimeoutCapacityHandler;

impl EffectHandler for SortedTimeoutCapacityHandler {
    fn handle_send(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        state: &[Value],
    ) -> EffectResult<Value> {
        UnsortedTopologyHandler.handle_send(role, partner, label, state)
    }

    fn handle_recv(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        state: &mut Vec<Value>,
        payload: &Value,
    ) -> EffectResult<()> {
        UnsortedTopologyHandler.handle_recv(role, partner, label, state, payload)
    }

    fn handle_choose(
        &self,
        role: &str,
        partner: &str,
        labels: &[String],
        state: &[Value],
    ) -> EffectResult<String> {
        UnsortedTopologyHandler.handle_choose(role, partner, labels, state)
    }

    fn step(&self, role: &str, state: &mut Vec<Value>) -> EffectResult<()> {
        UnsortedTopologyHandler.step(role, state)
    }

    fn topology_events(&self, tick: u64) -> EffectResult<Vec<TopologyPerturbation>> {
        EffectResult::success(if tick == 1 {
            sorted_timeout_capacity_events()
        } else {
            Vec::new()
        })
    }
}
