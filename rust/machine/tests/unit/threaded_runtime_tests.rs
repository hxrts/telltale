// Threaded runtime partitioning and step-contract tests.

use super::*;
use crate::buffer::BufferConfig;
use crate::communication_replay::{CommunicationReplayMode, DefaultCommunicationConsumption};
use crate::coroutine::KnowledgeFact;
use crate::effect::{EffectFailure, EffectHandler, EffectResult, SendDecision, SendDecisionInput};
use crate::engine::{FlowPolicy, FlowPredicate};
use crate::verification::{Hash, Signature, VerifyingKey};
use std::collections::{BTreeMap, BTreeSet};
use telltale_types::{GlobalType, Label, LocalTypeR};

#[derive(Debug, Clone, Copy)]
struct NoopHandler;

impl EffectHandler for NoopHandler {
    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &[Value],
    ) -> EffectResult<Value> {
        EffectResult::success(Value::Unit)
    }

    fn send_decision(&self, input: SendDecisionInput<'_>) -> EffectResult<SendDecision> {
        EffectResult::success(SendDecision::Deliver(input.payload.unwrap_or(Value::Unit)))
    }

    fn handle_recv(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &mut Vec<Value>,
        _payload: &Value,
    ) -> EffectResult<()> {
        EffectResult::success(())
    }

    fn handle_choose(
        &self,
        _role: &str,
        _partner: &str,
        labels: &[String],
        _state: &[Value],
    ) -> EffectResult<String> {
        match labels.first().cloned() {
            Some(label) => EffectResult::success(label),
            None => EffectResult::failure(EffectFailure::invalid_input("no labels available")),
        }
    }

    fn step(&self, _role: &str, _state: &mut Vec<Value>) -> EffectResult<()> {
        EffectResult::success(())
    }
}

fn evaluate_check(policy: FlowPolicy, known_fact: &str, query_fact: &str, target: &str) -> bool {
    let mut coro = Coroutine::new(0, 0, 1, "A".to_string(), 8, usize::MAX);
    let ep = Endpoint {
        sid: 1,
        role: "A".to_string(),
    };
    coro.knowledge_set.push(crate::coroutine::KnowledgeFact {
        endpoint: ep.clone(),
        fact: known_fact.to_string(),
    });
    coro.regs[2] = Value::Prod(
        Box::new(Value::Endpoint(ep)),
        Box::new(Value::Str(query_fact.to_string())),
    );
    coro.regs[3] = Value::Str(target.to_string());

    let cfg = ProtocolMachineConfig {
        flow_policy: policy,
        ..ProtocolMachineConfig::default()
    };
    let pack = step_check(&mut coro, &cfg, "A", 2, 3, 4, 0).expect("check should execute");
    match pack.coro_update {
        CoroUpdate::AdvancePcWriteReg { val, .. } => matches!(val, Value::Bool(true)),
        _ => panic!("unexpected check update"),
    }
}

#[test]
fn flow_policy_variant_matrix_for_threaded_check() {
    let mut allow_roles = BTreeSet::new();
    allow_roles.insert("Observer".to_string());

    let mut deny_roles = BTreeSet::new();
    deny_roles.insert("Observer".to_string());

    assert!(evaluate_check(
        FlowPolicy::AllowAll,
        "secret",
        "secret",
        "Observer"
    ));
    assert!(!evaluate_check(
        FlowPolicy::DenyAll,
        "secret",
        "secret",
        "Observer"
    ));
    assert!(evaluate_check(
        FlowPolicy::AllowRoles(allow_roles),
        "secret",
        "secret",
        "Observer"
    ));
    assert!(!evaluate_check(
        FlowPolicy::DenyRoles(deny_roles),
        "secret",
        "secret",
        "Observer"
    ));
    assert!(evaluate_check(
        FlowPolicy::PredicateExpr(FlowPredicate::FactContains("secret".to_string())),
        "top_secret",
        "top_secret",
        "Observer"
    ));
    assert!(evaluate_check(
        FlowPolicy::predicate(|knowledge: &KnowledgeFact, target: &str| {
            knowledge.fact.contains("secret") && target == "Observer"
        }),
        "top_secret",
        "top_secret",
        "Observer"
    ));
    let mut allow_only_observer = BTreeSet::new();
    allow_only_observer.insert("Observer".to_string());
    assert!(!evaluate_check(
        FlowPolicy::AllowRoles(allow_only_observer),
        "secret",
        "secret",
        "Blocked"
    ));
}

#[test]
fn threaded_open_uses_configured_buffer_capacity() {
    let mut coro = Coroutine::new(0, 0, 0, "A".to_string(), 8, usize::MAX);
    let store = ThreadedSessionStore::new();
    let handlers = vec![(("A".to_string(), "B".to_string()), "hAB".to_string())];
    let cfg = BufferConfig {
        mode: crate::buffer::BufferMode::Fifo,
        initial_capacity: 1,
        policy: crate::buffer::BackpressurePolicy::Error,
    };
    let pack = step_open(
        &mut coro,
        "A",
        &store,
        &cfg,
        &["A".to_string(), "B".to_string()],
        &[
            (
                "A".to_string(),
                LocalTypeR::send("B", Label::new("m"), LocalTypeR::End),
            ),
            (
                "B".to_string(),
                LocalTypeR::recv("A", Label::new("m"), LocalTypeR::End),
            ),
        ],
        &handlers,
        &[("A".to_string(), 1), ("B".to_string(), 2)],
        1,
    )
    .expect("open should succeed");
    let sid = match pack.events.first() {
        Some(ObsEvent::Opened { session, .. }) => *session,
        other => panic!("expected opened event, got {other:?}"),
    };
    let session = store.get(sid).expect("session exists");
    let guard = session.lock().expect("session lock poisoned");
    for buffer in guard.buffers.values() {
        assert_eq!(buffer.capacity(), 1);
    }
}

#[test]
fn threaded_run_reports_max_rounds_exhaustion_status() {
    let image = CodeImage {
        programs: {
            let mut m = BTreeMap::new();
            m.insert("A".to_string(), vec![Instr::Jump { target: 0 }]);
            m
        },
        global_type: GlobalType::End,
        local_types: {
            let mut m = BTreeMap::new();
            m.insert("A".to_string(), LocalTypeR::End);
            m
        },
    };
    let mut machine = ThreadedProtocolMachine::with_workers(ProtocolMachineConfig::default(), 1);
    machine
        .load_choreography(&image)
        .expect("load choreography");
    let status = machine
        .run(&NoopHandler, 8)
        .expect("run should return bounded status");
    assert_eq!(status, RunStatus::MaxRoundsExceeded);
}

#[test]
fn try_with_workers_rejects_invalid_config_without_panicking() {
    let config = ProtocolMachineConfig {
        num_registers: 0,
        ..ProtocolMachineConfig::default()
    };
    let result = ThreadedProtocolMachine::try_with_workers(config, 1);
    assert!(matches!(
        result,
        Err(ProtocolMachineError::InvalidConfig { .. })
    ));
}

#[test]
fn threaded_replay_accessors_fail_fast_on_poisoned_locks() {
    let machine = ThreadedProtocolMachine::with_workers(ProtocolMachineConfig::default(), 1);
    let replay = machine.communication_consumption.clone();
    let artifacts = machine.communication_consumption_artifacts.clone();

    let replay_poison = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _guard = replay.lock().expect("acquire replay lock");
        panic!("poison replay lock");
    }));
    assert!(replay_poison.is_err(), "poison setup should panic");

    let artifact_poison = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _guard = artifacts.lock().expect("acquire artifact lock");
        panic!("poison artifact lock");
    }));
    assert!(artifact_poison.is_err(), "poison setup should panic");

    let root_access = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _ignored = machine.communication_replay_root();
    }));
    assert!(
        root_access.is_err(),
        "replay-root accessor should fail fast after poison"
    );

    let artifacts_access = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _ignored = machine.communication_consumption_artifacts();
    }));
    assert!(
        artifacts_access.is_err(),
        "artifact accessor should fail fast after poison"
    );
}

#[test]
fn threaded_recv_reports_verification_fault_for_tampered_signature() {
    let mut local_types = BTreeMap::new();
    local_types.insert(
        "A".to_string(),
        LocalTypeR::send("B", Label::new("m"), LocalTypeR::End),
    );
    local_types.insert(
        "B".to_string(),
        LocalTypeR::recv("A", Label::new("m"), LocalTypeR::End),
    );

    let store = ThreadedSessionStore::new();
    let sid = store.open(
        vec!["A".to_string(), "B".to_string()],
        &BufferConfig::default(),
        &local_types,
    );
    {
        let session = store.get(sid).expect("session exists");
        let mut session = session.lock().expect("session lock poisoned");
        let tampered = crate::buffer::SignedValue {
            payload: Value::Nat(9),
            signature: Signature {
                signer: VerifyingKey([0_u8; 32]),
                digest: Hash([7_u8; 32]),
            },
            sequence_no: 0,
        };
        session
            .send_signed("A", "B", &tampered)
            .expect("inject signed payload");
    }
    let session = store.get(sid).expect("session exists");

    let mut coro = Coroutine::new(0, 0, sid, "B".to_string(), 8, usize::MAX);
    let endpoint = Endpoint {
        sid,
        role: "B".to_string(),
    };
    coro.owned_endpoints.push(endpoint.clone());
    coro.regs[0] = Value::Endpoint(endpoint);

    let config = ProtocolMachineConfig::default();
    let guard_resources = Arc::new(Mutex::new(BTreeMap::new()));
    let resource_states = Arc::new(Mutex::new(BTreeMap::new()));
    let communication_consumption = Arc::new(Mutex::new(DefaultCommunicationConsumption::new(
        CommunicationReplayMode::Off,
    )));
    let communication_consumption_artifacts = Arc::new(Mutex::new(Vec::new()));
    let crashed_sites = BTreeSet::new();
    let partitioned_edges = BTreeSet::new();
    let corrupted_edges = BTreeMap::new();
    let timed_out_sites = BTreeMap::new();
    let step_ctx = ThreadedStepCtx {
        config: &config,
        guard_resources: &guard_resources,
        resource_states: &resource_states,
        communication_consumption: &communication_consumption,
        communication_consumption_artifacts: &communication_consumption_artifacts,
        crashed_sites: &crashed_sites,
        partitioned_edges: &partitioned_edges,
        corrupted_edges: &corrupted_edges,
        timed_out_sites: &timed_out_sites,
        handler: &NoopHandler,
        tick: 1,
        nominal_publication_admitted: true,
    };
    let err = match step_recv(&mut coro, &session, "B", 0, 1, &step_ctx) {
        Ok(_) => panic!("tampered signature must fault"),
        Err(err) => err,
    };
    assert!(matches!(err.fault, Fault::VerificationFailed { .. }));
}

#[test]
fn delegation_handoff_guard_rejects_ambiguous_endpoint_ownership() {
    let mut local_types = BTreeMap::new();
    local_types.insert(
        "A".to_string(),
        LocalTypeR::send("B", Label::new("m"), LocalTypeR::End),
    );
    local_types.insert(
        "B".to_string(),
        LocalTypeR::recv("A", Label::new("m"), LocalTypeR::End),
    );
    let global = GlobalType::send("A", "B", Label::new("m"), GlobalType::End);
    let image = CodeImage::from_local_types(&local_types, &global);

    let mut machine = ThreadedProtocolMachine::with_workers(ProtocolMachineConfig::default(), 2);
    let sid = machine
        .load_choreography(&image)
        .expect("load choreography");
    let endpoint = Endpoint {
        sid,
        role: "A".to_string(),
    };

    let mut source = None;
    let mut target = None;
    for coro in &machine.coroutines {
        let guard = coro.lock().expect("coroutine lock poisoned");
        if guard.role == "A" {
            source = Some(guard.id);
        } else if guard.role == "B" {
            target = Some(guard.id);
        }
    }
    let source = source.expect("source coroutine");
    let target = target.expect("target coroutine");
    {
        let target_arc = machine
            .coroutines
            .get(target)
            .cloned()
            .expect("target coroutine arc");
        let mut target_guard = target_arc.lock().expect("coroutine lock poisoned");
        target_guard.owned_endpoints.push(endpoint.clone());
    }

    let err = machine
        .enqueue_handoff(endpoint, source, target, machine.clock.tick)
        .expect_err("ambiguous ownership must fail");
    match err {
        Fault::Transfer { message } => {
            assert!(
                message.contains("delegation guard violation"),
                "unexpected transfer fault message: {message}"
            );
        }
        other => panic!("expected transfer fault, got {other:?}"),
    }
}

#[test]
fn delegation_handoff_emits_endpoint_scoped_receipt() {
    let mut local_types = BTreeMap::new();
    local_types.insert(
        "A".to_string(),
        LocalTypeR::send("B", Label::new("m"), LocalTypeR::End),
    );
    local_types.insert(
        "B".to_string(),
        LocalTypeR::recv("A", Label::new("m"), LocalTypeR::End),
    );
    let global = GlobalType::send("A", "B", Label::new("m"), GlobalType::End);
    let image = CodeImage::from_local_types(&local_types, &global);

    let mut machine = ThreadedProtocolMachine::with_workers(ProtocolMachineConfig::default(), 2);
    let sid = machine
        .load_choreography(&image)
        .expect("load choreography");
    let endpoint = Endpoint {
        sid,
        role: "A".to_string(),
    };

    let mut source = None;
    let mut target = None;
    for coro in &machine.coroutines {
        let guard = coro.lock().expect("coroutine lock poisoned");
        if guard.role == "A" {
            source = Some(guard.id);
        } else if guard.role == "B" {
            target = Some(guard.id);
        }
    }
    let source = source.expect("source coroutine");
    let target = target.expect("target coroutine");

    machine
        .enqueue_handoff(endpoint.clone(), source, target, machine.clock.tick)
        .expect("enqueue handoff");
    let receipt = &machine
        .handoff_trace()
        .last()
        .expect("handoff trace")
        .receipt;
    assert_eq!(receipt.endpoint, endpoint);
    assert_eq!(receipt.from_coro, source);
    assert_eq!(receipt.to_coro, target);
    assert_eq!(
        receipt.scope,
        OwnershipScope::Fragments(BTreeSet::from(["A".to_string()]))
    );
}

#[test]
fn delegation_handoff_rollback_restores_source_when_apply_fails() {
    let mut local_types = BTreeMap::new();
    local_types.insert(
        "A".to_string(),
        LocalTypeR::send("B", Label::new("m"), LocalTypeR::End),
    );
    local_types.insert(
        "B".to_string(),
        LocalTypeR::recv("A", Label::new("m"), LocalTypeR::End),
    );
    local_types.insert("C".to_string(), LocalTypeR::End);
    let global = GlobalType::send("A", "B", Label::new("m"), GlobalType::End);
    let image = CodeImage::from_local_types(&local_types, &global);

    let mut machine = ThreadedProtocolMachine::with_workers(ProtocolMachineConfig::default(), 3);
    let sid = machine
        .load_choreography(&image)
        .expect("load choreography");
    let endpoint = Endpoint {
        sid,
        role: "A".to_string(),
    };

    let mut source = None;
    let mut target = None;
    let mut third = None;
    for coro in &machine.coroutines {
        let guard = coro.lock().expect("coroutine lock poisoned");
        match guard.role.as_str() {
            "A" => source = Some(guard.id),
            "B" => target = Some(guard.id),
            "C" => third = Some(guard.id),
            _ => {}
        }
    }
    let source = source.expect("source coroutine");
    let target = target.expect("target coroutine");
    let third = third.expect("third coroutine");

    machine
        .enqueue_handoff(endpoint.clone(), source, target, machine.clock.tick)
        .expect("enqueue handoff");

    {
        let third_arc = machine
            .coroutines
            .get(third)
            .cloned()
            .expect("third coroutine arc");
        let mut third_guard = third_arc.lock().expect("coroutine lock poisoned");
        third_guard.owned_endpoints.push(endpoint.clone());
    }

    let err = machine
        .apply_handoffs_deterministically()
        .expect_err("corrupted handoff apply must fail");
    match err {
        Fault::Transfer { message } => {
            assert!(
                message.contains("delegation guard violation"),
                "unexpected transfer fault message: {message}"
            );
        }
        other => panic!("expected transfer fault, got {other:?}"),
    }

    let source_guard = machine.coroutines[source]
        .lock()
        .expect("source coroutine lock poisoned");
    let target_guard = machine.coroutines[target]
        .lock()
        .expect("target coroutine lock poisoned");
    assert!(
        source_guard.owned_endpoints.contains(&endpoint),
        "rollback must restore source ownership"
    );
    assert!(
        !target_guard.owned_endpoints.contains(&endpoint),
        "rollback must remove any staged target ownership"
    );
    let audit = machine
        .delegation_audit_log()
        .last()
        .expect("rollback should be audited");
    assert_eq!(audit.status, DelegationStatus::RolledBack);
    assert!(audit
        .reason
        .as_ref()
        .is_some_and(|r| r.contains("delegation guard violation")));
}

#[test]
#[allow(clippy::too_many_lines)]
fn delegation_handoff_rebinds_pending_effects_and_invalidates_blocked_effects() {
    let mut local_types = BTreeMap::new();
    local_types.insert(
        "A".to_string(),
        LocalTypeR::send("B", Label::new("m"), LocalTypeR::End),
    );
    local_types.insert(
        "B".to_string(),
        LocalTypeR::recv("A", Label::new("m"), LocalTypeR::End),
    );
    let global = GlobalType::send("A", "B", Label::new("m"), GlobalType::End);
    let image = CodeImage::from_local_types(&local_types, &global);

    let mut machine = ThreadedProtocolMachine::with_workers(ProtocolMachineConfig::default(), 2);
    let sid = machine
        .load_choreography(&image)
        .expect("load choreography");
    let endpoint = Endpoint {
        sid,
        role: "A".to_string(),
    };

    let mut source = None;
    let mut target = None;
    for coro in &machine.coroutines {
        let guard = coro.lock().expect("coroutine lock poisoned");
        if guard.role == "A" {
            source = Some(guard.id);
        } else if guard.role == "B" {
            target = Some(guard.id);
        }
    }
    let source = source.expect("source coroutine");
    let target = target.expect("target coroutine");

    machine.outstanding_effects.push(OutstandingEffect {
        effect_id: 11,
        operation_id: "effect:11".to_string(),
        session: Some(sid),
        owner_id: Some("coro:0".to_string()),
        effect_interface: Some("Runtime".to_string()),
        effect_operation: Some("invoke".to_string()),
        effect_kind: "invoke_step".to_string(),
        handler_identity: "host/runtime".to_string(),
        status: OutstandingEffectStatus::Pending,
        ordering_key: 1,
        budget_ticks: Some(1),
        retry_policy: "forbid_late_results".to_string(),
        invalidation_token: "effect:11:live".to_string(),
        completed_at_tick: None,
        inputs: serde_json::json!({ "session": sid }),
        outputs: serde_json::json!({ "status": "pending" }),
    });
    machine.outstanding_effects.push(OutstandingEffect {
        effect_id: 12,
        operation_id: "effect:12".to_string(),
        session: Some(sid),
        owner_id: Some("coro:0".to_string()),
        effect_interface: Some("Runtime".to_string()),
        effect_operation: Some("receive".to_string()),
        effect_kind: "handle_recv".to_string(),
        handler_identity: "host/runtime".to_string(),
        status: OutstandingEffectStatus::Blocked,
        ordering_key: 2,
        budget_ticks: Some(1),
        retry_policy: "forbid_late_results".to_string(),
        invalidation_token: "effect:12:live".to_string(),
        completed_at_tick: None,
        inputs: serde_json::json!({ "session": sid }),
        outputs: serde_json::json!({ "status": "blocked" }),
    });
    machine.operation_instances.push(OperationInstance {
        agreement_profile: None,
        operation_id: "effect:11".to_string(),
        session: Some(sid),
        owner_id: Some("coro:0".to_string()),
        kind: "invoke".to_string(),
        phase: OperationPhase::Pending,
        handler_identity: Some("host/runtime".to_string()),
        effect_ids: vec![11],
        dependent_operation_ids: Vec::new(),
        terminal_publication: None,
        budget_ticks: Some(1),
        requires_proof: false,
    });
    machine.operation_instances.push(OperationInstance {
        agreement_profile: None,
        operation_id: "effect:12".to_string(),
        session: Some(sid),
        owner_id: Some("coro:0".to_string()),
        kind: "receive".to_string(),
        phase: OperationPhase::Blocked,
        handler_identity: Some("host/runtime".to_string()),
        effect_ids: vec![12],
        dependent_operation_ids: Vec::new(),
        terminal_publication: Some("effect.blocked".to_string()),
        budget_ticks: Some(1),
        requires_proof: false,
    });

    machine
        .enqueue_handoff(endpoint, source, target, machine.clock.tick)
        .expect("enqueue handoff");
    machine
        .apply_handoffs_deterministically()
        .expect("apply handoff");

    let pending = machine
        .outstanding_effects
        .iter()
        .find(|effect| effect.effect_id == 11)
        .expect("pending effect");
    assert_eq!(pending.owner_id.as_deref(), Some("coro:1"));
    assert_eq!(pending.status, OutstandingEffectStatus::Pending);

    let blocked = machine
        .outstanding_effects
        .iter()
        .find(|effect| effect.effect_id == 12)
        .expect("blocked effect");
    assert_eq!(blocked.owner_id.as_deref(), Some("coro:1"));
    assert_eq!(blocked.status, OutstandingEffectStatus::Invalidated);
}

#[test]
fn progress_contracts_escalate_consistently_in_threaded_runtime() {
    let mut machine = ThreadedProtocolMachine::with_workers(ProtocolMachineConfig::default(), 2);
    machine.clock.tick = 1;
    let effect_id = machine
        .issue_runtime_effect(
            "invoke_step",
            Some(7),
            "host/runtime",
            serde_json::json!({ "session": 7 }),
        )
        .expect("unit fixture has fresh occurrence capacity");

    machine.clock.tick = 2;
    machine
        .evaluate_progress_contracts()
        .expect("blocked escalation should succeed");
    assert_eq!(
        machine
            .progress_contracts
            .iter()
            .find(|contract| contract.operation_id == format!("effect:{effect_id}"))
            .expect("progress contract")
            .state,
        ProgressState::Blocked
    );

    machine.clock.tick = 3;
    machine
        .evaluate_progress_contracts()
        .expect("no-progress escalation should succeed");
    assert_eq!(
        machine
            .progress_contracts
            .iter()
            .find(|contract| contract.operation_id == format!("effect:{effect_id}"))
            .expect("progress contract")
            .state,
        ProgressState::NoProgress
    );

    machine.clock.tick = 4;
    machine
        .evaluate_progress_contracts()
        .expect("degraded escalation should succeed");
    assert_eq!(
        machine
            .progress_contracts
            .iter()
            .find(|contract| contract.operation_id == format!("effect:{effect_id}"))
            .expect("progress contract")
            .state,
        ProgressState::Degraded
    );

    machine.clock.tick = 5;
    machine
        .evaluate_progress_contracts()
        .expect("timeout escalation should succeed");
    assert_eq!(
        machine
            .progress_contracts
            .iter()
            .find(|contract| contract.operation_id == format!("effect:{effect_id}"))
            .expect("progress contract")
            .state,
        ProgressState::TimedOut
    );
    let err = machine
        .complete_runtime_effect(
            effect_id,
            OutstandingEffectStatus::Succeeded,
            serde_json::json!({ "status": "success" }),
        )
        .expect_err("late timeout result must be rejected");
    assert!(err.to_string().contains("late result"));
}

fn lifecycle_loop_image(invoke: bool) -> CodeImage {
    let instructions = if invoke {
        vec![
            Instr::Invoke {
                action: crate::instr::InvokeAction::Named("step".into()),
            },
            Instr::Jump { target: 0 },
        ]
    } else {
        vec![Instr::Jump { target: 0 }]
    };
    CodeImage {
        programs: BTreeMap::from([("A".into(), instructions)]),
        global_type: GlobalType::End,
        local_types: BTreeMap::from([("A".into(), LocalTypeR::End)]),
    }
}

#[test]
fn required_threaded_reap_preserves_other_sessions_and_stable_ids() {
    let mut machine = ThreadedProtocolMachine::with_workers(ProtocolMachineConfig::default(), 2);
    let image = lifecycle_loop_image(false);
    let first = machine
        .load_choreography(&image)
        .expect("first actual session");
    let second = machine
        .load_choreography(&image)
        .expect("second actual session");
    let second_coro = machine.session_coroutines(second)[0].clone();
    machine
        .resource_states
        .lock()
        .expect("resource fixture")
        .insert(first, ResourceState::default());
    machine
        .resource_states
        .lock()
        .expect("resource fixture")
        .insert(second, ResourceState::default());
    let summary = machine
        .close_and_reap_session(first)
        .expect("target disposal acknowledged");
    assert_eq!(summary.sid, first);
    assert!(machine.sessions.get(first).is_none());
    assert!(machine.session_coroutines(first).is_empty());
    assert!(machine.coroutine_by_id(second_coro.id).is_some());
    assert_eq!(machine.session_coroutines(second)[0].pc, second_coro.pc);
    assert!(machine
        .resource_states
        .lock()
        .expect("resources")
        .get(&first)
        .is_none());
    assert!(machine
        .resource_states
        .lock()
        .expect("resources")
        .get(&second)
        .is_some());
    machine
        .step_round(&NoopHandler, 1)
        .expect("surviving session dispatches after compaction");
    let third = machine
        .load_choreography(&image)
        .expect("new session after reap");
    let third_coro = machine.session_coroutines(third)[0].id;
    assert!(third_coro > second_coro.id);
    machine
        .step_round(&NoopHandler, 2)
        .expect("both stable ids dispatch");
    assert_eq!(
        machine
            .close_and_reap_session(first)
            .expect("idempotent archived acknowledgment"),
        summary
    );
    assert_eq!(machine.sessions.active_count(), 2);
}

#[test]
fn required_threaded_reap_rejects_epoch_and_index_faults_before_mutation() {
    let mut machine = ThreadedProtocolMachine::with_workers(ProtocolMachineConfig::default(), 1);
    let sid = machine
        .load_choreography(&lifecycle_loop_image(false))
        .expect("real session");
    machine
        .sessions
        .get(sid)
        .expect("session")
        .lock()
        .expect("session lock")
        .epoch = usize::MAX;
    assert!(
        matches!(machine.close_and_reap_session(sid), Err(ThreadedSessionLifecycleError::EpochExhausted { session }) if session == sid)
    );
    assert_eq!(
        machine
            .sessions
            .get(sid)
            .expect("not removed")
            .lock()
            .expect("session")
            .status,
        SessionStatus::Active
    );
    machine
        .sessions
        .get(sid)
        .expect("session")
        .lock()
        .expect("session lock")
        .epoch = 0;
    let coro = machine.session_coroutines(sid)[0].id;
    machine.coroutine_indexes.insert(coro, usize::MAX);
    assert!(
        matches!(machine.close_and_reap_session(sid), Err(ThreadedSessionLifecycleError::InvalidCoroutineIndex { coroutine }) if coroutine == coro)
    );
    assert!(machine.sessions.get(sid).is_some());
    assert!(machine.reaped_sessions.is_empty());
}

#[test]
fn required_threaded_reap_preserves_actual_poison_failure() {
    let mut machine = ThreadedProtocolMachine::with_workers(ProtocolMachineConfig::default(), 1);
    let sid = machine
        .load_choreography(&lifecycle_loop_image(false))
        .expect("real session");
    let target = machine.coroutines[0].clone();
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _guard = target.lock().expect("initial unpoisoned fixture");
        panic!("injected actual coroutine lock poison");
    }));
    assert!(result.is_err());
    let error = machine
        .close_and_reap_session(sid)
        .expect_err("required lock failure cannot acknowledge reap");
    assert!(matches!(
        error,
        ThreadedSessionLifecycleError::LockPoisoned {
            component: "coroutine"
        }
    ));
    assert!(machine.sessions.get(sid).is_some());
    assert!(machine.reaped_sessions.is_empty());
}

struct LifecycleBlockingHandler {
    target: SessionId,
    first: std::sync::atomic::AtomicBool,
    calls: std::sync::atomic::AtomicUsize,
    entered: std::sync::mpsc::SyncSender<()>,
    released: Arc<std::sync::Barrier>,
}
impl EffectHandler for LifecycleBlockingHandler {
    fn handle_effect(&self, request: EffectRequest) -> EffectOutcome {
        if request.session == Some(self.target) {
            self.calls.fetch_add(1, Ordering::SeqCst);
            if self.first.swap(false, Ordering::SeqCst) {
                self.entered
                    .send(())
                    .expect("test observes actual worker entry");
                self.released.wait();
            }
        }
        NoopHandler.handle_effect(request)
    }
    fn handle_send(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        state: &[Value],
    ) -> EffectResult<Value> {
        NoopHandler.handle_send(role, partner, label, state)
    }
    fn handle_recv(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        state: &mut Vec<Value>,
        payload: &Value,
    ) -> EffectResult<()> {
        NoopHandler.handle_recv(role, partner, label, state, payload)
    }
    fn handle_choose(
        &self,
        role: &str,
        partner: &str,
        labels: &[String],
        state: &[Value],
    ) -> EffectResult<String> {
        NoopHandler.handle_choose(role, partner, labels, state)
    }
    fn step(&self, role: &str, state: &mut Vec<Value>) -> EffectResult<()> {
        NoopHandler.step(role, state)
    }
}
#[test]
fn required_threaded_reap_acknowledges_completed_worker_scope() {
    use std::sync::{
        atomic::{AtomicBool, AtomicUsize, Ordering},
        mpsc, Barrier,
    };
    let mut machine = ThreadedProtocolMachine::with_workers(ProtocolMachineConfig::default(), 2);
    let image = lifecycle_loop_image(true);
    let first = machine
        .load_choreography(&image)
        .expect("target actual session");
    let second = machine
        .load_choreography(&image)
        .expect("surviving actual session");
    let (entered_tx, entered_rx) = mpsc::sync_channel(1);
    let (close_tx, close_rx) = mpsc::sync_channel(1);
    let (ack_tx, ack_rx) = mpsc::sync_channel(1);
    let released = Arc::new(Barrier::new(2));
    let handler = LifecycleBlockingHandler {
        target: first,
        first: AtomicBool::new(true),
        calls: AtomicUsize::new(0),
        entered: entered_tx,
        released: released.clone(),
    };
    std::thread::scope(|scope| {
        let owner = scope.spawn(move || {
            machine
                .step_round(&handler, 2)
                .expect("scoped worker round completes");
            close_rx.recv().expect("owned disposal command");
            let summary = machine
                .close_and_reap_session(first)
                .expect("required acknowledgment after worker scope");
            let at_ack = handler.calls.load(Ordering::SeqCst);
            ack_tx
                .send(summary)
                .expect("actual acknowledgment observer");
            machine
                .step_round(&handler, 1)
                .expect("surviving session continues");
            machine
                .step_round(&handler, 1)
                .expect("surviving invoke continues");
            assert_eq!(
                handler.calls.load(Ordering::SeqCst),
                at_ack,
                "target cannot execute after acknowledgment"
            );
            assert!(machine.sessions.get(second).is_some());
        });
        entered_rx
            .recv()
            .expect("actual target worker has entered handler");
        close_tx
            .send(())
            .expect("request target disposal while worker is blocked");
        assert!(
            matches!(ack_rx.try_recv(), Err(mpsc::TryRecvError::Empty)),
            "no acknowledgment before actual worker completion"
        );
        released.wait();
        assert_eq!(
            ack_rx.recv().expect("owned close acknowledgment").sid,
            first
        );
        owner.join().expect("all test-owned threads joined");
    });
}

#[test]
fn required_threaded_reap_preserves_natural_terminal_epoch() {
    let mut image = CodeImage::from_local_types(
        &BTreeMap::from([("A".into(), LocalTypeR::End)]),
        &GlobalType::End,
    );
    image
        .programs
        .insert("A".into(), vec![Instr::Close { session: 0 }, Instr::Halt]);
    let mut machine = ThreadedProtocolMachine::with_workers(ProtocolMachineConfig::default(), 2);
    let sid = machine
        .load_choreography(&image)
        .expect("actual natural completion session");
    machine
        .run(&NoopHandler, 8)
        .expect("actual protocol close and halt");
    let target = machine
        .sessions
        .get(sid)
        .expect("natural close retained until disposal");
    let epoch = target.lock().expect("actual naturally closed state").epoch;
    assert_eq!(
        target.lock().expect("actual terminal status").status,
        SessionStatus::Closed
    );
    let summary = machine
        .close_and_reap_session(sid)
        .expect("acknowledged naturally closed disposal");
    assert_eq!(summary.epoch, epoch);
    assert_eq!(
        machine
            .close_and_reap_session(sid)
            .expect("repeated actual acknowledgment"),
        summary
    );
    assert!(machine.sessions.get(sid).is_none());
}

#[test]
fn required_disposal_cooperative_threaded_summaries_match() {
    let image = lifecycle_loop_image(false);
    let mut cooperative = crate::engine::ProtocolMachine::new(ProtocolMachineConfig::default());
    let mut threaded = ThreadedProtocolMachine::with_workers(ProtocolMachineConfig::default(), 2);
    let cooperative_target = cooperative
        .load_choreography(&image)
        .expect("cooperative target");
    let threaded_target = threaded.load_choreography(&image).expect("threaded target");
    let cooperative_survivor = cooperative
        .load_choreography(&image)
        .expect("cooperative survivor");
    let threaded_survivor = threaded
        .load_choreography(&image)
        .expect("threaded survivor");
    let cooperative_ack = cooperative
        .close_and_reap_session(cooperative_target)
        .expect("cooperative required acknowledgment");
    let threaded_ack = threaded
        .close_and_reap_session(threaded_target)
        .expect("threaded required acknowledgment");
    assert_eq!(
        cooperative_ack, threaded_ack,
        "same initial state has the same terminal summary"
    );
    assert!(cooperative.sessions().get(cooperative_target).is_none());
    assert!(threaded.sessions.get(threaded_target).is_none());
    cooperative
        .step_round(&NoopHandler, 1)
        .expect("cooperative surviving stable id dispatches");
    threaded
        .step_round(&NoopHandler, 1)
        .expect("threaded surviving stable id dispatches");
    assert!(cooperative.sessions().get(cooperative_survivor).is_some());
    assert!(threaded.sessions.get(threaded_survivor).is_some());
    assert_eq!(
        cooperative
            .close_and_reap_session(cooperative_target)
            .expect("cooperative repeated acknowledgment"),
        cooperative_ack
    );
    assert_eq!(
        threaded
            .close_and_reap_session(threaded_target)
            .expect("threaded repeated acknowledgment"),
        threaded_ack
    );
}

// Actual native multi-pick regression; outcomes are retained in checkpoint receipts.
// Exercises actual two-pick native dispatch, not arbitrary injected Result values.
#[cfg(not(target_arch = "wasm32"))]
#[test]
fn returned_wave_preserves_later_fault_after_original_failure() {
    let mut machine = ThreadedProtocolMachine::with_workers(ProtocolMachineConfig::default(), 2);
    assert!(machine.config.instruction_cost > 0);
    let image = lifecycle_loop_image(false);
    let first_sid = machine
        .load_choreography(&image)
        .expect("first actual session");
    let second_sid = machine
        .load_choreography(&image)
        .expect("second actual session");
    let first = machine
        .coroutines
        .iter()
        .find(|original| original.lock().expect("resident coroutine").session_id == first_sid)
        .cloned()
        .expect("first resident coroutine handle");
    let second = machine
        .coroutines
        .iter()
        .find(|original| original.lock().expect("resident coroutine").session_id == second_sid)
        .cloned()
        .expect("second resident coroutine handle");
    let first_id = {
        let mut coro = first.lock().expect("first original coroutine");
        coro.pc = usize::MAX;
        coro.id
    };
    let second_id = {
        let mut coro = second.lock().expect("second original coroutine");
        coro.cost_budget = 0;
        coro.id
    };
    let tick = machine.clock.tick;
    let picks = vec![
        Picked {
            coro_id: first_id,
            sid: first_sid,
            lane: 0,
            coro: first,
            session: machine
                .sessions
                .get(first_sid)
                .expect("first resident session"),
        },
        Picked {
            coro_id: second_id,
            sid: second_sid,
            lane: 1,
            coro: second,
            session: machine
                .sessions
                .get(second_sid)
                .expect("second resident session"),
        },
    ];
    let result = machine.execute_picks(picks, &NoopHandler, tick);
    let faults: Vec<_> = machine
        .trace
        .iter()
        .filter_map(|event| match event {
            ObsEvent::Faulted {
                tick,
                coro_id,
                fault,
            } => Some((*tick, *coro_id, fault.clone())),
            _ => None,
        })
        .collect();
    let clock_after = machine.clock.tick;
    // Consume actual original native worker handles before result assertions.
    let disposal = machine
        .shutdown_worker_pool()
        .expect("original worker settlement");
    assert_eq!(disposal.joined_workers(), 2);
    assert!(disposal.worker_panics().is_empty());
    assert!(matches!(result, Err(ProtocolMachineError::Fault {
        coro_id, fault: Fault::PcOutOfBounds,
    }) if coro_id == first_id));
    assert_eq!(
        clock_after, tick,
        "dispatch cannot invent another scheduler tick"
    );
    assert_eq!(
        faults,
        vec![
            (tick, first_id, Fault::PcOutOfBounds),
            (tick, second_id, Fault::OutOfCredits),
        ]
    );
}

// Real native two-pick regression; checkpoint evidence records actual outcomes.
#[cfg(not(target_arch = "wasm32"))]
struct ReturnedGenericFailureHandler {
    calls: Mutex<Vec<crate::effect::EffectRequest>>,
    failure: EffectFailure,
}
#[cfg(not(target_arch = "wasm32"))]
impl EffectHandler for ReturnedGenericFailureHandler {
    fn handle_effect(&self, request: crate::effect::EffectRequest) -> crate::effect::EffectOutcome {
        use crate::effect::{EffectOutcome, EffectRequestBody};
        self.calls
            .lock()
            .expect("actual request owner")
            .push(request.clone());
        if matches!(&request.body, EffectRequestBody::InvokeStep { .. }) {
            return EffectOutcome::failure(self.failure.clone());
        }
        NoopHandler.handle_effect(request)
    }
    fn handle_send(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        state: &[Value],
    ) -> EffectResult<Value> {
        NoopHandler.handle_send(role, partner, label, state)
    }
    fn handle_recv(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        state: &mut Vec<Value>,
        payload: &Value,
    ) -> EffectResult<()> {
        NoopHandler.handle_recv(role, partner, label, state, payload)
    }
    fn handle_choose(
        &self,
        role: &str,
        partner: &str,
        labels: &[String],
        state: &[Value],
    ) -> EffectResult<String> {
        NoopHandler.handle_choose(role, partner, labels, state)
    }
    fn step(&self, role: &str, state: &mut Vec<Value>) -> EffectResult<()> {
        NoopHandler.step(role, state)
    }
    fn supports_wal_sync(&self) -> bool {
        true
    }
}
// Actual native multi-pick regression; outcomes are retained in checkpoint receipts.
// Exercises actual two-pick native dispatch, not arbitrary injected Result values.
#[cfg(not(target_arch = "wasm32"))]
#[test]
fn returned_wave_retains_independent_actual_generic_failure() {
    let mut machine = ThreadedProtocolMachine::with_workers(
        ProtocolMachineConfig {
            output_condition_policy: crate::output_condition::OutputConditionPolicy::AllowAll,
            ..ProtocolMachineConfig::default()
        },
        2,
    );
    assert!(machine.config.instruction_cost > 0);
    let image = lifecycle_loop_image(true);
    let first_sid = machine
        .load_choreography(&image)
        .expect("first actual session");
    let second_sid = machine
        .load_choreography(&image)
        .expect("second actual session");
    let first = machine
        .coroutines
        .iter()
        .find(|original| original.lock().expect("resident coroutine").session_id == first_sid)
        .cloned()
        .expect("first resident coroutine handle");
    let second = machine
        .coroutines
        .iter()
        .find(|original| original.lock().expect("resident coroutine").session_id == second_sid)
        .cloned()
        .expect("second resident coroutine handle");
    let first_id = {
        let mut coro = first.lock().expect("first original coroutine");
        coro.pc = usize::MAX;
        coro.id
    };
    let second_id = {
        let coro = second.lock().expect("second original coroutine");
        assert!(coro.cost_budget >= machine.config.instruction_cost);
        coro.id
    };
    let retained_second = second.clone();
    let original_failure = EffectFailure::denied("actual independent callback refusal");
    let handler = ReturnedGenericFailureHandler {
        calls: Mutex::new(Vec::new()),
        failure: original_failure.clone(),
    };
    let tick = machine.clock.tick;
    let picks = vec![
        Picked {
            coro_id: first_id,
            sid: first_sid,
            lane: 0,
            coro: first,
            session: machine
                .sessions
                .get(first_sid)
                .expect("first resident session"),
        },
        Picked {
            coro_id: second_id,
            sid: second_sid,
            lane: 1,
            coro: second,
            session: machine
                .sessions
                .get(second_sid)
                .expect("second resident session"),
        },
    ];
    let result = machine.execute_picks(picks, &handler, tick);
    let second_pc = retained_second
        .lock()
        .expect("actual returned coroutine")
        .pc;
    let exchanges = machine.effect_exchanges().to_vec();
    let calls = handler.calls.lock().expect("real host calls").clone();
    let faults = returned_generic_failure_faults(&machine);
    let clock_after = machine.clock.tick;
    // Consume actual original native worker handles before result assertions.
    let disposal = machine
        .shutdown_worker_pool()
        .expect("original worker settlement");
    assert_eq!(disposal.joined_workers(), 2);
    assert!(disposal.worker_panics().is_empty());
    assert!(matches!(result, Err(ProtocolMachineError::Fault {
        coro_id, fault: Fault::PcOutOfBounds,
    }) if coro_id == first_id));
    assert_eq!(
        clock_after, tick,
        "dispatch cannot invent another scheduler tick"
    );
    assert_returned_generic_failure_custody(
        &calls,
        &exchanges,
        second_sid,
        second_pc,
        &original_failure,
    );
    assert_returned_failure_order(&faults, tick, first_id, second_id, &original_failure);
}

#[cfg(not(target_arch = "wasm32"))]
fn assert_returned_generic_failure_custody(
    calls: &[crate::effect::EffectRequest],
    exchanges: &[crate::effect::EffectExchangeRecord],
    second_sid: crate::session::SessionId,
    second_pc: usize,
    original_failure: &EffectFailure,
) {
    use crate::effect::EffectRequestBody;
    assert_eq!(
        second_pc, 0,
        "later result cannot advance after primary failure"
    );
    assert_eq!(
        calls
            .iter()
            .filter(|r| matches!(&r.body, EffectRequestBody::InvokeStep { .. }))
            .count(),
        1
    );
    assert_eq!(
        calls
            .iter()
            .filter(|r| matches!(&r.body, EffectRequestBody::OutputConditionHint { .. }))
            .count(),
        0
    );
    assert_eq!(
        calls
            .iter()
            .filter(|r| matches!(&r.body, EffectRequestBody::WalSync { .. }))
            .count(),
        0,
        "retaining returned work must not run a later WAL effect"
    );
    let invocation = calls
        .iter()
        .find(|r| matches!(&r.body, EffectRequestBody::InvokeStep { .. }))
        .expect("actual callback reached before primary commit");
    assert_eq!(invocation.session, Some(second_sid));
    let retained = returned_wave_original_exchanges(exchanges, invocation);
    assert_eq!(
        retained.len(),
        1,
        "exact original callback observation reaches canonical custody once"
    );
    let outcome = retained[0]
        .outcome
        .clone()
        .into_invoke_state_for(&invocation.body);
    assert!(
        matches!(outcome, Ok(EffectResult::Failure(failure)) if &failure == original_failure),
        "retain actual typed original callback failure independently of the primary PC fault"
    );
}

#[cfg(not(target_arch = "wasm32"))]
fn assert_returned_failure_order(
    faults: &[(u64, usize, Fault)],
    tick: u64,
    first: usize,
    second: usize,
    failure: &EffectFailure,
) {
    assert_eq!(
        faults,
        &[
            (tick, first, Fault::PcOutOfBounds),
            (
                tick,
                second,
                Fault::Invoke {
                    failure: failure.clone()
                }
            )
        ]
    );
}

#[cfg(not(target_arch = "wasm32"))]
fn returned_generic_failure_faults(machine: &ThreadedProtocolMachine) -> Vec<(u64, usize, Fault)> {
    machine
        .trace
        .iter()
        .filter_map(|event| match event {
            ObsEvent::Faulted {
                tick,
                coro_id,
                fault,
            } => Some((*tick, *coro_id, fault.clone())),
            _ => None,
        })
        .collect()
}

// Real native two-pick regression; checkpoint evidence records actual outcomes.
#[cfg(not(target_arch = "wasm32"))]
struct PublicReturnedGenericHandler {
    calls: Mutex<Vec<crate::effect::EffectRequest>>,
}
#[cfg(not(target_arch = "wasm32"))]
impl EffectHandler for PublicReturnedGenericHandler {
    fn handle_effect(&self, request: crate::effect::EffectRequest) -> crate::effect::EffectOutcome {
        use crate::effect::{EffectOutcome, EffectRequestBody, EffectResponse};
        self.calls
            .lock()
            .expect("actual request owner")
            .push(request.clone());
        if let EffectRequestBody::InvokeStep { state, .. } = &request.body {
            let mut state = state.clone();
            state[0] = Value::Str("actual-later-result".into());
            return EffectOutcome::success(EffectResponse::InvokeStep { state });
        }
        if matches!(&request.body, EffectRequestBody::WalSync { .. }) {
            return EffectOutcome::success(EffectResponse::WalSync);
        }
        NoopHandler.handle_effect(request)
    }
    fn handle_send(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        state: &[Value],
    ) -> EffectResult<Value> {
        NoopHandler.handle_send(role, partner, label, state)
    }
    fn handle_recv(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        state: &mut Vec<Value>,
        payload: &Value,
    ) -> EffectResult<()> {
        NoopHandler.handle_recv(role, partner, label, state, payload)
    }
    fn handle_choose(
        &self,
        role: &str,
        partner: &str,
        labels: &[String],
        state: &[Value],
    ) -> EffectResult<String> {
        NoopHandler.handle_choose(role, partner, labels, state)
    }
    fn step(&self, role: &str, state: &mut Vec<Value>) -> EffectResult<()> {
        NoopHandler.step(role, state)
    }
    fn supports_wal_sync(&self) -> bool {
        true
    }
}
// Actual native multi-pick regression; outcomes are retained in checkpoint receipts.
// Exercises actual two-pick native dispatch, not arbitrary injected Result values.
#[cfg(not(target_arch = "wasm32"))]
#[test]
fn public_wave_retains_first_fault_and_commits_independent_valid_result() {
    let mut machine = ThreadedProtocolMachine::with_workers(
        ProtocolMachineConfig {
            threaded_round_semantics: crate::ThreadedRoundSemantics::WaveParallelExtension,
            output_condition_policy: crate::output_condition::OutputConditionPolicy::AllowAll,
            ..ProtocolMachineConfig::default()
        },
        2,
    );
    assert!(machine.config.instruction_cost > 0);
    let image = lifecycle_loop_image(true);
    let first_owner = machine
        .load_choreography_owned(&image, "actual-first-owner")
        .expect("first issued owner");
    let second_owner = machine
        .load_choreography_owned(&image, "actual-second-owner")
        .expect("second issued owner");
    let first_sid = first_owner.session_id();
    let second_sid = second_owner.session_id();
    let first = machine
        .coroutines
        .iter()
        .find(|original| original.lock().expect("resident coroutine").session_id == first_sid)
        .cloned()
        .expect("first resident coroutine handle");
    let second = machine
        .coroutines
        .iter()
        .find(|original| original.lock().expect("resident coroutine").session_id == second_sid)
        .cloned()
        .expect("second resident coroutine handle");
    let first_id = {
        let mut coro = first.lock().expect("first original coroutine");
        coro.pc = usize::MAX;
        coro.id
    };
    let second_id = {
        let coro = second.lock().expect("second original coroutine");
        assert!(coro.cost_budget >= machine.config.instruction_cost);
        coro.id
    };
    let retained_second = second.clone();
    let handler = PublicReturnedGenericHandler {
        calls: Mutex::new(Vec::new()),
    };
    let tick = machine
        .clock
        .tick
        .checked_add(1)
        .expect("original next round is representable");
    let result = machine.step_round(&handler, 2);
    let selected = machine.lane_trace().to_vec();
    let second_pc = retained_second
        .lock()
        .expect("actual returned coroutine")
        .pc;
    let exchanges = machine.effect_exchanges().to_vec();
    let calls = handler.calls.lock().expect("real host calls").clone();
    let clock_after = machine.clock.tick;
    // Consume actual original native worker handles before result assertions.
    let disposal = machine
        .shutdown_worker_pool()
        .expect("original worker settlement");
    assert_eq!(disposal.joined_workers(), 2);
    assert!(disposal.worker_panics().is_empty());
    assert!(matches!(result, Err(ProtocolMachineError::Fault {
        coro_id, fault: Fault::PcOutOfBounds,
    }) if coro_id == first_id));
    assert_eq!(
        clock_after, tick,
        "dispatch cannot invent another scheduler tick"
    );
    assert_public_returned_generic_custody(&calls, &exchanges, second_sid, second_pc);
    assert_public_returned_selection(&selected, first_id, second_id, tick);
    assert!(calls.iter().all(|request| request.tick == tick));
}

#[cfg(not(target_arch = "wasm32"))]
fn assert_public_returned_generic_custody(
    calls: &[crate::effect::EffectRequest],
    exchanges: &[crate::effect::EffectExchangeRecord],
    second_sid: crate::session::SessionId,
    second_pc: usize,
) {
    use crate::effect::EffectRequestBody;
    assert_eq!(
        second_pc, 1,
        "independent original result passes its own gates despite an unrelated local fault"
    );
    assert_eq!(
        calls
            .iter()
            .filter(|r| matches!(&r.body, EffectRequestBody::InvokeStep { .. }))
            .count(),
        1
    );
    assert_eq!(
        calls
            .iter()
            .filter(|r| matches!(&r.body, EffectRequestBody::OutputConditionHint { .. }))
            .count(),
        1
    );
    assert_eq!(
        calls
            .iter()
            .filter(|r| matches!(&r.body, EffectRequestBody::WalSync { .. }))
            .count(),
        1,
        "independent original commit must run its actual WAL gate exactly once"
    );
    let invocation = calls
        .iter()
        .find(|r| matches!(&r.body, EffectRequestBody::InvokeStep { .. }))
        .expect("actual callback reached before primary commit");
    assert_eq!(invocation.session, Some(second_sid));
    let retained = returned_wave_original_exchanges(exchanges, invocation);
    assert_eq!(
        retained.len(),
        1,
        "exact original callback observation reaches canonical custody once"
    );
    assert!(retained[0].succeeded());
    let outcome = retained[0]
        .outcome
        .clone()
        .into_invoke_state_for(&invocation.body);
    assert!(
        matches!(outcome, Ok(EffectResult::Success(state))
        if state.first() == Some(&Value::Str("actual-later-result".into()))),
        "retain actual typed returned state, without requiring live-register publication"
    );
}

#[cfg(not(target_arch = "wasm32"))]
fn assert_public_returned_selection(
    selected: &[LaneSelection],
    first: usize,
    second: usize,
    tick: u64,
) {
    assert_eq!(
        selected.len(),
        2,
        "actual checked public wave selected both original coroutines"
    );
    assert_eq!(selected[0].coro_id, first);
    assert_eq!(selected[1].coro_id, second);
    assert_ne!(selected[0].session, selected[1].session);
    assert_ne!(selected[0].lane, selected[1].lane);
    assert!(selected
        .iter()
        .all(|pick| pick.wave == 0 && pick.tick == tick));
}

// Real native two-pick regression; checkpoint evidence records actual outcomes.
#[cfg(not(target_arch = "wasm32"))]
struct PublicReturnedWalFailureHandler {
    calls: Mutex<Vec<crate::effect::EffectRequest>>,
    failure: crate::effect::EffectFailure,
}
#[cfg(not(target_arch = "wasm32"))]
impl EffectHandler for PublicReturnedWalFailureHandler {
    fn handle_effect(&self, request: crate::effect::EffectRequest) -> crate::effect::EffectOutcome {
        use crate::effect::{EffectOutcome, EffectRequestBody, EffectResponse};
        self.calls
            .lock()
            .expect("actual request owner")
            .push(request.clone());
        if let EffectRequestBody::InvokeStep { state, .. } = &request.body {
            let mut state = state.clone();
            state[0] = Value::Str("actual-later-result".into());
            return EffectOutcome::success(EffectResponse::InvokeStep { state });
        }
        if matches!(&request.body, EffectRequestBody::WalSync { .. }) {
            return EffectOutcome::failure(self.failure.clone());
        }
        NoopHandler.handle_effect(request)
    }
    fn handle_send(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        state: &[Value],
    ) -> EffectResult<Value> {
        NoopHandler.handle_send(role, partner, label, state)
    }
    fn handle_recv(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        state: &mut Vec<Value>,
        payload: &Value,
    ) -> EffectResult<()> {
        NoopHandler.handle_recv(role, partner, label, state, payload)
    }
    fn handle_choose(
        &self,
        role: &str,
        partner: &str,
        labels: &[String],
        state: &[Value],
    ) -> EffectResult<String> {
        NoopHandler.handle_choose(role, partner, labels, state)
    }
    fn step(&self, role: &str, state: &mut Vec<Value>) -> EffectResult<()> {
        NoopHandler.step(role, state)
    }
    fn supports_wal_sync(&self) -> bool {
        true
    }
}
// Actual native multi-pick regression; outcomes are retained in checkpoint receipts.
// Exercises actual two-pick native dispatch, not arbitrary injected Result values.
#[cfg(not(target_arch = "wasm32"))]
#[test]
fn public_wave_retains_later_wal_refusal_after_first_fault() {
    let mut machine = ThreadedProtocolMachine::with_workers(
        ProtocolMachineConfig {
            threaded_round_semantics: crate::ThreadedRoundSemantics::WaveParallelExtension,
            output_condition_policy: crate::output_condition::OutputConditionPolicy::AllowAll,
            ..ProtocolMachineConfig::default()
        },
        2,
    );
    assert!(machine.config.instruction_cost > 0);
    let image = lifecycle_loop_image(true);
    let first_owner = machine
        .load_choreography_owned(&image, "actual-first-owner")
        .expect("first issued owner");
    let second_owner = machine
        .load_choreography_owned(&image, "actual-second-owner")
        .expect("second issued owner");
    let first_sid = first_owner.session_id();
    let second_sid = second_owner.session_id();
    let first = machine
        .coroutines
        .iter()
        .find(|original| original.lock().expect("resident coroutine").session_id == first_sid)
        .cloned()
        .expect("first resident coroutine handle");
    let second = machine
        .coroutines
        .iter()
        .find(|original| original.lock().expect("resident coroutine").session_id == second_sid)
        .cloned()
        .expect("second resident coroutine handle");
    let first_id = {
        let mut coro = first.lock().expect("first original coroutine");
        coro.pc = usize::MAX;
        coro.id
    };
    let second_id = {
        let coro = second.lock().expect("second original coroutine");
        assert!(coro.cost_budget >= machine.config.instruction_cost);
        coro.id
    };
    let retained_second = second.clone();
    let original_failure = crate::effect::EffectFailure::denied("actual independent WAL refusal");
    let handler = PublicReturnedWalFailureHandler {
        calls: Mutex::new(Vec::new()),
        failure: original_failure.clone(),
    };
    let tick = machine
        .clock
        .tick
        .checked_add(1)
        .expect("original next round is representable");
    let result = machine.step_round(&handler, 2);
    let selected = machine.lane_trace().to_vec();
    let second_pc = retained_second
        .lock()
        .expect("actual returned coroutine")
        .pc;
    let exchanges = machine.effect_exchanges().to_vec();
    let calls = handler.calls.lock().expect("real host calls").clone();
    let clock_after = machine.clock.tick;
    let faults = public_wal_returned_faults(&machine);
    // Consume actual original native worker handles before result assertions.
    let disposal = machine
        .shutdown_worker_pool()
        .expect("original worker settlement");
    assert_eq!(disposal.joined_workers(), 2);
    assert!(disposal.worker_panics().is_empty());
    assert!(matches!(result, Err(ProtocolMachineError::Fault {
        coro_id, fault: Fault::PcOutOfBounds,
    }) if coro_id == first_id));
    assert_eq!(
        clock_after, tick,
        "dispatch cannot invent another scheduler tick"
    );
    assert_public_wal_returned_generic_custody(&calls, &exchanges, second_sid, second_pc);
    assert_public_wal_returned_selection(&selected, first_id, second_id, tick);
    assert!(calls.iter().all(|request| request.tick == tick));
    assert_eq!(
        faults,
        vec![
            (tick, first_id, Fault::PcOutOfBounds),
            (
                tick,
                second_id,
                Fault::Invoke {
                    failure: original_failure.clone()
                }
            ),
        ]
    );
    assert_public_wal_refusal_custody(&calls, &exchanges, &original_failure, second_id, tick);
}

#[cfg(not(target_arch = "wasm32"))]
fn assert_public_wal_returned_generic_custody(
    calls: &[crate::effect::EffectRequest],
    exchanges: &[crate::effect::EffectExchangeRecord],
    second_sid: crate::session::SessionId,
    second_pc: usize,
) {
    use crate::effect::EffectRequestBody;
    assert_eq!(
        second_pc, 0,
        "independent original result cannot advance after its own actual WAL refusal"
    );
    assert_eq!(
        calls
            .iter()
            .filter(|r| matches!(&r.body, EffectRequestBody::InvokeStep { .. }))
            .count(),
        1
    );
    assert_eq!(
        calls
            .iter()
            .filter(|r| matches!(&r.body, EffectRequestBody::OutputConditionHint { .. }))
            .count(),
        1
    );
    assert_eq!(
        calls
            .iter()
            .filter(|r| matches!(&r.body, EffectRequestBody::WalSync { .. }))
            .count(),
        1,
        "independent original commit must run its actual WAL gate exactly once"
    );
    let invocation = calls
        .iter()
        .find(|r| matches!(&r.body, EffectRequestBody::InvokeStep { .. }))
        .expect("actual callback reached before primary commit");
    assert_eq!(invocation.session, Some(second_sid));
    let retained = returned_wave_original_exchanges(exchanges, invocation);
    assert_eq!(
        retained.len(),
        1,
        "exact original callback observation reaches canonical custody once"
    );
    assert!(retained[0].succeeded());
    let outcome = retained[0]
        .outcome
        .clone()
        .into_invoke_state_for(&invocation.body);
    assert!(
        matches!(outcome, Ok(EffectResult::Success(state))
        if state.first() == Some(&Value::Str("actual-later-result".into()))),
        "retain actual typed returned state, without requiring live-register publication"
    );
}

#[cfg(not(target_arch = "wasm32"))]
fn assert_public_wal_returned_selection(
    selected: &[LaneSelection],
    first: usize,
    second: usize,
    tick: u64,
) {
    assert_eq!(
        selected.len(),
        2,
        "actual checked public wave selected both original coroutines"
    );
    assert_eq!(selected[0].coro_id, first);
    assert_eq!(selected[1].coro_id, second);
    assert_ne!(selected[0].session, selected[1].session);
    assert_ne!(selected[0].lane, selected[1].lane);
    assert!(selected
        .iter()
        .all(|pick| pick.wave == 0 && pick.tick == tick));
}

#[cfg(not(target_arch = "wasm32"))]
fn assert_public_wal_refusal_custody(
    calls: &[crate::effect::EffectRequest],
    exchanges: &[crate::effect::EffectExchangeRecord],
    original_failure: &crate::effect::EffectFailure,
    second_id: usize,
    tick: u64,
) {
    let request = calls
        .iter()
        .find(|request| {
            matches!(
                &request.body,
                crate::effect::EffectRequestBody::WalSync { .. }
            )
        })
        .expect("actual original WAL gate reached");
    let crate::effect::EffectRequestBody::WalSync { sync } = &request.body else {
        panic!("selected actual WAL request");
    };
    assert_eq!(sync.downstream_coroutine_id, format!("coro:{second_id}"));
    assert_eq!(sync.tick, tick);
    let retained = returned_wave_original_exchanges(exchanges, request);
    assert_eq!(retained.len(), 1, "retain exact original WAL outcome once");
    let outcome = retained[0].outcome.clone().into_unit("wal_sync");
    assert!(
        matches!(outcome,
            Ok(EffectResult::Failure(failure)) if &failure == original_failure
        ),
        "retain actual independent WAL refusal, not an inferred error"
    );
}

#[cfg(not(target_arch = "wasm32"))]
fn public_wal_returned_faults(machine: &ThreadedProtocolMachine) -> Vec<(u64, usize, Fault)> {
    machine
        .trace
        .iter()
        .filter_map(|event| match event {
            ObsEvent::Faulted {
                tick,
                coro_id,
                fault,
            } => Some((*tick, *coro_id, fault.clone())),
            _ => None,
        })
        .collect()
}

#[cfg(not(target_arch = "wasm32"))]
fn returned_wave_original_exchanges<'a>(
    exchanges: &'a [crate::effect::EffectExchangeRecord],
    original: &crate::effect::EffectRequest,
) -> Vec<&'a crate::effect::EffectExchangeRecord> {
    assert_eq!(
        original.effect_id, None,
        "actual callback precedes canonical ID assignment"
    );
    let retained: Vec<_> = exchanges
        .iter()
        .filter(|record| {
            let mut issued = original.clone();
            issued.effect_id = Some(record.effect_id);
            record.request == issued
        })
        .collect();
    for record in &retained {
        assert_eq!(record.request.effect_id, Some(record.effect_id));
        assert_eq!(
            exchanges
                .iter()
                .filter(|other| other.effect_id == record.effect_id)
                .count(),
            1,
            "canonical assigned occurrence is unique across the complete exchange ledger"
        );
    }
    retained
}

#[cfg(not(target_arch = "wasm32"))]
#[test]
fn public_wave_effect_capacity_holds_the_whole_original_selection() {
    for enough in [false, true] {
        let mut machine = ThreadedProtocolMachine::with_workers(
            ProtocolMachineConfig {
                threaded_round_semantics: crate::ThreadedRoundSemantics::WaveParallelExtension,
                output_condition_policy: crate::output_condition::OutputConditionPolicy::AllowAll,
                ..ProtocolMachineConfig::default()
            },
            2,
        );
        let image = lifecycle_loop_image(true);
        let first = machine
            .load_choreography_owned(&image, "capacity-first-owner")
            .unwrap();
        let second = machine
            .load_choreography_owned(&image, "capacity-second-owner")
            .unwrap();
        let handler = PublicReturnedGenericHandler {
            calls: Mutex::new(Vec::new()),
        };
        machine.next_effect_id = if enough { u64::MAX - 9 } else { u64::MAX - 5 };
        let original_roles: Vec<_> = machine
            .coroutines()
            .iter()
            .map(|coro| (coro.session_id, coro.id))
            .collect();
        let ready = machine.scheduler.ready_set_snapshot();
        let before = capacity_original_instructions(&machine);
        let result = machine.step_round(&handler, 2);
        let after = capacity_original_instructions(&machine);
        let ready_after = machine.scheduler.ready_set_snapshot();
        let exchanges = machine.effect_exchanges().to_vec();
        let canonical = machine.outstanding_effects().to_vec();
        let derived: Vec<_> = machine
            .effect_trace()
            .iter()
            .filter(|entry| entry.effect_kind == "invoke_step")
            .cloned()
            .collect();

        let publications = machine
            .trace()
            .iter()
            .filter(|event| matches!(event, ObsEvent::Invoked { .. }))
            .count();

        let calls = handler.calls.into_inner().unwrap();
        let counter = machine.next_effect_id;
        let tick = machine.clock.tick;
        let selection = machine.lane_trace().to_vec();
        let disposal = machine.shutdown_worker_pool().unwrap();
        assert_eq!(disposal.joined_workers(), 2);
        assert!(disposal.worker_panics().is_empty());
        assert_ne!(first.session_id(), second.session_id());
        assert_eq!(tick, 1);
        if enough {
            assert!(result.is_ok());
            assert_eq!(counter, u64::MAX);
            assert_eq!(selection.len(), 2);
            for sid in [first.session_id(), second.session_id()] {
                let original = original_roles
                    .iter()
                    .find(|(session, _)| *session == sid)
                    .unwrap()
                    .1;
                assert_eq!(
                    selection
                        .iter()
                        .filter(|pick| pick.session == sid
                            && pick.coro_id == original
                            && pick.tick == tick)
                        .count(),
                    1
                );
                assert_capacity_public_owner_result(
                    &calls, &exchanges, &derived, sid, original, tick,
                );
            }

            assert!(after.iter().all(|(_, pc, _, _)| *pc == 1));
        } else {
            let error = result.unwrap_err();
            assert_capacity_wave_refusal(&error, &calls, &exchanges, counter);
            assert_eq!(before, after, "no instruction/register/cost mutation");
            assert_eq!(ready, ready_after, "all original selections restored");
        }
        assert_capacity_wave_occurrences(
            &calls,
            &exchanges,
            &canonical,
            &derived,
            publications,
            tick,
        );
    }
}

#[cfg(not(target_arch = "wasm32"))]
fn capacity_original_instructions(
    machine: &ThreadedProtocolMachine,
) -> Vec<(usize, usize, Vec<Value>, usize)> {
    machine
        .coroutines()
        .iter()
        .map(|coro| (coro.id, coro.pc, coro.regs.clone(), coro.cost_budget))
        .collect()
}

#[cfg(not(target_arch = "wasm32"))]
fn assert_capacity_public_owner_result(
    calls: &[crate::effect::EffectRequest],
    exchanges: &[crate::effect::EffectExchangeRecord],
    derived: &[crate::effect::EffectTraceEntry],
    sid: crate::session::SessionId,
    original: usize,
    tick: u64,
) {
    use crate::effect::EffectRequestBody;
    let original_derived: Vec<_> = derived
        .iter()
        .filter(|entry| {
            entry
                .inputs
                .get("coro_id")
                .and_then(serde_json::Value::as_u64)
                .and_then(|id| usize::try_from(id).ok())
                == Some(original)
        })
        .collect();
    assert_eq!(original_derived.len(), 1);
    assert_eq!(original_derived[0].ordering_key, tick);
    assert_eq!(original_derived[0].outputs, json!({"ok": true}));

    let invokes: Vec<_> = calls
        .iter()
        .filter(|request| {
            request.session == Some(sid)
                && matches!(request.body, EffectRequestBody::InvokeStep { .. })
        })
        .collect();
    assert_eq!(invokes.len(), 1);
    let invocation = invokes[0];
    assert_eq!(invocation.tick, tick);
    let retained = returned_wave_original_exchanges(exchanges, invocation);
    assert_eq!(retained.len(), 1);
    let EffectRequestBody::InvokeStep { state, .. } = &invocation.body else {
        unreachable!()
    };
    let mut expected = state.clone();
    expected[0] = Value::Str("actual-later-result".into());
    assert_eq!(
        retained[0]
            .outcome
            .clone()
            .into_invoke_state_for(&invocation.body)
            .unwrap(),
        EffectResult::Success(expected)
    );
    let hints: Vec<_> = calls
        .iter()
        .filter(|request| {
            request.session == Some(sid)
                && matches!(request.body, EffectRequestBody::OutputConditionHint { .. })
        })
        .collect();
    assert_eq!(hints.len(), 1);
    let retained_hint = returned_wave_original_exchanges(exchanges, hints[0]);
    assert_eq!(retained_hint.len(), 1);
    assert_eq!(
        retained_hint[0]
            .outcome
            .clone()
            .into_output_condition_hint()
            .unwrap(),
        None
    );
    let wals: Vec<_> = calls.iter().filter(|request| matches!(&request.body,
        EffectRequestBody::WalSync { sync } if sync.downstream_coroutine_id == format!("coro:{original}")))
        .collect();
    assert_eq!(wals.len(), 1);
    let EffectRequestBody::WalSync { sync } = &wals[0].body else {
        unreachable!()
    };
    assert_eq!(
        wals[0].session, None,
        "canonical WAL envelope is operation-scoped"
    );
    assert_eq!(wals[0].tick, tick);
    assert_eq!(sync.tick, tick);
    assert_eq!(wals[0].operation_id.as_ref(), Some(&sync.operation_id));
    if let Some(agreement) = &sync.agreement_state {
        assert_eq!(agreement.session, Some(sid));
    }
    let retained_wal = returned_wave_original_exchanges(exchanges, wals[0]);
    assert_eq!(retained_wal.len(), 1);
    assert_eq!(
        retained_wal[0]
            .outcome
            .clone()
            .into_unit("wal_sync")
            .unwrap(),
        EffectResult::Success(())
    );
}

#[cfg(not(target_arch = "wasm32"))]
fn assert_capacity_wave_occurrences(
    calls: &[crate::effect::EffectRequest],
    exchanges: &[crate::effect::EffectExchangeRecord],
    canonical: &[crate::semantic_objects::OutstandingEffect],
    derived: &[crate::effect::EffectTraceEntry],
    publications: usize,
    tick: u64,
) {
    assert_eq!(
        calls
            .iter()
            .filter(|request| matches!(
                request.body,
                crate::effect::EffectRequestBody::InvokeStep { .. }
            ))
            .count(),
        publications
    );
    assert_eq!(
        calls
            .iter()
            .filter(|request| matches!(
                request.body,
                crate::effect::EffectRequestBody::WalSync { .. }
            ))
            .count(),
        publications
    );
    assert!(exchanges.iter().all(|record| record.request.tick == tick));

    let canonical_ids: BTreeSet<_> = canonical.iter().map(|effect| effect.effect_id).collect();
    assert_eq!(canonical_ids.len(), canonical.len());
    assert_eq!(canonical.len(), exchanges.len() + publications);
    assert!(exchanges
        .iter()
        .all(|exchange| canonical_ids.contains(&exchange.effect_id)));
    assert!(canonical_ids.iter().all(|id| *id < u64::MAX));

    assert_eq!(derived.len(), publications);
    let occurrence_ids: Vec<_> = exchanges
        .iter()
        .map(|record| record.effect_id)
        .chain(derived.iter().map(|entry| entry.effect_id))
        .collect();
    let occurrence_set: BTreeSet<_> = occurrence_ids.iter().copied().collect();
    assert_eq!(
        occurrence_ids.len(),
        occurrence_set.len(),
        "callbacks and derived commits never alias"
    );
    assert!(occurrence_set.iter().all(|id| *id < u64::MAX));
    let ids: BTreeSet<_> = exchanges.iter().map(|record| record.effect_id).collect();
    assert_eq!(ids.len(), exchanges.len());
    assert!(ids.iter().all(|id| *id < u64::MAX));
}

#[cfg(not(target_arch = "wasm32"))]
fn assert_capacity_wave_refusal(
    error: &ProtocolMachineError,
    calls: &[crate::effect::EffectRequest],
    exchanges: &[crate::effect::EffectExchangeRecord],
    counter: u64,
) {
    let ProtocolMachineError::HandlerError(actual) = error else {
        panic!("expected complete-wave capacity refusal");
    };
    assert_eq!(
        actual,
        &EffectFailure::contract_violation("canonical effect occurrence identifiers exhausted")
    );
    assert_eq!(calls.len(), 1);
    assert!(matches!(
        calls[0].body,
        crate::effect::EffectRequestBody::TopologyEvents { .. }
    ));
    assert_eq!(
        exchanges.len(),
        1,
        "only admitted original poll, no worker issuance"
    );
    assert_eq!(counter, u64::MAX - 4);
}
