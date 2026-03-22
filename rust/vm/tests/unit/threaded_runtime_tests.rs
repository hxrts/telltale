    use super::*;
    use crate::buffer::BufferConfig;
    use crate::communication_replay::{CommunicationReplayMode, DefaultCommunicationConsumption};
    use crate::coroutine::KnowledgeFact;
    use crate::effect::{EffectFailure, EffectHandler, EffectResult, SendDecision, SendDecisionInput};
    use crate::verification::{Hash, Signature, VerifyingKey};
    use crate::vm::{FlowPolicy, FlowPredicate};
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

    fn evaluate_check(
        policy: FlowPolicy,
        known_fact: &str,
        query_fact: &str,
        target: &str,
    ) -> bool {
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

        let cfg = VMConfig {
            flow_policy: policy,
            ..VMConfig::default()
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
        let mut vm = ThreadedVM::with_workers(VMConfig::default(), 1);
        vm.load_choreography(&image).expect("load choreography");
        let status = vm
            .run(&NoopHandler, 8)
            .expect("run should return bounded status");
        assert_eq!(status, RunStatus::MaxRoundsExceeded);
    }

    #[test]
    fn try_with_workers_rejects_invalid_config_without_panicking() {
        let config = VMConfig {
            num_registers: 0,
            ..VMConfig::default()
        };
        let result = ThreadedVM::try_with_workers(config, 1);
        assert!(matches!(result, Err(VMError::InvalidConfig { .. })));
    }

    #[test]
    fn threaded_replay_accessors_fail_fast_on_poisoned_locks() {
        let vm = ThreadedVM::with_workers(VMConfig::default(), 1);
        let replay = vm.communication_consumption.clone();
        let artifacts = vm.communication_consumption_artifacts.clone();

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
            let _ignored = vm.communication_replay_root();
        }));
        assert!(
            root_access.is_err(),
            "replay-root accessor should fail fast after poison"
        );

        let artifacts_access = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _ignored = vm.communication_consumption_artifacts();
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

        let config = VMConfig::default();
        let guard_resources = Arc::new(Mutex::new(BTreeMap::new()));
        let resource_states = Arc::new(Mutex::new(BTreeMap::new()));
        let communication_consumption = Arc::new(Mutex::new(
            DefaultCommunicationConsumption::new(CommunicationReplayMode::Off),
        ));
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
        };
        let err = match step_recv(&mut coro, &session, "B", 0, 1, &step_ctx) {
            Ok(_) => panic!("tampered signature must fault"),
            Err(err) => err,
        };
        assert!(matches!(err, Fault::VerificationFailed { .. }));
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

        let mut vm = ThreadedVM::with_workers(VMConfig::default(), 2);
        let sid = vm.load_choreography(&image).expect("load choreography");
        let endpoint = Endpoint {
            sid,
            role: "A".to_string(),
        };

        let mut source = None;
        let mut target = None;
        for coro in &vm.coroutines {
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
            let target_arc = vm
                .coroutines
                .get(target)
                .cloned()
                .expect("target coroutine arc");
            let mut target_guard = target_arc.lock().expect("coroutine lock poisoned");
            target_guard.owned_endpoints.push(endpoint.clone());
        }

        let err = vm
            .enqueue_handoff(endpoint, source, target, vm.clock.tick)
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

        let mut vm = ThreadedVM::with_workers(VMConfig::default(), 2);
        let sid = vm.load_choreography(&image).expect("load choreography");
        let endpoint = Endpoint {
            sid,
            role: "A".to_string(),
        };

        let mut source = None;
        let mut target = None;
        for coro in &vm.coroutines {
            let guard = coro.lock().expect("coroutine lock poisoned");
            if guard.role == "A" {
                source = Some(guard.id);
            } else if guard.role == "B" {
                target = Some(guard.id);
            }
        }
        let source = source.expect("source coroutine");
        let target = target.expect("target coroutine");

        vm.enqueue_handoff(endpoint.clone(), source, target, vm.clock.tick)
            .expect("enqueue handoff");
        let receipt = &vm.handoff_trace().last().expect("handoff trace").receipt;
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

        let mut vm = ThreadedVM::with_workers(VMConfig::default(), 3);
        let sid = vm.load_choreography(&image).expect("load choreography");
        let endpoint = Endpoint {
            sid,
            role: "A".to_string(),
        };

        let mut source = None;
        let mut target = None;
        let mut third = None;
        for coro in &vm.coroutines {
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

        vm.enqueue_handoff(endpoint.clone(), source, target, vm.clock.tick)
            .expect("enqueue handoff");

        {
            let third_arc = vm
                .coroutines
                .get(third)
                .cloned()
                .expect("third coroutine arc");
            let mut third_guard = third_arc.lock().expect("coroutine lock poisoned");
            third_guard.owned_endpoints.push(endpoint.clone());
        }

        let err = vm
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

        let source_guard = vm.coroutines[source]
            .lock()
            .expect("source coroutine lock poisoned");
        let target_guard = vm.coroutines[target]
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
        let audit = vm
            .delegation_audit_log()
            .last()
            .expect("rollback should be audited");
        assert_eq!(audit.status, DelegationStatus::RolledBack);
        assert!(audit.reason.as_ref().is_some_and(|r| r.contains("delegation guard violation")));
    }

    #[test]
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

        let mut vm = ThreadedVM::with_workers(VMConfig::default(), 2);
        let sid = vm.load_choreography(&image).expect("load choreography");
        let endpoint = Endpoint {
            sid,
            role: "A".to_string(),
        };

        let mut source = None;
        let mut target = None;
        for coro in &vm.coroutines {
            let guard = coro.lock().expect("coroutine lock poisoned");
            if guard.role == "A" {
                source = Some(guard.id);
            } else if guard.role == "B" {
                target = Some(guard.id);
            }
        }
        let source = source.expect("source coroutine");
        let target = target.expect("target coroutine");

        vm.outstanding_effects.push(OutstandingEffect {
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
        vm.outstanding_effects.push(OutstandingEffect {
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
        vm.operation_instances.push(OperationInstance {
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
        vm.operation_instances.push(OperationInstance {
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

        vm.enqueue_handoff(endpoint, source, target, vm.clock.tick)
            .expect("enqueue handoff");
        vm.apply_handoffs_deterministically()
            .expect("apply handoff");

        let pending = vm
            .outstanding_effects
            .iter()
            .find(|effect| effect.effect_id == 11)
            .expect("pending effect");
        assert_eq!(pending.owner_id.as_deref(), Some("coro:1"));
        assert_eq!(pending.status, OutstandingEffectStatus::Pending);

        let blocked = vm
            .outstanding_effects
            .iter()
            .find(|effect| effect.effect_id == 12)
            .expect("blocked effect");
        assert_eq!(blocked.owner_id.as_deref(), Some("coro:1"));
        assert_eq!(blocked.status, OutstandingEffectStatus::Invalidated);
    }

    #[test]
    fn progress_contracts_escalate_consistently_in_threaded_runtime() {
        let mut vm = ThreadedVM::with_workers(VMConfig::default(), 2);
        vm.clock.tick = 1;
        let effect_id = vm.issue_runtime_effect(
            "invoke_step",
            Some(7),
            "host/runtime",
            serde_json::json!({ "session": 7 }),
        );

        vm.clock.tick = 2;
        vm.evaluate_progress_contracts()
            .expect("blocked escalation should succeed");
        assert_eq!(
            vm.progress_contracts
                .iter()
                .find(|contract| contract.operation_id == format!("effect:{effect_id}"))
                .expect("progress contract")
                .state,
            ProgressState::Blocked
        );

        vm.clock.tick = 3;
        vm.evaluate_progress_contracts()
            .expect("no-progress escalation should succeed");
        assert_eq!(
            vm.progress_contracts
                .iter()
                .find(|contract| contract.operation_id == format!("effect:{effect_id}"))
                .expect("progress contract")
                .state,
            ProgressState::NoProgress
        );

        vm.clock.tick = 4;
        vm.evaluate_progress_contracts()
            .expect("degraded escalation should succeed");
        assert_eq!(
            vm.progress_contracts
                .iter()
                .find(|contract| contract.operation_id == format!("effect:{effect_id}"))
                .expect("progress contract")
                .state,
            ProgressState::Degraded
        );

        vm.clock.tick = 5;
        vm.evaluate_progress_contracts()
            .expect("timeout escalation should succeed");
        assert_eq!(
            vm.progress_contracts
                .iter()
                .find(|contract| contract.operation_id == format!("effect:{effect_id}"))
                .expect("progress contract")
                .state,
            ProgressState::TimedOut
        );
        let err = vm
            .complete_runtime_effect(
                effect_id,
                OutstandingEffectStatus::Succeeded,
                serde_json::json!({ "status": "success" }),
            )
            .expect_err("late timeout result must be rejected");
        assert!(err.to_string().contains("late result"));
    }
