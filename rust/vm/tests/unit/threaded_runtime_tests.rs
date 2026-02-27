    use super::*;
    use crate::buffer::BufferConfig;
    use crate::communication_replay::{CommunicationReplayMode, DefaultCommunicationConsumption};
    use crate::coroutine::KnowledgeFact;
    use crate::effect::{EffectHandler, SendDecision, SendDecisionInput};
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
        ) -> Result<Value, String> {
            Ok(Value::Unit)
        }

        fn send_decision(&self, input: SendDecisionInput<'_>) -> Result<SendDecision, String> {
            Ok(SendDecision::Deliver(input.payload.unwrap_or(Value::Unit)))
        }

        fn handle_recv(
            &self,
            _role: &str,
            _partner: &str,
            _label: &str,
            _state: &mut Vec<Value>,
            _payload: &Value,
        ) -> Result<(), String> {
            Ok(())
        }

        fn handle_choose(
            &self,
            _role: &str,
            _partner: &str,
            labels: &[String],
            _state: &[Value],
        ) -> Result<String, String> {
            labels
                .first()
                .cloned()
                .ok_or_else(|| "no labels available".to_string())
        }

        fn step(&self, _role: &str, _state: &mut Vec<Value>) -> Result<(), String> {
            Ok(())
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
        let handlers = vec![
            (("A".to_string(), "A".to_string()), "hAA".to_string()),
            (("A".to_string(), "B".to_string()), "hAB".to_string()),
            (("B".to_string(), "A".to_string()), "hBA".to_string()),
            (("B".to_string(), "B".to_string()), "hBB".to_string()),
        ];
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
                ("A".to_string(), LocalTypeR::End),
                ("B".to_string(), LocalTypeR::End),
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
    fn threaded_replay_accessors_recover_from_poisoned_locks() {
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

        let _root = vm.communication_replay_root();
        let snapshot = vm.communication_consumption_artifacts();
        assert!(snapshot.is_empty());
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
