    #[test]
    fn test_check_applies_predicate_flow_policy() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut vm = VM::new(VMConfig {
            flow_policy: FlowPolicy::PredicateExpr(FlowPredicate::FactContains(
                "secret".to_string(),
            )),
            ..VMConfig::default()
        });
        let sid = vm.load_choreography(&image).unwrap();

        let a_idx = vm
            .coroutines
            .iter()
            .position(|c| c.role == "A")
            .expect("A coroutine exists");
        let ep_a = Endpoint {
            sid,
            role: "A".to_string(),
        };

        vm.coroutines[a_idx]
            .knowledge_set
            .push(crate::coroutine::KnowledgeFact {
                endpoint: ep_a.clone(),
                fact: "top_secret".to_string(),
            });
        vm.coroutines[a_idx].regs[2] = Value::Prod(
            Box::new(Value::Endpoint(ep_a)),
            Box::new(Value::Str("top_secret".to_string())),
        );
        vm.coroutines[a_idx].regs[3] = Value::Str("Observer".to_string());

        let a_program_id = vm.coroutines[a_idx].program_id;
        vm.programs[a_program_id] = vec![
            Instr::Check {
                knowledge: 2,
                target: 3,
                dst: 4,
            },
            Instr::Halt,
        ];

        let handler = PassthroughHandler;
        let _ignored = vm.step(&handler).expect("check step should succeed");
        assert_eq!(vm.coroutines[a_idx].regs[4], Value::Bool(true));
    }

    #[test]
    fn test_check_applies_runtime_predicate_flow_policy() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut vm = VM::new(VMConfig {
            flow_policy: FlowPolicy::predicate(|knowledge: &KnowledgeFact, target: &str| {
                knowledge.fact.contains("secret") && target == "Observer"
            }),
            ..VMConfig::default()
        });
        let sid = vm.load_choreography(&image).unwrap();

        let a_idx = vm
            .coroutines
            .iter()
            .position(|c| c.role == "A")
            .expect("A coroutine exists");
        let ep_a = Endpoint {
            sid,
            role: "A".to_string(),
        };

        vm.coroutines[a_idx].knowledge_set.push(KnowledgeFact {
            endpoint: ep_a.clone(),
            fact: "top_secret".to_string(),
        });
        vm.coroutines[a_idx].regs[2] = Value::Prod(
            Box::new(Value::Endpoint(ep_a)),
            Box::new(Value::Str("top_secret".to_string())),
        );
        vm.coroutines[a_idx].regs[3] = Value::Str("Observer".to_string());

        let a_program_id = vm.coroutines[a_idx].program_id;
        vm.programs[a_program_id] = vec![
            Instr::Check {
                knowledge: 2,
                target: 3,
                dst: 4,
            },
            Instr::Halt,
        ];

        let handler = PassthroughHandler;
        let _ignored = vm.step(&handler).expect("check step should succeed");
        assert_eq!(vm.coroutines[a_idx].regs[4], Value::Bool(true));
    }

    fn run_check_with_flow_policy(
        policy: FlowPolicy,
        target_role: &str,
        known_fact: &str,
        query_fact: &str,
        insert_fact: bool,
    ) -> bool {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut vm = VM::new(VMConfig {
            flow_policy: policy,
            ..VMConfig::default()
        });
        let sid = vm.load_choreography(&image).expect("load choreography");
        let a_idx = vm
            .coroutines
            .iter()
            .position(|c| c.role == "A")
            .expect("A coroutine exists");
        let ep_a = Endpoint {
            sid,
            role: "A".to_string(),
        };

        if insert_fact {
            vm.coroutines[a_idx].knowledge_set.push(KnowledgeFact {
                endpoint: ep_a.clone(),
                fact: known_fact.to_string(),
            });
        }
        vm.coroutines[a_idx].regs[2] = Value::Prod(
            Box::new(Value::Endpoint(ep_a)),
            Box::new(Value::Str(query_fact.to_string())),
        );
        vm.coroutines[a_idx].regs[3] = Value::Str(target_role.to_string());

        let a_program_id = vm.coroutines[a_idx].program_id;
        vm.programs[a_program_id] = vec![
            Instr::Check {
                knowledge: 2,
                target: 3,
                dst: 4,
            },
            Instr::Halt,
        ];

        let handler = PassthroughHandler;
        let _ignored = vm.step(&handler).expect("check step should execute");
        matches!(vm.coroutines[a_idx].regs[4], Value::Bool(true))
    }

    #[test]
    fn test_check_flow_policy_variant_matrix() {
        let mut allow_roles = BTreeSet::new();
        allow_roles.insert("Observer".to_string());

        let mut deny_roles = BTreeSet::new();
        deny_roles.insert("Observer".to_string());

        assert!(run_check_with_flow_policy(
            FlowPolicy::AllowAll,
            "Observer",
            "secret",
            "secret",
            true
        ));
        assert!(!run_check_with_flow_policy(
            FlowPolicy::DenyAll,
            "Observer",
            "secret",
            "secret",
            true
        ));
        assert!(run_check_with_flow_policy(
            FlowPolicy::AllowRoles(allow_roles),
            "Observer",
            "secret",
            "secret",
            true
        ));
        assert!(!run_check_with_flow_policy(
            FlowPolicy::DenyRoles(deny_roles),
            "Observer",
            "secret",
            "secret",
            true
        ));
        assert!(run_check_with_flow_policy(
            FlowPolicy::PredicateExpr(FlowPredicate::FactContains("secret".to_string())),
            "Observer",
            "top_secret",
            "top_secret",
            true
        ));
        assert!(run_check_with_flow_policy(
            FlowPolicy::predicate(|knowledge: &KnowledgeFact, target: &str| {
                knowledge.fact.contains("secret") && target == "Observer"
            }),
            "Observer",
            "top_secret",
            "top_secret",
            true
        ));
        assert!(!run_check_with_flow_policy(
            FlowPolicy::AllowAll,
            "Observer",
            "secret",
            "secret",
            false
        ));
    }

    #[test]
    fn test_timeout_event_blocks_scheduling() {
        let image = CodeImage {
            programs: {
                let mut m = BTreeMap::new();
                m.insert("A".to_string(), vec![Instr::Halt]);
                m
            },
            global_type: GlobalType::End,
            local_types: {
                let mut m = BTreeMap::new();
                m.insert("A".to_string(), LocalTypeR::End);
                m
            },
        };
        let mut vm = VM::new(VMConfig::default());
        vm.load_choreography(&image).expect("load choreography");
        let step = vm
            .step(&TimeoutOnTickOneHandler)
            .expect("timeout topology ingress should not fault");
        assert!(matches!(step, StepResult::Stuck));
        assert!(!vm.timed_out_sites().is_empty());
    }

    #[test]
    fn test_corrupt_event_mutates_send_payload() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);
        let mut vm = VM::new(VMConfig::default());
        let sid = vm.load_choreography(&image).expect("load choreography");

        let a_idx = vm
            .coroutines
            .iter()
            .position(|c| c.role == "A")
            .expect("A coroutine exists");
        vm.coroutines[a_idx].regs[1] = Value::Nat(10);

        let _ignored = vm
            .step(&CorruptOnTickOneHandler)
            .expect("send step with corruption should execute");
        let received = vm
            .sessions
            .get_mut(sid)
            .expect("session exists")
            .recv("A", "B");
        assert_eq!(received, Some(Value::Nat(11)));
    }

    #[test]
    fn test_crash_event_faults_session_and_clears_monitor_kind() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);
        let mut vm = VM::new(VMConfig::default());
        let sid = vm.load_choreography(&image).expect("load choreography");

        assert!(vm.monitor.session_kinds.contains_key(&sid));
        let _ignored = vm
            .step(&CrashOnTickOneHandler)
            .expect("crash topology ingress should not fault step");
        let session = vm.sessions.get(sid).expect("session exists");
        assert!(matches!(session.status, SessionStatus::Faulted { .. }));
        assert!(!vm.monitor.session_kinds.contains_key(&sid));
        assert!(vm.crashed_sites.contains(&"A".to_string()));
    }

    #[test]
    fn vm_state_serialization_contains_lean_aligned_fields() {
        let vm = VM::new(VMConfig::default());
        let json = serde_json::to_value(&vm).expect("serialize VM state");
        let obj = json.as_object().expect("VM state must serialize as object");
        for key in [
            "config",
            "code",
            "programs",
            "persistent",
            "coroutines",
            "sessions",
            "arena",
            "resource_states",
            "sched",
            "monitor",
            "obs_trace",
            "clock",
            "next_coro_id",
            "next_session_id",
            "crashed_sites",
            "partitioned_edges",
        ] {
            assert!(obj.contains_key(key), "missing VM state field: {key}");
        }
    }

    #[test]
    fn wf_vm_state_rejects_dangling_coroutine_session_reference() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);
        let mut vm = VM::new(VMConfig::default());
        vm.load_choreography(&image).expect("load choreography");

        vm.coroutines[0].session_id = usize::MAX - 1;
        let err = vm
            .wf_vm_state()
            .expect_err("dangling session reference should fail wf check");
        assert!(err.contains("references missing session"));
    }

    #[test]
    fn wf_vm_state_rejects_monitor_missing_kind_for_session() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);
        let mut vm = VM::new(VMConfig::default());
        let sid = vm.load_choreography(&image).expect("load choreography");

        vm.monitor.remove_kind(sid);
        let err = vm
            .wf_vm_state()
            .expect_err("missing monitor kind should fail wf check");
        assert!(err.contains("monitor missing kind for active session"));
    }
