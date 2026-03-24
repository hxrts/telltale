    #[test]
    fn test_check_applies_predicate_flow_policy() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut vm = ProtocolMachine::new(ProtocolMachineConfig {
            flow_policy: FlowPolicy::PredicateExpr(FlowPredicate::FactContains(
                "secret".to_string(),
            )),
            ..ProtocolMachineConfig::default()
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
        vm.replace_program_for_test(a_program_id, vec![
            Instr::Check {
                knowledge: 2,
                target: 3,
                dst: 4,
            },
            Instr::Halt,
        ]);

        let handler = PassthroughHandler;
        let _ignored = vm.step(&handler).expect("check step should succeed");
        assert_eq!(vm.coroutines[a_idx].regs[4], Value::Bool(true));
    }

    #[test]
    fn test_check_applies_runtime_predicate_flow_policy() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut vm = ProtocolMachine::new(ProtocolMachineConfig {
            flow_policy: FlowPolicy::predicate(|knowledge: &KnowledgeFact, target: &str| {
                knowledge.fact.contains("secret") && target == "Observer"
            }),
            ..ProtocolMachineConfig::default()
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
        vm.replace_program_for_test(a_program_id, vec![
            Instr::Check {
                knowledge: 2,
                target: 3,
                dst: 4,
            },
            Instr::Halt,
        ]);

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

        let mut vm = ProtocolMachine::new(ProtocolMachineConfig {
            flow_policy: policy,
            ..ProtocolMachineConfig::default()
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
        vm.replace_program_for_test(a_program_id, vec![
            Instr::Check {
                knowledge: 2,
                target: 3,
                dst: 4,
            },
            Instr::Halt,
        ]);

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
        let mut vm = ProtocolMachine::new(ProtocolMachineConfig::default());
        vm.load_choreography(&image).expect("load choreography");
        let step = vm
            .step(&TimeoutOnTickOneHandler)
            .expect("timeout topology ingress should not fault");
        assert!(matches!(step, ProtocolMachineStepResult::Stuck));
        assert!(!vm.timed_out_sites().is_empty());
        let audit = vm.authority_audit_log();
        assert_eq!(audit.len(), 1);
        match &audit[0].artifact {
            AuthorityArtifact::Timeout(witness) => {
                assert_eq!(witness.site, "A");
                assert_eq!(witness.issued_at_tick, 1);
                assert_eq!(witness.until_tick, 21);
            }
            other => panic!("expected timeout witness, got {other:?}"),
        }
        assert_eq!(audit[0].event, AuthorityAuditEvent::Issued);
        assert!(vm.obs_trace().iter().any(|event| matches!(
            event,
            ObsEvent::TimeoutIssued {
                site,
                until_tick: 21,
                ..
            } if site == "A"
        )));
    }

    #[test]
    fn test_corrupt_event_mutates_send_payload() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);
        let mut vm = ProtocolMachine::new(ProtocolMachineConfig::default());
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
    fn test_cancel_abandoned_transfer_emits_request_and_completion() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);
        let mut vm = ProtocolMachine::new(ProtocolMachineConfig::default());
        let owned = vm
            .load_choreography_owned(&image, "owner/a")
            .expect("load owned choreography");

        let receipt = owned
            .begin_transfer(&mut vm, "owner/b", OwnershipScope::Session)
            .expect("stage transfer");
        let witness = owned
            .cancel_abandoned_transfer(&mut vm, &receipt)
            .expect("cancel abandoned transfer");

        assert!(vm.obs_trace().iter().any(|event| matches!(
            event,
            ObsEvent::CancellationRequested {
                session,
                witness_id,
                ..
            } if *session == owned.session_id() && *witness_id == witness.witness_id
        )));
        assert!(vm.obs_trace().iter().any(|event| matches!(
            event,
            ObsEvent::Cancelled {
                session,
                witness_id,
                ..
            } if *session == owned.session_id() && *witness_id == witness.witness_id
        )));
        assert!(vm.obs_trace().iter().any(|event| matches!(
            event,
            ObsEvent::SessionTerminal {
                session,
                reason: SessionTerminalReason::Cancelled { .. },
                ..
            } if *session == owned.session_id()
        )));
    }

    #[test]
    fn test_crash_event_faults_session_and_clears_monitor_kind() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);
        let mut vm = ProtocolMachine::new(ProtocolMachineConfig::default());
        let sid = vm.load_choreography(&image).expect("load choreography");

        assert!(vm.monitor.session_kinds.contains_key(&sid));
        let _ignored = vm
            .step(&CrashOnTickOneHandler)
            .expect("crash topology ingress should not fault step");
        let session = vm.sessions.get(sid).expect("session exists");
        assert!(matches!(session.status, SessionStatus::Faulted { .. }));
        assert!(!vm.monitor.session_kinds.contains_key(&sid));
        assert!(vm.crashed_sites.contains("A"));
    }

    #[test]
    fn vm_state_serialization_contains_lean_aligned_fields() {
        let vm = ProtocolMachine::new(ProtocolMachineConfig::default());
        let json = serde_json::to_value(&vm).expect("serialize ProtocolMachine state");
        let obj = json.as_object().expect("ProtocolMachine state must serialize as object");
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
            assert!(obj.contains_key(key), "missing ProtocolMachine state field: {key}");
        }
    }

    #[test]
    fn wf_vm_state_rejects_dangling_coroutine_session_reference() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);
        let mut vm = ProtocolMachine::new(ProtocolMachineConfig::default());
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
        let mut vm = ProtocolMachine::new(ProtocolMachineConfig::default());
        let sid = vm.load_choreography(&image).expect("load choreography");

        vm.monitor.remove_kind(sid);
        let err = vm
            .wf_vm_state()
            .expect_err("missing monitor kind should fail wf check");
        assert!(err.contains("monitor missing kind for active session"));
    }
