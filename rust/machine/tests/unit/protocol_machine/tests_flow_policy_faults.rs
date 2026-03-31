    #[test]
    fn test_check_applies_predicate_flow_policy() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut machine = ProtocolMachine::new(ProtocolMachineConfig {
            flow_policy: FlowPolicy::PredicateExpr(FlowPredicate::FactContains(
                "secret".to_string(),
            )),
            ..ProtocolMachineConfig::default()
        });
        let sid = machine.load_choreography(&image).unwrap();

        let a_idx = machine
            .coroutines
            .iter()
            .position(|c| c.role == "A")
            .expect("A coroutine exists");
        let ep_a = Endpoint {
            sid,
            role: "A".to_string(),
        };

        machine.coroutines[a_idx]
            .knowledge_set
            .push(crate::coroutine::KnowledgeFact {
                endpoint: ep_a.clone(),
                fact: "top_secret".to_string(),
            });
        machine.coroutines[a_idx].regs[2] = Value::Prod(
            Box::new(Value::Endpoint(ep_a)),
            Box::new(Value::Str("top_secret".to_string())),
        );
        machine.coroutines[a_idx].regs[3] = Value::Str("Observer".to_string());

        let a_program_id = machine.coroutines[a_idx].program_id;
        machine.replace_program_for_test(a_program_id, vec![
            Instr::Check {
                knowledge: 2,
                target: 3,
                dst: 4,
            },
            Instr::Halt,
        ]);

        let handler = PassthroughHandler;
        let _ignored = machine.step(&handler).expect("check step should succeed");
        assert_eq!(machine.coroutines[a_idx].regs[4], Value::Bool(true));
    }

    #[test]
    fn test_check_applies_runtime_predicate_flow_policy() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut machine = ProtocolMachine::new(ProtocolMachineConfig {
            flow_policy: FlowPolicy::predicate(|knowledge: &KnowledgeFact, target: &str| {
                knowledge.fact.contains("secret") && target == "Observer"
            }),
            ..ProtocolMachineConfig::default()
        });
        let sid = machine.load_choreography(&image).unwrap();

        let a_idx = machine
            .coroutines
            .iter()
            .position(|c| c.role == "A")
            .expect("A coroutine exists");
        let ep_a = Endpoint {
            sid,
            role: "A".to_string(),
        };

        machine.coroutines[a_idx].knowledge_set.push(KnowledgeFact {
            endpoint: ep_a.clone(),
            fact: "top_secret".to_string(),
        });
        machine.coroutines[a_idx].regs[2] = Value::Prod(
            Box::new(Value::Endpoint(ep_a)),
            Box::new(Value::Str("top_secret".to_string())),
        );
        machine.coroutines[a_idx].regs[3] = Value::Str("Observer".to_string());

        let a_program_id = machine.coroutines[a_idx].program_id;
        machine.replace_program_for_test(a_program_id, vec![
            Instr::Check {
                knowledge: 2,
                target: 3,
                dst: 4,
            },
            Instr::Halt,
        ]);

        let handler = PassthroughHandler;
        let _ignored = machine.step(&handler).expect("check step should succeed");
        assert_eq!(machine.coroutines[a_idx].regs[4], Value::Bool(true));
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

        let mut machine = ProtocolMachine::new(ProtocolMachineConfig {
            flow_policy: policy,
            ..ProtocolMachineConfig::default()
        });
        let sid = machine.load_choreography(&image).expect("load choreography");
        let a_idx = machine
            .coroutines
            .iter()
            .position(|c| c.role == "A")
            .expect("A coroutine exists");
        let ep_a = Endpoint {
            sid,
            role: "A".to_string(),
        };

        if insert_fact {
            machine.coroutines[a_idx].knowledge_set.push(KnowledgeFact {
                endpoint: ep_a.clone(),
                fact: known_fact.to_string(),
            });
        }
        machine.coroutines[a_idx].regs[2] = Value::Prod(
            Box::new(Value::Endpoint(ep_a)),
            Box::new(Value::Str(query_fact.to_string())),
        );
        machine.coroutines[a_idx].regs[3] = Value::Str(target_role.to_string());

        let a_program_id = machine.coroutines[a_idx].program_id;
        machine.replace_program_for_test(a_program_id, vec![
            Instr::Check {
                knowledge: 2,
                target: 3,
                dst: 4,
            },
            Instr::Halt,
        ]);

        let handler = PassthroughHandler;
        let _ignored = machine.step(&handler).expect("check step should execute");
        matches!(machine.coroutines[a_idx].regs[4], Value::Bool(true))
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
        let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
        machine.load_choreography(&image).expect("load choreography");
        let step = machine
            .step(&TimeoutOnTickOneHandler)
            .expect("timeout topology ingress should not fault");
        assert!(matches!(step, StepResult::Stuck));
        assert!(!machine.timed_out_sites().is_empty());
        let audit = machine.authority_audit_log();
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
        let active_timeout = machine
            .timeout_witnesses()
            .get("A")
            .expect("active timeout witness for A");
        assert_eq!(active_timeout.witness_id, 0);
        assert_eq!(active_timeout.until_tick, 21);
        assert!(machine.obs_trace().iter().any(|event| matches!(
            event,
            ObsEvent::TimeoutIssued {
                site,
                until_tick: 21,
                ..
            } if site == "A"
        )));
    }

    #[test]
    fn test_timeout_expiration_uses_the_same_issued_witness() {
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
        let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
        machine.load_choreography(&image).expect("load choreography");
        let _ = machine
            .step(&TimeoutOnTickOneHandler)
            .expect("timeout topology ingress should not fault");

        let issued = machine
            .timeout_witnesses()
            .get("A")
            .expect("issued timeout witness")
            .clone();
        machine.clock.tick = issued.until_tick;
        machine.prune_expired_timeouts();

        assert!(
            !machine.timeout_witnesses().contains_key("A"),
            "expired witness should be removed from active timeout state"
        );
        let audit = machine.authority_audit_log();
        assert_eq!(audit.len(), 2);
        assert_eq!(audit[0].event, AuthorityAuditEvent::Issued);
        assert_eq!(audit[1].event, AuthorityAuditEvent::Expired);
        match &audit[1].artifact {
            AuthorityArtifact::Timeout(expired) => assert_eq!(expired, &issued),
            other => panic!("expected expired timeout witness, got {other:?}"),
        }
    }

    #[test]
    fn test_new_timeout_invalidates_prior_witness_before_replacement() {
        struct TimeoutOnTickOneAndTwoHandler;

        impl EffectHandler for TimeoutOnTickOneAndTwoHandler {
            fn handle_send(
                &self,
                _role: &str,
                _partner: &str,
                _label: &str,
                _state: &[Value],
            ) -> EffectResult<Value> {
                EffectResult::success(Value::Nat(1))
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
                    None => {
                        EffectResult::failure(EffectFailure::invalid_input("no labels available"))
                    }
                }
            }

            fn step(&self, _role: &str, _state: &mut Vec<Value>) -> EffectResult<()> {
                EffectResult::success(())
            }

            fn topology_events(&self, tick: u64) -> EffectResult<Vec<TopologyPerturbation>> {
                match tick {
                    1 => EffectResult::success(vec![TopologyPerturbation::Timeout {
                        site: "A".to_string(),
                        duration: Duration::from_millis(20),
                    }]),
                    2 => EffectResult::success(vec![TopologyPerturbation::Timeout {
                        site: "A".to_string(),
                        duration: Duration::from_millis(40),
                    }]),
                    _ => EffectResult::success(Vec::new()),
                }
            }
        }

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
        let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
        machine.load_choreography(&image).expect("load choreography");
        let _ = machine
            .step(&TimeoutOnTickOneAndTwoHandler)
            .expect("first timeout ingress should not fault");
        let first = machine
            .timeout_witnesses()
            .get("A")
            .expect("first timeout witness")
            .clone();
        let _ = machine
            .step(&TimeoutOnTickOneAndTwoHandler)
            .expect("second timeout ingress should not fault");

        let audit = machine.authority_audit_log();
        assert_eq!(audit.len(), 3);
        assert_eq!(audit[0].event, AuthorityAuditEvent::Issued);
        assert_eq!(audit[1].event, AuthorityAuditEvent::Invalidated);
        assert_eq!(audit[2].event, AuthorityAuditEvent::Issued);
        match &audit[1].artifact {
            AuthorityArtifact::Timeout(invalidated) => assert_eq!(invalidated, &first),
            other => panic!("expected invalidated timeout witness, got {other:?}"),
        }
        let active = machine
            .timeout_witnesses()
            .get("A")
            .expect("replacement timeout witness");
        assert_ne!(active.witness_id, first.witness_id);
        assert_eq!(active.until_tick, 42);
    }

    #[test]
    fn test_corrupt_event_mutates_send_payload() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);
        let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
        let sid = machine.load_choreography(&image).expect("load choreography");

        let a_idx = machine
            .coroutines
            .iter()
            .position(|c| c.role == "A")
            .expect("A coroutine exists");
        machine.coroutines[a_idx].regs[1] = Value::Nat(10);

        let _ignored = machine
            .step(&CorruptOnTickOneHandler)
            .expect("send step with corruption should execute");
        let received = machine
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
        let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
        let owned = machine
            .load_choreography_owned(&image, "owner/a")
            .expect("load owned choreography");

        let receipt = owned
            .begin_transfer(&mut machine, "owner/b", OwnershipScope::Session)
            .expect("stage transfer");
        let witness = owned
            .cancel_abandoned_transfer(&mut machine, &receipt)
            .expect("cancel abandoned transfer");

        assert!(machine.obs_trace().iter().any(|event| matches!(
            event,
            ObsEvent::CancellationRequested {
                session,
                witness_id,
                ..
            } if session == &owned.session_id() && witness_id == &witness.witness_id
        )));
        assert!(machine.obs_trace().iter().any(|event| matches!(
            event,
            ObsEvent::Cancelled {
                session,
                witness_id,
                ..
            } if session == &owned.session_id() && witness_id == &witness.witness_id
        )));
        assert!(machine.obs_trace().iter().any(|event| matches!(
            event,
            ObsEvent::SessionTerminal {
                session,
                reason: SessionTerminalReason::Cancelled { .. },
                ..
            } if session == &owned.session_id()
        )));
    }

    #[test]
    fn test_crash_event_faults_session_and_clears_monitor_kind() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);
        let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
        let sid = machine.load_choreography(&image).expect("load choreography");

        assert!(machine.monitor.session_kinds.contains_key(&sid));
        let _ignored = machine
            .step(&CrashOnTickOneHandler)
            .expect("crash topology ingress should not fault step");
        let session = machine.sessions.get(sid).expect("session exists");
        assert!(matches!(session.status, SessionStatus::Faulted { .. }));
        assert!(!machine.monitor.session_kinds.contains_key(&sid));
        assert!(machine.crashed_sites.contains("A"));
    }

    #[test]
    fn protocol_machine_state_serialization_contains_lean_aligned_fields() {
        let machine = ProtocolMachine::new(ProtocolMachineConfig::default());
        let json = serde_json::to_value(&machine).expect("serialize ProtocolMachine state");
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
        let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
        machine.load_choreography(&image).expect("load choreography");

        machine.coroutines[0].session_id = usize::MAX - 1;
        let err = machine
            .wf_vm_state()
            .expect_err("dangling session reference should fail wf check");
        assert!(err.contains("references missing session"));
    }

    #[test]
    fn wf_vm_state_rejects_monitor_missing_kind_for_session() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);
        let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
        let sid = machine.load_choreography(&image).expect("load choreography");

        machine.monitor.remove_kind(sid);
        let err = machine
            .wf_vm_state()
            .expect_err("missing monitor kind should fail wf check");
        assert!(err.contains("monitor missing kind for active session"));
    }
