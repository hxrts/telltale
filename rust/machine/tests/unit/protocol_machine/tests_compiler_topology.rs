    // Compiler topology tests for branch and choice codegen.

    #[test]
    fn test_compiler_multi_branch() {
        use crate::compiler::compile;

        // Send with 2 branches → should emit deterministic Offer(first-label) + branch code.
        let lt = LocalTypeR::send_choice(
            "B",
            vec![
                (Label::new("yes"), None, LocalTypeR::End),
                (Label::new("no"), None, LocalTypeR::End),
            ],
        );

        let code = compile(&lt);

        assert!(
            matches!(&code[0], Instr::Offer { label, .. } if label == "yes"),
            "expected Offer(\"yes\"), got {:?}",
            code[0]
        );
        assert!(
            matches!(code[1], Instr::Halt),
            "expected Halt after deterministic offer"
        );
    }

    #[test]
    fn test_compiler_single_branch_unchanged() {
        use crate::compiler::compile;

        // Single-branch Send → should emit Send, not Offer.
        let lt = LocalTypeR::Send {
            partner: "B".into(),
            branches: vec![(Label::new("msg"), None, LocalTypeR::End)],
        };
        let code = compile(&lt);
        assert!(matches!(code[0], Instr::Send { .. }));
    }

    #[test]
    fn test_vm_recursive_choice_protocol() {
        // mu x. A→B:{continue.A→B:data.x, stop.end}
        let mut local_types = BTreeMap::new();
        local_types.insert(
            "A".to_string(),
            LocalTypeR::mu(
                "x",
                LocalTypeR::send_choice(
                    "B",
                    vec![
                        (
                            Label::new("continue"),
                            None,
                            LocalTypeR::Send {
                                partner: "B".into(),
                                branches: vec![(Label::new("data"), None, LocalTypeR::var("x"))],
                            },
                        ),
                        (Label::new("stop"), None, LocalTypeR::End),
                    ],
                ),
            ),
        );
        local_types.insert(
            "B".to_string(),
            LocalTypeR::mu(
                "x",
                LocalTypeR::recv_choice(
                    "A",
                    vec![
                        (
                            Label::new("continue"),
                            None,
                            LocalTypeR::Recv {
                                partner: "A".into(),
                                branches: vec![(Label::new("data"), None, LocalTypeR::var("x"))],
                            },
                        ),
                        (Label::new("stop"), None, LocalTypeR::End),
                    ],
                ),
            ),
        );

        let global = GlobalType::mu(
            "x",
            GlobalType::comm(
                "A",
                "B",
                vec![
                    (
                        Label::new("continue"),
                        GlobalType::send("A", "B", Label::new("data"), GlobalType::var("x")),
                    ),
                    (Label::new("stop"), GlobalType::End),
                ],
            ),
        );

        // Manually craft bytecode: A offers "stop" immediately.
        let a_code = vec![
            Instr::Offer {
                chan: 0,
                label: "stop".into(),
            },
            Instr::Halt,
        ];
        let b_code = vec![
            Instr::Choose {
                chan: 0,
                table: vec![("continue".into(), 1), ("stop".into(), 3)],
            },
            // continue branch: Recv data, then loop back to Offer
            Instr::Receive { chan: 0, dst: 1 },
            Instr::Jump { target: 0 },
            // stop branch: Halt
            Instr::Halt,
        ];

        let image = CodeImage {
            programs: {
                let mut m = BTreeMap::new();
                m.insert("A".to_string(), a_code);
                m.insert("B".to_string(), b_code);
                m
            },
            global_type: global,
            local_types,
        };

        let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
        let _sid = machine.load_choreography(&image).unwrap();

        let handler = PassthroughHandler;
        machine.run(&handler, 100).unwrap();

        assert!(machine.coroutines.iter().all(|c| c.is_terminal()));
    }

    #[test]
    fn test_vm_single_branch_then_multi_branch_choice() {
        // B→A:ack, then mu t. B→A:{continue→t, stop→End}
        // This is the protocol that was failing in fuzz tests.
        let projected: BTreeMap<String, LocalTypeR> = {
            let global = GlobalType::Comm {
                sender: "B".into(),
                receiver: "A".into(),
                branches: vec![(
                    Label::new("ack"),
                    GlobalType::Mu {
                        var: "t".into(),
                        body: Box::new(GlobalType::Comm {
                            sender: "B".into(),
                            receiver: "A".into(),
                            branches: vec![
                                (Label::new("continue"), GlobalType::Var("t".into())),
                                (Label::new("stop"), GlobalType::End),
                            ],
                        }),
                    },
                )],
            };
            telltale_theory::projection::project_all(&global)
                .unwrap()
                .into_iter()
                .collect()
        };

        let global = GlobalType::Comm {
            sender: "B".into(),
            receiver: "A".into(),
            branches: vec![(
                Label::new("ack"),
                GlobalType::Mu {
                    var: "t".into(),
                    body: Box::new(GlobalType::Comm {
                        sender: "B".into(),
                        receiver: "A".into(),
                        branches: vec![
                            (Label::new("continue"), GlobalType::Var("t".into())),
                            (Label::new("stop"), GlobalType::End),
                        ],
                    }),
                },
            )],
        };
        let image = CodeImage::from_local_types(&projected, &global);

        let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
        let _sid = machine.load_choreography(&image).unwrap();

        let handler = PassthroughHandler;
        // Don't unwrap — just run to completion
        let _ignored = machine.run(&handler, 500);

        let faults: Vec<_> = machine
            .obs_trace
            .iter()
            .filter(|e| matches!(e, ObsEvent::Faulted { .. }))
            .collect();
        assert!(faults.is_empty(), "faults: {faults:?}");
    }

    #[test]
    fn test_output_condition_gate_denies_commit() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut machine = ProtocolMachine::new(ProtocolMachineConfig {
            output_condition_policy: OutputConditionPolicy::DenyAll,
            ..ProtocolMachineConfig::default()
        });
        let _sid = machine.load_choreography(&image).unwrap();

        let handler = PassthroughHandler;
        let result = machine.run(&handler, 10);
        assert!(result.is_err());
        assert!(
            matches!(
                result,
                Err(ProtocolMachineError::Fault {
                    fault: Fault::OutputCondition { .. },
                    ..
                })
            ),
            "expected output-condition fault, got: {result:?}"
        );
        assert!(machine
            .output_condition_checks()
            .iter()
            .any(|c| c.meta.predicate_ref == "protocol_machine.observable_output" && !c.passed));
    }

    #[test]
    fn test_output_condition_allowlist_accepts_default_predicate() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut machine = ProtocolMachine::new(ProtocolMachineConfig {
            output_condition_policy: OutputConditionPolicy::PredicateAllowList(vec![
                "protocol_machine.observable_output".to_string(),
            ]),
            ..ProtocolMachineConfig::default()
        });
        let _sid = machine.load_choreography(&image).unwrap();

        let handler = PassthroughHandler;
        machine.run(&handler, 100).unwrap();
        assert!(machine
            .output_condition_checks()
            .iter()
            .any(|c| c.meta.predicate_ref == "protocol_machine.observable_output" && c.passed));
    }

    #[test]
    fn test_effect_trace_records_committed_effects() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
        let _sid = machine.load_choreography(&image).unwrap();
        let handler = PassthroughHandler;
        machine.run(&handler, 100).unwrap();

        let kinds: Vec<_> = machine
            .effect_trace()
            .iter()
            .map(|e| e.effect_kind.as_str())
            .collect();
        assert!(kinds.contains(&"send_decision"));
        assert!(kinds.contains(&"handle_recv"));
    }

    #[test]
    fn test_effect_trace_capture_mode_disabled_records_no_entries() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut machine = ProtocolMachine::new(ProtocolMachineConfig {
            effect_trace_capture_mode: EffectTraceCaptureMode::Disabled,
            ..ProtocolMachineConfig::default()
        });
        machine.load_choreography(&image).expect("load choreography");
        machine.run(&PassthroughHandler, 100)
            .expect("run should succeed");

        assert!(machine.effect_trace().is_empty());
    }

    #[test]
    fn test_effect_trace_capture_mode_topology_only_filters_runtime_effects() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut machine = ProtocolMachine::new(ProtocolMachineConfig {
            effect_trace_capture_mode: EffectTraceCaptureMode::TopologyOnly,
            ..ProtocolMachineConfig::default()
        });
        machine.load_choreography(&image).expect("load choreography");
        machine.run(&TimeoutOnTickOneHandler, 100)
            .expect("run should succeed");

        assert!(!machine.effect_trace().is_empty());
        assert!(machine
            .effect_trace()
            .iter()
            .all(|entry| entry.effect_kind == "topology_event"));
    }

    #[test]
    fn test_host_contract_assertions_reject_handler_identity_flips() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut machine = ProtocolMachine::new(ProtocolMachineConfig {
            host_contract_assertions: HostContractMode::Enforced,
            ..ProtocolMachineConfig::default()
        });
        machine.load_choreography(&image).expect("load choreography");

        let err = machine
            .step(&IdentityFlappingHandler::new())
            .expect_err("identity change should fail with assertions enabled");
        match err {
            ProtocolMachineError::HandlerError(message) => {
                assert!(message.message.contains("handler_identity changed"));
            }
            ProtocolMachineError::Fault {
                fault: Fault::Invoke { failure },
                ..
            } => {
                assert!(failure.message.contains("handler_identity changed"));
            }
            other => panic!("unexpected error: {other:?}"),
        }
    }

    #[test]
    fn test_host_contract_assertions_reject_unsorted_topology_inputs() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut machine = ProtocolMachine::new(ProtocolMachineConfig {
            host_contract_assertions: HostContractMode::Enforced,
            ..ProtocolMachineConfig::default()
        });
        machine.load_choreography(&image).expect("load choreography");

        let err = machine
            .step(&UnsortedTopologyHandler)
            .expect_err("unsorted topology events should fail with assertions enabled");
        match err {
            ProtocolMachineError::HandlerError(message) => {
                assert!(message.message.contains("topology_events"));
                assert!(message.message.contains("pre-sorted"));
            }
            other => panic!("unexpected error: {other:?}"),
        }
    }

    #[test]
    fn test_transfer_moves_progress_tokens_with_endpoint() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
        let sid = machine.load_choreography(&image).unwrap();

        let a_idx = machine
            .coroutines
            .iter()
            .position(|c| c.role == "A")
            .expect("A coroutine exists");
        let b_idx = machine
            .coroutines
            .iter()
            .position(|c| c.role == "B")
            .expect("B coroutine exists");

        let ep_a = Endpoint {
            sid,
            role: "A".to_string(),
        };
        machine.coroutines[a_idx]
            .progress_tokens
            .push(ProgressToken::for_endpoint(ep_a.clone()));
        machine.coroutines[a_idx].regs[2] = Value::Endpoint(ep_a.clone());
        machine.coroutines[a_idx].regs[3] =
            Value::Nat(u64::try_from(machine.coroutines[b_idx].id).expect("coroutine id fits in u64"));

        let a_program_id = machine.coroutines[a_idx].program_id;
        machine.replace_program_for_test(a_program_id, vec![
            Instr::Transfer {
                endpoint: 2,
                target: 3,
                bundle: 0,
            },
            Instr::Halt,
        ]);

        let handler = PassthroughHandler;
        // Intentionally discard StepResult: we only care that the step executes without panic
        let _ignored = machine.step(&handler).expect("transfer step should succeed");

        assert!(machine.coroutines[a_idx].progress_tokens.is_empty());
        assert!(machine.coroutines[b_idx]
            .progress_tokens
            .iter()
            .any(|t| t.sid == sid && t.endpoint == ep_a));
        let audit = machine
            .delegation_audit_log()
            .last()
            .expect("delegation audit should be recorded");
        assert_eq!(audit.status, DelegationStatus::Committed);
        assert_eq!(audit.receipt.session, sid);
        assert_eq!(audit.receipt.from_coro, machine.coroutines[a_idx].id);
        assert_eq!(audit.receipt.to_coro, machine.coroutines[b_idx].id);
        assert_eq!(
            audit.receipt.scope,
            OwnershipScope::Fragments(BTreeSet::from(["A".to_string()]))
        );
    }

    #[test]
    fn test_transfer_rejects_delegation_guard_violation() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
        let sid = machine.load_choreography(&image).unwrap();

        let a_idx = machine
            .coroutines
            .iter()
            .position(|c| c.role == "A")
            .expect("A coroutine exists");
        let b_idx = machine
            .coroutines
            .iter()
            .position(|c| c.role == "B")
            .expect("B coroutine exists");

        let ep_a = Endpoint {
            sid,
            role: "A".to_string(),
        };
        machine.coroutines[b_idx].owned_endpoints.push(ep_a.clone());
        machine.coroutines[a_idx].regs[2] = Value::Endpoint(ep_a);
        machine.coroutines[a_idx].regs[3] =
            Value::Nat(u64::try_from(machine.coroutines[b_idx].id).expect("coroutine id fits in u64"));

        let a_program_id = machine.coroutines[a_idx].program_id;
        machine.replace_program_for_test(a_program_id, vec![
            Instr::Transfer {
                endpoint: 2,
                target: 3,
                bundle: 0,
            },
            Instr::Halt,
        ]);

        let err = machine
            .step(&PassthroughHandler)
            .expect_err("transfer must fail");
        match err {
            ProtocolMachineError::Fault { fault, .. } => match fault {
                Fault::Transfer { message } => {
                    assert!(
                        message.contains("delegation guard violation before transfer"),
                        "unexpected transfer fault message: {message}"
                    );
                }
                other => panic!("expected transfer fault, got {other:?}"),
            },
            other => panic!("expected ProtocolMachineError::Fault, got {other:?}"),
        }
    }

    #[test]
    fn test_transfer_rejects_cross_session_target_and_preserves_source_state() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
        let sid1 = machine.load_choreography(&image).unwrap();
        let sid2 = machine.load_choreography(&image).unwrap();

        let a1_idx = machine
            .coroutines
            .iter()
            .position(|c| c.role == "A" && c.session_id == sid1)
            .expect("A coroutine for session 1 exists");
        let b2_idx = machine
            .coroutines
            .iter()
            .position(|c| c.role == "B" && c.session_id == sid2)
            .expect("B coroutine for session 2 exists");

        let ep_a = Endpoint {
            sid: sid1,
            role: "A".to_string(),
        };
        machine.coroutines[a1_idx].regs[2] = Value::Endpoint(ep_a.clone());
        machine.coroutines[a1_idx].regs[3] =
            Value::Nat(u64::try_from(machine.coroutines[b2_idx].id).expect("coroutine id fits in u64"));

        let a_program_id = machine.coroutines[a1_idx].program_id;
        machine.replace_program_for_test(a_program_id, vec![
            Instr::Transfer {
                endpoint: 2,
                target: 3,
                bundle: 0,
            },
            Instr::Halt,
        ]);

        let err = machine
            .step(&PassthroughHandler)
            .expect_err("cross-session transfer must fail");
        match err {
            ProtocolMachineError::Fault { fault, .. } => match fault {
                Fault::Transfer { message } => {
                    assert!(
                        message.contains("target coroutine session"),
                        "unexpected transfer fault message: {message}"
                    );
                }
                other => panic!("expected transfer fault, got {other:?}"),
            },
            other => panic!("expected ProtocolMachineError::Fault, got {other:?}"),
        }

        assert!(
            machine.coroutines[a1_idx].owned_endpoints.contains(&ep_a),
            "source endpoint ownership must remain intact on failed validation"
        );
        assert!(
            !machine.coroutines[b2_idx].owned_endpoints.contains(&ep_a),
            "cross-session target must not receive endpoint ownership"
        );
        assert!(
            machine.delegation_audit_log().is_empty(),
            "failed prevalidation should not emit a committed delegation record"
        );
    }

    #[test]
    fn test_load_choreography_owned_claims_owner_and_routes_mutation() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
        let owned = machine
            .load_choreography_owned(&image, "runtime/owner")
            .expect("owned open should succeed");
        assert_eq!(owned.capability().owner_id, "runtime/owner");
        assert_eq!(owned.capability().scope, OwnershipScope::Session);

        let edge = Edge::new(owned.session_id(), "A", "B");
        owned
            .apply_host_mutation(
                &mut machine,
                SessionHostMutation::UpdateTrace {
                    edge: edge.clone(),
                    trace: vec![ValType::Nat],
                },
            )
            .expect("owned mutation should succeed");
        assert_eq!(
            machine.sessions().lookup_trace(&edge),
            Some([ValType::Nat].as_slice())
        );
    }

    #[test]
    fn test_host_contract_assertions_reject_unaudited_transfer_events() {
        let machine = ProtocolMachine::new(ProtocolMachineConfig {
            host_contract_assertions: HostContractMode::Enforced,
            ..ProtocolMachineConfig::default()
        });
        let err = machine
            .assert_delegation_events_audited(&[ObsEvent::Transferred {
                tick: 0,
                session: 9,
                role: "A".to_string(),
                from: 1,
                to: 2,
            }])
            .expect_err("unaudited transfer event must fail host assertion");
        match err {
            ProtocolMachineError::HandlerError(message) => {
                assert!(
                    message
                        .message
                        .contains("matching committed delegation audit record"),
                    "unexpected error message: {message}"
                );
            }
            other => panic!("expected handler error, got {other:?}"),
        }
    }

    #[test]
    fn test_check_applies_flow_policy() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut denied_roles = BTreeSet::new();
        denied_roles.insert("Observer".to_string());
        let mut machine = ProtocolMachine::new(ProtocolMachineConfig {
            flow_policy: FlowPolicy::DenyRoles(denied_roles),
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
                fact: "secret".to_string(),
            });
        machine.coroutines[a_idx].regs[2] = Value::Prod(
            Box::new(Value::Endpoint(ep_a)),
            Box::new(Value::Str("secret".to_string())),
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
        // Intentionally discard StepResult: we only care that the step executes without panic
        let _ignored = machine.step(&handler).expect("check step should succeed");
        assert_eq!(machine.coroutines[a_idx].regs[4], Value::Bool(false));
    }
