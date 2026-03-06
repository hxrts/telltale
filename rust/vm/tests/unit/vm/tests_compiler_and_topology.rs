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

        let mut vm = VM::new(VMConfig::default());
        let _sid = vm.load_choreography(&image).unwrap();

        let handler = PassthroughHandler;
        vm.run(&handler, 100).unwrap();

        assert!(vm.coroutines.iter().all(|c| c.is_terminal()));
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

        let mut vm = VM::new(VMConfig::default());
        let _sid = vm.load_choreography(&image).unwrap();

        let handler = PassthroughHandler;
        // Don't unwrap — just run to completion
        let _ignored = vm.run(&handler, 500);

        let faults: Vec<_> = vm
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

        let mut vm = VM::new(VMConfig {
            output_condition_policy: OutputConditionPolicy::DenyAll,
            ..VMConfig::default()
        });
        let _sid = vm.load_choreography(&image).unwrap();

        let handler = PassthroughHandler;
        let result = vm.run(&handler, 10);
        assert!(result.is_err());
        assert!(
            matches!(
                result,
                Err(VMError::Fault {
                    fault: Fault::OutputCondition { .. },
                    ..
                })
            ),
            "expected output-condition fault, got: {result:?}"
        );
        assert!(vm
            .output_condition_checks()
            .iter()
            .any(|c| c.meta.predicate_ref == "vm.observable_output" && !c.passed));
    }

    #[test]
    fn test_output_condition_allowlist_accepts_default_predicate() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut vm = VM::new(VMConfig {
            output_condition_policy: OutputConditionPolicy::PredicateAllowList(vec![
                "vm.observable_output".to_string(),
            ]),
            ..VMConfig::default()
        });
        let _sid = vm.load_choreography(&image).unwrap();

        let handler = PassthroughHandler;
        vm.run(&handler, 100).unwrap();
        assert!(vm
            .output_condition_checks()
            .iter()
            .any(|c| c.meta.predicate_ref == "vm.observable_output" && c.passed));
    }

    #[test]
    fn test_effect_trace_records_committed_effects() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut vm = VM::new(VMConfig::default());
        let _sid = vm.load_choreography(&image).unwrap();
        let handler = PassthroughHandler;
        vm.run(&handler, 100).unwrap();

        let kinds: Vec<_> = vm
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

        let mut vm = VM::new(VMConfig {
            effect_trace_capture_mode: EffectTraceCaptureMode::Disabled,
            ..VMConfig::default()
        });
        vm.load_choreography(&image).expect("load choreography");
        vm.run(&PassthroughHandler, 100)
            .expect("run should succeed");

        assert!(vm.effect_trace().is_empty());
    }

    #[test]
    fn test_effect_trace_capture_mode_topology_only_filters_runtime_effects() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut vm = VM::new(VMConfig {
            effect_trace_capture_mode: EffectTraceCaptureMode::TopologyOnly,
            ..VMConfig::default()
        });
        vm.load_choreography(&image).expect("load choreography");
        vm.run(&TimeoutOnTickOneHandler, 100)
            .expect("run should succeed");

        assert!(!vm.effect_trace().is_empty());
        assert!(vm
            .effect_trace()
            .iter()
            .all(|entry| entry.effect_kind == "topology_event"));
    }

    #[test]
    fn test_host_contract_assertions_reject_handler_identity_flips() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut vm = VM::new(VMConfig {
            host_contract_assertions: true,
            ..VMConfig::default()
        });
        vm.load_choreography(&image).expect("load choreography");

        let err = vm
            .step(&IdentityFlappingHandler::new())
            .expect_err("identity change should fail with assertions enabled");
        match err {
            VMError::HandlerError(message) => {
                assert!(message.contains("handler_identity changed"));
            }
            VMError::Fault {
                fault: Fault::Invoke { message },
                ..
            } => {
                assert!(message.contains("handler_identity changed"));
            }
            other => panic!("unexpected error: {other:?}"),
        }
    }

    #[test]
    fn test_host_contract_assertions_reject_unsorted_topology_inputs() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut vm = VM::new(VMConfig {
            host_contract_assertions: true,
            ..VMConfig::default()
        });
        vm.load_choreography(&image).expect("load choreography");

        let err = vm
            .step(&UnsortedTopologyHandler)
            .expect_err("unsorted topology events should fail with assertions enabled");
        match err {
            VMError::HandlerError(message) => {
                assert!(message.contains("topology_events"));
                assert!(message.contains("pre-sorted"));
            }
            other => panic!("unexpected error: {other:?}"),
        }
    }

    #[test]
    fn test_transfer_moves_progress_tokens_with_endpoint() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut vm = VM::new(VMConfig::default());
        let sid = vm.load_choreography(&image).unwrap();

        let a_idx = vm
            .coroutines
            .iter()
            .position(|c| c.role == "A")
            .expect("A coroutine exists");
        let b_idx = vm
            .coroutines
            .iter()
            .position(|c| c.role == "B")
            .expect("B coroutine exists");

        let ep_a = Endpoint {
            sid,
            role: "A".to_string(),
        };
        vm.coroutines[a_idx]
            .progress_tokens
            .push(ProgressToken::for_endpoint(ep_a.clone()));
        vm.coroutines[a_idx].regs[2] = Value::Endpoint(ep_a.clone());
        vm.coroutines[a_idx].regs[3] =
            Value::Nat(u64::try_from(vm.coroutines[b_idx].id).expect("coroutine id fits in u64"));

        let a_program_id = vm.coroutines[a_idx].program_id;
        vm.replace_program_for_test(a_program_id, vec![
            Instr::Transfer {
                endpoint: 2,
                target: 3,
                bundle: 0,
            },
            Instr::Halt,
        ]);

        let handler = PassthroughHandler;
        // Intentionally discard StepResult: we only care that the step executes without panic
        let _ignored = vm.step(&handler).expect("transfer step should succeed");

        assert!(vm.coroutines[a_idx].progress_tokens.is_empty());
        assert!(vm.coroutines[b_idx]
            .progress_tokens
            .iter()
            .any(|t| t.sid == sid && t.endpoint == ep_a));
    }

    #[test]
    fn test_transfer_rejects_delegation_guard_violation() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut vm = VM::new(VMConfig::default());
        let sid = vm.load_choreography(&image).unwrap();

        let a_idx = vm
            .coroutines
            .iter()
            .position(|c| c.role == "A")
            .expect("A coroutine exists");
        let b_idx = vm
            .coroutines
            .iter()
            .position(|c| c.role == "B")
            .expect("B coroutine exists");

        let ep_a = Endpoint {
            sid,
            role: "A".to_string(),
        };
        vm.coroutines[b_idx].owned_endpoints.push(ep_a.clone());
        vm.coroutines[a_idx].regs[2] = Value::Endpoint(ep_a);
        vm.coroutines[a_idx].regs[3] =
            Value::Nat(u64::try_from(vm.coroutines[b_idx].id).expect("coroutine id fits in u64"));

        let a_program_id = vm.coroutines[a_idx].program_id;
        vm.replace_program_for_test(a_program_id, vec![
            Instr::Transfer {
                endpoint: 2,
                target: 3,
                bundle: 0,
            },
            Instr::Halt,
        ]);

        let err = vm
            .step(&PassthroughHandler)
            .expect_err("transfer must fail");
        match err {
            VMError::Fault { fault, .. } => match fault {
                Fault::Transfer { message } => {
                    assert!(
                        message.contains("delegation guard violation before transfer"),
                        "unexpected transfer fault message: {message}"
                    );
                }
                other => panic!("expected transfer fault, got {other:?}"),
            },
            other => panic!("expected VMError::Fault, got {other:?}"),
        }
    }

    #[test]
    fn test_check_applies_flow_policy() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut denied_roles = BTreeSet::new();
        denied_roles.insert("Observer".to_string());
        let mut vm = VM::new(VMConfig {
            flow_policy: FlowPolicy::DenyRoles(denied_roles),
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
                fact: "secret".to_string(),
            });
        vm.coroutines[a_idx].regs[2] = Value::Prod(
            Box::new(Value::Endpoint(ep_a)),
            Box::new(Value::Str("secret".to_string())),
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
        // Intentionally discard StepResult: we only care that the step executes without panic
        let _ignored = vm.step(&handler).expect("check step should succeed");
        assert_eq!(vm.coroutines[a_idx].regs[4], Value::Bool(false));
    }
