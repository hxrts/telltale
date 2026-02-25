    #[test]
    fn test_monitor_precheck_rejects_open_role_dst_arity_mismatch() {
        let image = open_test_image(Instr::Open {
            roles: vec!["A".to_string(), "B".to_string()],
            local_types: vec![("A".to_string(), LocalTypeR::End)],
            handlers: vec![(("A".to_string(), "A".to_string()), "h".to_string())],
            dsts: vec![("A".to_string(), 0)],
        });

        let mut vm = VM::new(VMConfig::default());
        vm.load_choreography(&image).expect("load choreography");
        let handler = PassthroughHandler;

        let err = vm
            .step_round(&handler, 1)
            .expect_err("open monitor precheck should fail");
        match err {
            VMError::Fault {
                fault: Fault::Speculation { message },
                ..
            } => assert!(message.contains("open arity mismatch")),
            other => panic!("unexpected error: {other:?}"),
        }
    }

    #[test]
    fn test_invoke_faults_when_no_default_handler_is_bound() {
        let image = open_test_image(Instr::Invoke {
            action: InvokeAction::Reg(0),
            dst: Some(1),
        });
        let mut vm = VM::new(VMConfig::default());
        let sid = vm.load_choreography(&image).expect("load choreography");
        vm.sessions_mut()
            .get_mut(sid)
            .expect("session exists")
            .edge_handlers
            .clear();
        let handler = PassthroughHandler;

        let err = vm
            .step_round(&handler, 1)
            .expect_err("invoke should fault without default handler");
        match err {
            VMError::Fault {
                fault: Fault::Invoke { message },
                ..
            } => assert_eq!(message, "no handler bound"),
            other => panic!("unexpected error: {other:?}"),
        }
    }

    #[test]
    fn test_invoke_applies_persistence_delta_when_model_provides_one() {
        let mut vm: VM<(), (), RecordingPersistence, DefaultVerificationModel> =
            VM::new_with_models(VMConfig::default());
        vm.apply_open_delta(0).expect("open delta");
        vm.apply_invoke_delta(0, "Nat(7)").expect("invoke delta");

        assert!(
            vm.persistent_state().iter().any(|d| d.starts_with("open:")),
            "expected open delta to be applied"
        );
        assert!(
            vm.persistent_state()
                .iter()
                .any(|d| d.starts_with("invoke:0:Nat(7)")),
            "expected invoke delta with action witness"
        );
    }

    #[test]
    fn test_close_applies_persistence_delta_when_model_provides_one() {
        let mut vm: VM<(), (), RecordingPersistence, DefaultVerificationModel> =
            VM::new_with_models(VMConfig::default());
        vm.apply_close_delta(0).expect("close delta");
        assert!(
            vm.persistent_state()
                .iter()
                .any(|d| d.starts_with("close:0")),
            "expected close delta to be applied"
        );
    }

    #[test]
    fn test_output_condition_digest_matches_lean_placeholder() {
        let image = open_test_image(Instr::Invoke {
            action: InvokeAction::Reg(0),
            dst: Some(1),
        });
        let mut vm = VM::new(VMConfig::default());
        vm.load_choreography(&image).expect("load choreography");
        let handler = PassthroughHandler;

        vm.step_round(&handler, 1).expect("invoke step");
        let check = vm
            .output_condition_checks()
            .last()
            .expect("output-condition check recorded");
        assert_eq!(check.meta.output_digest, "vm.output_digest.unspecified");
    }

    #[test]
    fn test_vm_recursive_protocol() {
        // mu step. A!B:msg. B!A:msg. var step
        let mut local_types = BTreeMap::new();
        local_types.insert(
            "A".to_string(),
            LocalTypeR::mu(
                "step",
                LocalTypeR::Send {
                    partner: "B".into(),
                    branches: vec![(
                        Label::new("msg"),
                        None,
                        LocalTypeR::Recv {
                            partner: "B".into(),
                            branches: vec![(Label::new("msg"), None, LocalTypeR::var("step"))],
                        },
                    )],
                },
            ),
        );
        local_types.insert(
            "B".to_string(),
            LocalTypeR::mu(
                "step",
                LocalTypeR::Recv {
                    partner: "A".into(),
                    branches: vec![(
                        Label::new("msg"),
                        None,
                        LocalTypeR::Send {
                            partner: "A".into(),
                            branches: vec![(Label::new("msg"), None, LocalTypeR::var("step"))],
                        },
                    )],
                },
            ),
        );

        let global = GlobalType::mu(
            "step",
            GlobalType::send(
                "A",
                "B",
                Label::new("msg"),
                GlobalType::send("B", "A", Label::new("msg"), GlobalType::var("step")),
            ),
        );
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut vm = VM::new(VMConfig::default());
        let _sid = vm.load_choreography(&image).unwrap();

        let handler = PassthroughHandler;
        // Run for enough steps to exercise several loop iterations.
        vm.run(&handler, 200).unwrap();

        // Should not fault — recursive protocol with blocking should work.
        assert!(vm
            .coroutines
            .iter()
            .all(|c| !matches!(c.status, CoroStatus::Faulted(_))));
    }

    #[test]
    fn test_vm_blocking_does_not_advance_type() {
        // Set up a protocol where B must recv before A sends.
        // B: recv, then send. A: send, then recv.
        // B will block on recv until A sends.
        let mut local_types = BTreeMap::new();
        local_types.insert(
            "A".to_string(),
            LocalTypeR::Send {
                partner: "B".into(),
                branches: vec![(Label::new("msg"), None, LocalTypeR::End)],
            },
        );
        local_types.insert(
            "B".to_string(),
            LocalTypeR::Recv {
                partner: "A".into(),
                branches: vec![(Label::new("msg"), None, LocalTypeR::End)],
            },
        );

        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut vm = VM::new(VMConfig::default());
        let sid = vm.load_choreography(&image).unwrap();

        let handler = PassthroughHandler;

        // Step once: scheduler picks first ready coro (A or B).
        // If B is picked first, it should block (no message yet).
        // Type should NOT advance on block.
        let ep_b = Endpoint {
            sid,
            role: "B".into(),
        };
        let type_before = vm.sessions.lookup_type(&ep_b).cloned();

        // Run to completion.
        vm.run(&handler, 100).unwrap();
        assert!(vm.coroutines.iter().all(|c| c.is_terminal()));

        // Verify B's type was Recv before execution.
        assert!(matches!(type_before, Some(LocalTypeR::Recv { .. })));
    }

    #[test]
    fn test_blocked_step_has_no_type_or_trace_side_effects() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut vm = VM::new(VMConfig::default());
        let sid = vm.load_choreography(&image).unwrap();
        vm.pause_role("A");

        let ep_b = Endpoint {
            sid,
            role: "B".to_string(),
        };
        let type_before = vm.sessions.lookup_type(&ep_b).cloned();
        let trace_len_before = vm.obs_trace().len();
        let b_pc_before = vm
            .coroutines
            .iter()
            .find(|c| c.role == "B")
            .expect("B coroutine exists")
            .pc;

        let handler = PassthroughHandler;
        let step_result = vm.step(&handler).expect("step should succeed");
        assert!(matches!(step_result, StepResult::Continue));

        let type_after = vm.sessions.lookup_type(&ep_b).cloned();
        let b_coro_after = vm
            .coroutines
            .iter()
            .find(|c| c.role == "B")
            .expect("B coroutine exists");

        assert_eq!(type_before, type_after, "blocked step advanced type state");
        assert_eq!(b_pc_before, b_coro_after.pc, "blocked step advanced PC");
        assert!(
            matches!(b_coro_after.status, CoroStatus::Blocked(_)),
            "blocked step did not block coroutine"
        );
        assert_eq!(
            trace_len_before,
            vm.obs_trace().len(),
            "blocked step emitted observable events"
        );
    }

    #[test]
    fn test_faulted_step_does_not_advance_type_state() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut vm = VM::new(VMConfig::default());
        let sid = vm.load_choreography(&image).unwrap();
        vm.pause_role("B");

        let ep_a = Endpoint {
            sid,
            role: "A".to_string(),
        };
        let type_before = vm.sessions.lookup_type(&ep_a).cloned();

        let handler = FailingSendHandler;
        let result = vm.step(&handler);
        assert!(matches!(result, Err(VMError::Fault { .. })));

        let type_after = vm.sessions.lookup_type(&ep_a).cloned();
        assert_eq!(type_before, type_after, "faulted step advanced type state");
        assert!(
            vm.obs_trace()
                .iter()
                .any(|event| matches!(event, ObsEvent::Faulted { .. })),
            "faulted step must emit Faulted trace event"
        );
    }

    #[test]
    fn test_sent_event_matches_committed_session_transition() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut vm = VM::new(VMConfig::default());
        let sid = vm.load_choreography(&image).unwrap();
        vm.pause_role("B");

        let ep_a = Endpoint {
            sid,
            role: "A".to_string(),
        };

        let handler = PassthroughHandler;
        vm.step(&handler).expect("single send step should succeed");

        let session = vm.sessions().get(sid).expect("session should exist");
        assert!(
            session.has_message("A", "B"),
            "committed send must enqueue message"
        );
        assert!(
            vm.obs_trace().iter().any(|event| {
                matches!(
                    event,
                    ObsEvent::Sent {
                        session: ev_sid,
                        from,
                        to,
                        label,
                        ..
                    } if *ev_sid == sid && from == "A" && to == "B" && label == "msg"
                )
            }),
            "committed send must emit matching Sent trace event"
        );
        assert!(
            matches!(vm.sessions.lookup_type(&ep_a), Some(LocalTypeR::End)),
            "committed send must advance sender type"
        );
    }

    #[test]
    fn test_vm_load_multiple_sessions() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);

        let image1 = CodeImage::from_local_types(&local_types, &global);
        let image2 = CodeImage::from_local_types(&local_types, &global);

        let mut vm = VM::new(VMConfig::default());
        let sid1 = vm.load_choreography(&image1).unwrap();
        let sid2 = vm.load_choreography(&image2).unwrap();

        assert_ne!(sid1, sid2);
        assert_eq!(vm.coroutines.len(), 4);

        let handler = PassthroughHandler;
        vm.run(&handler, 200).unwrap();
        assert!(vm.coroutines.iter().all(|c| c.is_terminal()));
    }

    #[test]
    fn test_vm_choice_protocol() {
        // A chooses "yes" or "no", B offers (receives the choice).
        // A: Send { B, [yes → End, no → End] }
        // B: Recv { A, [yes → End, no → End] }
        let mut local_types = BTreeMap::new();
        local_types.insert(
            "A".to_string(),
            LocalTypeR::send_choice(
                "B",
                vec![
                    (Label::new("yes"), None, LocalTypeR::End),
                    (Label::new("no"), None, LocalTypeR::End),
                ],
            ),
        );
        local_types.insert(
            "B".to_string(),
            LocalTypeR::recv_choice(
                "A",
                vec![
                    (Label::new("yes"), None, LocalTypeR::End),
                    (Label::new("no"), None, LocalTypeR::End),
                ],
            ),
        );

        let global = GlobalType::comm(
            "A",
            "B",
            vec![
                (Label::new("yes"), GlobalType::End),
                (Label::new("no"), GlobalType::End),
            ],
        );

        // Manually compile: A offers a label, B chooses from table.
        let a_code = vec![
            Instr::Offer {
                chan: 0,
                label: "yes".into(),
            },
            Instr::Halt,
        ];
        let b_code = vec![
            Instr::Choose {
                chan: 0,
                table: vec![("yes".into(), 1), ("no".into(), 2)],
            },
            Instr::Halt, // yes branch
            Instr::Halt, // no branch
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

        // Verify events include Sent (from Choose) and Received (from Offer).
        let sent = vm
            .obs_trace
            .iter()
            .any(|e| matches!(e, ObsEvent::Sent { label, .. } if label == "yes"));
        let recv = vm
            .obs_trace
            .iter()
            .any(|e| matches!(e, ObsEvent::Received { label, .. } if label == "yes"));
        assert!(sent, "expected Sent event with label 'yes'");
        assert!(recv, "expected Received event with label 'yes'");
    }

    #[test]
    fn test_vm_offer_blocks_until_choice() {
        // B tries to Offer before A has Chosen → should block.
        let mut local_types = BTreeMap::new();
        local_types.insert(
            "A".to_string(),
            LocalTypeR::send_choice("B", vec![(Label::new("go"), None, LocalTypeR::End)]),
        );
        local_types.insert(
            "B".to_string(),
            LocalTypeR::recv_choice("A", vec![(Label::new("go"), None, LocalTypeR::End)]),
        );

        let global = GlobalType::send("A", "B", Label::new("go"), GlobalType::End);

        let a_code = vec![
            Instr::Offer {
                chan: 0,
                label: "go".into(),
            },
            Instr::Halt,
        ];
        let b_code = vec![
            Instr::Choose {
                chan: 0,
                table: vec![("go".into(), 1)],
            },
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
    fn test_vm_close_session() {
        // Simple: A sends to B, then closes.
        let mut local_types = BTreeMap::new();
        local_types.insert(
            "A".to_string(),
            LocalTypeR::Send {
                partner: "B".into(),
                branches: vec![(Label::new("msg"), None, LocalTypeR::End)],
            },
        );
        local_types.insert(
            "B".to_string(),
            LocalTypeR::Recv {
                partner: "A".into(),
                branches: vec![(Label::new("msg"), None, LocalTypeR::End)],
            },
        );

        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);

        // A: Send, Close, Halt.  B: Recv, Close, Halt.
        let a_code = vec![
            Instr::Send { chan: 0, val: 1 },
            Instr::Close { session: 0 },
            Instr::Halt,
        ];
        let b_code = vec![
            Instr::Receive { chan: 0, dst: 1 },
            Instr::Close { session: 0 },
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
        let closed_count = vm
            .obs_trace
            .iter()
            .filter(|e| matches!(e, ObsEvent::Closed { .. }))
            .count();
        assert!(closed_count >= 1, "expected at least one Closed event");
    }

