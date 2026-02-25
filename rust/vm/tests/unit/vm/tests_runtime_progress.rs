    #[test]
    fn test_vm_simple_send_recv() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut vm = VM::new(VMConfig::default());
        let _sid = vm.load_choreography(&image).unwrap();

        let handler = PassthroughHandler;
        vm.run(&handler, 100).unwrap();

        // Both coroutines should be done.
        assert!(vm.coroutines.iter().all(|c| c.is_terminal()));
    }

    #[test]
    fn test_canonical_dispatch_uses_send_decision_and_handle_recv() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut vm = VM::new(VMConfig::default());
        vm.load_choreography(&image).expect("load choreography");
        let handler = CallbackAuditHandler::default();
        vm.run(&handler, 100).expect("run should succeed");

        assert!(handler.send_decision_calls.load(Ordering::Relaxed) > 0);
        assert!(handler.handle_recv_calls.load(Ordering::Relaxed) > 0);
        assert_eq!(handler.handle_send_calls.load(Ordering::Relaxed), 0);
    }

    #[test]
    fn test_canonical_dispatch_does_not_call_handle_choose() {
        let image = choice_image_with_explicit_offer_choose();
        let mut vm = VM::new(VMConfig::default());
        vm.load_choreography(&image).expect("load choreography");
        let handler = CallbackAuditHandler::default();
        vm.run(&handler, 100).expect("run should succeed");

        assert_eq!(handler.handle_choose_calls.load(Ordering::Relaxed), 0);
        assert!(handler.send_decision_calls.load(Ordering::Relaxed) > 0);
        assert!(handler.handle_recv_calls.load(Ordering::Relaxed) > 0);
    }

    #[test]
    fn test_payload_validation_structural_rejects_annotated_type_mismatch() {
        let local_types = typed_send_recv_types(Some(ValType::Nat));
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut vm = VM::new(VMConfig {
            payload_validation_mode: PayloadValidationMode::Structural,
            ..VMConfig::default()
        });
        vm.load_choreography(&image).expect("load choreography");

        let err = vm
            .run(&AdversarialBoolSendHandler, 100)
            .expect_err("annotated payload type mismatch should fault");
        match err {
            VMError::Fault {
                fault:
                    Fault::TypeViolation {
                        expected, actual, ..
                    },
                ..
            } => {
                assert_eq!(expected, ValType::Nat);
                assert_eq!(actual, ValType::Bool);
            }
            other => panic!("unexpected error: {other:?}"),
        }
    }

    #[test]
    fn test_payload_validation_off_allows_annotated_type_mismatch_for_compatibility() {
        let local_types = typed_send_recv_types(Some(ValType::Nat));
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut vm = VM::new(VMConfig {
            payload_validation_mode: PayloadValidationMode::Off,
            ..VMConfig::default()
        });
        vm.load_choreography(&image).expect("load choreography");
        vm.run(&AdversarialBoolSendHandler, 100)
            .expect("off mode preserves compatibility behavior");
    }

    #[test]
    fn test_payload_validation_strict_schema_requires_annotations_for_send_recv() {
        let local_types = typed_send_recv_types(None);
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut vm = VM::new(VMConfig {
            payload_validation_mode: PayloadValidationMode::StrictSchema,
            ..VMConfig::default()
        });
        vm.load_choreography(&image).expect("load choreography");

        let err = vm
            .run(&PassthroughHandler, 100)
            .expect_err("strict schema mode should require explicit payload annotations");
        match err {
            VMError::Fault {
                fault: Fault::TypeViolation { message, .. },
                ..
            } => {
                assert!(message.contains("requires explicit ValType annotation"));
            }
            other => panic!("unexpected error: {other:?}"),
        }
    }

    #[test]
    fn test_payload_validation_size_bound_rejects_oversized_payloads() {
        let local_types = typed_send_recv_types(None);
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut vm = VM::new(VMConfig {
            max_payload_bytes: 16,
            ..VMConfig::default()
        });
        vm.load_choreography(&image).expect("load choreography");

        let err = vm
            .run(&OversizedPayloadSendHandler, 100)
            .expect_err("payload above max_payload_bytes should fault");
        match err {
            VMError::Fault {
                fault: Fault::TypeViolation { message, .. },
                ..
            } => {
                assert!(message.contains("exceeds max_payload_bytes"));
            }
            other => panic!("unexpected error: {other:?}"),
        }
    }

    #[test]
    fn test_step_round_advances_at_most_one_coroutine_when_concurrency_gt_one() {
        let mut local_types = BTreeMap::new();
        local_types.insert("A".to_string(), LocalTypeR::End);
        local_types.insert("B".to_string(), LocalTypeR::End);

        let mut programs = BTreeMap::new();
        programs.insert("A".to_string(), vec![Instr::Halt]);
        programs.insert("B".to_string(), vec![Instr::Halt]);

        let image = CodeImage {
            programs,
            global_type: GlobalType::End,
            local_types,
        };

        let mut vm = VM::new(VMConfig::default());
        vm.load_choreography(&image).expect("load choreography");
        let handler = PassthroughHandler;

        assert_eq!(vm.scheduler_step_count(), 0);
        let first = vm.step_round(&handler, 8).expect("first round");
        assert!(matches!(first, StepResult::Continue));
        assert_eq!(vm.scheduler_step_count(), 1);
        assert_eq!(
            vm.coroutines
                .iter()
                .filter(|c| matches!(c.status, CoroStatus::Done))
                .count(),
            1
        );

        let second = vm.step_round(&handler, 8).expect("second round");
        assert!(matches!(second, StepResult::AllDone));
        assert_eq!(vm.scheduler_step_count(), 2);
    }

    #[test]
    fn test_step_round_with_no_eligible_coroutines_does_not_increment_step_count() {
        let mut local_types = BTreeMap::new();
        local_types.insert("A".to_string(), LocalTypeR::End);

        let mut programs = BTreeMap::new();
        programs.insert("A".to_string(), vec![Instr::Halt]);

        let image = CodeImage {
            programs,
            global_type: GlobalType::End,
            local_types,
        };

        let mut vm = VM::new(VMConfig::default());
        vm.load_choreography(&image).expect("load choreography");
        vm.pause_role("A");
        let handler = PassthroughHandler;

        assert_eq!(vm.scheduler_step_count(), 0);
        let result = vm.step_round(&handler, 1).expect("step round");
        assert!(matches!(result, StepResult::Stuck));
        assert_eq!(vm.scheduler_step_count(), 0);
    }

    #[test]
    fn test_yield_advances_pc_and_sets_spawn_wait_blocked_status() {
        let mut local_types = BTreeMap::new();
        local_types.insert("A".to_string(), LocalTypeR::End);

        let mut programs = BTreeMap::new();
        programs.insert("A".to_string(), vec![Instr::Yield, Instr::Halt]);

        let image = CodeImage {
            programs,
            global_type: GlobalType::End,
            local_types,
        };

        let mut vm = VM::new(VMConfig::default());
        vm.load_choreography(&image).expect("load choreography");
        let handler = PassthroughHandler;

        let first = vm.step_round(&handler, 1).expect("yield step");
        assert!(matches!(first, StepResult::Continue));
        let coro = vm.coroutine(0).expect("coroutine exists");
        assert_eq!(coro.pc, 1);
        assert!(matches!(
            coro.status,
            CoroStatus::Blocked(BlockReason::Spawn)
        ));

        let second = vm.step_round(&handler, 1).expect("halt step");
        assert!(matches!(second, StepResult::AllDone));
    }

    #[test]
    fn test_run_status_reports_all_done_stuck_and_max_rounds_exceeded() {
        let all_done_image = CodeImage {
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
        let mut all_done_vm = VM::new(VMConfig::default());
        all_done_vm
            .load_choreography(&all_done_image)
            .expect("load all-done choreography");
        let all_done = all_done_vm
            .run(&PassthroughHandler, 8)
            .expect("all-done run must succeed");
        assert_eq!(all_done, RunStatus::AllDone);

        let stuck_image = CodeImage {
            programs: {
                let mut m = BTreeMap::new();
                m.insert("A".to_string(), vec![Instr::Receive { chan: 0, dst: 1 }]);
                m
            },
            global_type: GlobalType::End,
            local_types: {
                let mut m = BTreeMap::new();
                m.insert(
                    "A".to_string(),
                    LocalTypeR::recv("B", Label::new("m"), LocalTypeR::End),
                );
                m
            },
        };
        let mut stuck_vm = VM::new(VMConfig::default());
        stuck_vm
            .load_choreography(&stuck_image)
            .expect("load stuck choreography");
        let stuck = stuck_vm
            .run(&PassthroughHandler, 8)
            .expect("stuck run must return status, not fault");
        assert_eq!(stuck, RunStatus::Stuck);

        let max_image = CodeImage {
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
        let mut max_vm = VM::new(VMConfig::default());
        max_vm
            .load_choreography(&max_image)
            .expect("load loop choreography");
        let exhausted = max_vm
            .run(&PassthroughHandler, 8)
            .expect("bounded loop run must return status");
        assert_eq!(exhausted, RunStatus::MaxRoundsExceeded);
    }

    fn open_test_image(open_instr: Instr) -> CodeImage {
        let mut local_types = BTreeMap::new();
        local_types.insert("A".to_string(), LocalTypeR::End);
        let mut programs = BTreeMap::new();
        programs.insert("A".to_string(), vec![open_instr, Instr::Halt]);
        CodeImage {
            programs,
            global_type: GlobalType::End,
            local_types,
        }
    }

    fn open_buffer_pressure_image() -> CodeImage {
        let full_handlers = vec![
            (("A".to_string(), "A".to_string()), "hAA".to_string()),
            (("A".to_string(), "B".to_string()), "hAB".to_string()),
            (("B".to_string(), "A".to_string()), "hBA".to_string()),
            (("B".to_string(), "B".to_string()), "hBB".to_string()),
        ];
        let send_twice = LocalTypeR::send(
            "B",
            Label::new("m"),
            LocalTypeR::send("B", Label::new("m"), LocalTypeR::End),
        );
        let recv_twice = LocalTypeR::recv(
            "A",
            Label::new("m"),
            LocalTypeR::recv("A", Label::new("m"), LocalTypeR::End),
        );
        let mut local_types = BTreeMap::new();
        local_types.insert("A".to_string(), LocalTypeR::End);
        let mut programs = BTreeMap::new();
        programs.insert(
            "A".to_string(),
            vec![
                Instr::Open {
                    roles: vec!["A".to_string(), "B".to_string()],
                    local_types: vec![("A".to_string(), send_twice), ("B".to_string(), recv_twice)],
                    handlers: full_handlers,
                    dsts: vec![("A".to_string(), 1), ("B".to_string(), 2)],
                },
                Instr::Set {
                    dst: 3,
                    val: crate::instr::ImmValue::Nat(7),
                },
                Instr::Send { chan: 1, val: 3 },
                Instr::Send { chan: 1, val: 3 },
                Instr::Halt,
            ],
        );
        CodeImage {
            programs,
            global_type: GlobalType::End,
            local_types,
        }
    }

    #[test]
    fn test_open_faults_on_arity_mismatch() {
        let image = open_test_image(Instr::Open {
            roles: vec!["A".to_string()],
            local_types: vec![("A".to_string(), LocalTypeR::End)],
            handlers: vec![(("A".to_string(), "A".to_string()), "h".to_string())],
            dsts: vec![("B".to_string(), 0)],
        });

        let mut vm = VM::new(VMConfig::default());
        vm.load_choreography(&image).expect("load choreography");
        let handler = PassthroughHandler;

        let err = vm
            .step_round(&handler, 1)
            .expect_err("expected open arity fault");
        match err {
            VMError::Fault {
                fault: Fault::Close { message },
                ..
            } => assert_eq!(message, "open arity mismatch"),
            other => panic!("unexpected error: {other:?}"),
        }
    }

    #[test]
    fn test_open_faults_when_handler_coverage_is_incomplete() {
        let image = open_test_image(Instr::Open {
            roles: vec!["A".to_string(), "B".to_string()],
            local_types: vec![
                ("A".to_string(), LocalTypeR::End),
                ("B".to_string(), LocalTypeR::End),
            ],
            handlers: vec![(("A".to_string(), "B".to_string()), "h".to_string())],
            dsts: vec![("A".to_string(), 0), ("B".to_string(), 1)],
        });

        let mut vm = VM::new(VMConfig::default());
        vm.load_choreography(&image).expect("load choreography");
        let handler = PassthroughHandler;

        let err = vm
            .step_round(&handler, 1)
            .expect_err("expected handler coverage fault");
        match err {
            VMError::Fault {
                fault: Fault::Speculation { message },
                ..
            } => assert_eq!(message, "handler bindings missing"),
            other => panic!("unexpected error: {other:?}"),
        }
    }

    #[test]
    fn test_open_initializes_local_types_handlers_and_endpoints() {
        let full_handlers = vec![
            (("A".to_string(), "A".to_string()), "hAA".to_string()),
            (("A".to_string(), "B".to_string()), "hAB".to_string()),
            (("B".to_string(), "A".to_string()), "hBA".to_string()),
            (("B".to_string(), "B".to_string()), "hBB".to_string()),
        ];
        let image = open_test_image(Instr::Open {
            roles: vec!["A".to_string(), "B".to_string()],
            local_types: vec![
                ("A".to_string(), LocalTypeR::End),
                ("B".to_string(), LocalTypeR::End),
            ],
            handlers: full_handlers.clone(),
            dsts: vec![("A".to_string(), 0), ("B".to_string(), 1)],
        });

        let mut vm = VM::new(VMConfig::default());
        vm.load_choreography(&image).expect("load choreography");
        let handler = PassthroughHandler;

        let result = vm.step_round(&handler, 1).expect("open step");
        assert!(matches!(result, StepResult::Continue));

        let sid = match vm
            .trace()
            .iter()
            .rev()
            .find(|event| matches!(event, ObsEvent::Opened { .. }))
            .expect("opened event emitted")
        {
            ObsEvent::Opened { session, .. } => *session,
            _ => unreachable!(),
        };
        let session = vm.sessions().get(sid).expect("opened session exists");
        assert_eq!(session.local_types.len(), 2);
        for ((sender, receiver), handler_id) in full_handlers {
            let edge = Edge::new(sid, sender, receiver);
            assert_eq!(session.edge_handlers.get(&edge), Some(&handler_id));
        }

        let coro = vm.coroutine(0).expect("coroutine exists");
        assert!(matches!(coro.regs[0], Value::Endpoint(_)));
        assert!(matches!(coro.regs[1], Value::Endpoint(_)));
    }

    #[test]
    fn test_runtime_open_uses_configured_buffer_capacity_for_new_sessions() {
        let image = open_buffer_pressure_image();
        let cfg = VMConfig {
            buffer_config: BufferConfig {
                mode: crate::buffer::BufferMode::Fifo,
                initial_capacity: 1,
                policy: crate::buffer::BackpressurePolicy::Error,
            },
            ..VMConfig::default()
        };
        let mut vm = VM::new(cfg);
        vm.load_choreography(&image).expect("load choreography");
        let err = vm
            .run(&PassthroughHandler, 32)
            .expect_err("second open-session send must fault with capacity=1,error policy");
        match err {
            VMError::Fault {
                fault: Fault::BufferFull { .. },
                ..
            } => {}
            other => panic!("expected BufferFull fault, got {other:?}"),
        }
    }

    #[test]
    fn test_runtime_open_allocates_session_id_after_loaded_session_without_collision() {
        let full_handlers = vec![
            (("A".to_string(), "A".to_string()), "hAA".to_string()),
            (("A".to_string(), "B".to_string()), "hAB".to_string()),
            (("B".to_string(), "A".to_string()), "hBA".to_string()),
            (("B".to_string(), "B".to_string()), "hBB".to_string()),
        ];
        let image = open_test_image(Instr::Open {
            roles: vec!["A".to_string(), "B".to_string()],
            local_types: vec![
                ("A".to_string(), LocalTypeR::End),
                ("B".to_string(), LocalTypeR::End),
            ],
            handlers: full_handlers,
            dsts: vec![("A".to_string(), 0), ("B".to_string(), 1)],
        });

        let mut vm = VM::new(VMConfig::default());
        let sid0 = vm.load_choreography(&image).expect("load choreography");
        assert_eq!(sid0, 0);

        let handler = PassthroughHandler;
        let result = vm.step_round(&handler, 1).expect("open step");
        assert!(matches!(result, StepResult::Continue));

        let opened: Vec<SessionId> = vm
            .trace()
            .iter()
            .filter_map(|event| match event {
                ObsEvent::Opened { session, .. } => Some(*session),
                _ => None,
            })
            .collect();
        assert_eq!(opened, vec![0, 1], "expected monotonic opened sessions");
        assert!(
            vm.sessions().get(0).is_some(),
            "bootstrap session must remain"
        );
        assert!(
            vm.sessions().get(1).is_some(),
            "runtime-open session must exist"
        );
        assert_eq!(vm.next_session_id(), 2);
    }

    #[test]
    fn test_monitor_precheck_rejects_duplicate_choose_labels() {
        let image = open_test_image(Instr::Choose {
            chan: 0,
            table: vec![("L".to_string(), 0), ("L".to_string(), 1)],
        });
        let mut vm = VM::new(VMConfig::default());
        vm.load_choreography(&image).expect("load choreography");
        let handler = PassthroughHandler;

        let err = vm
            .step_round(&handler, 1)
            .expect_err("duplicate labels must fail monitor precheck");
        match err {
            VMError::Fault {
                fault: Fault::Speculation { message },
                ..
            } => assert!(message.contains("duplicate choose labels")),
            other => panic!("unexpected error: {other:?}"),
        }
    }

