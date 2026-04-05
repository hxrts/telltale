    // Semantic state and session-store invariant tests.

    fn simple_send_recv_image() -> CodeImage {
        let mut local_types = BTreeMap::new();
        local_types.insert(
            "A".to_string(),
            LocalTypeR::Send {
                partner: "B".to_string(),
                branches: vec![(Label::new("m"), None, LocalTypeR::End)],
            },
        );
        local_types.insert(
            "B".to_string(),
            LocalTypeR::Recv {
                partner: "A".to_string(),
                branches: vec![(Label::new("m"), None, LocalTypeR::End)],
            },
        );
        let global = GlobalType::send("A", "B", Label::new("m"), GlobalType::End);
        CodeImage::from_local_types(&local_types, &global)
    }

    fn bool_send_recv_image() -> CodeImage {
        let mut local_types = BTreeMap::new();
        local_types.insert(
            "A".to_string(),
            LocalTypeR::Send {
                partner: "B".to_string(),
                branches: vec![
                    (
                        Label::new("m"),
                        Some(telltale_types::ValType::Bool),
                        LocalTypeR::End,
                    ),
                ],
            },
        );
        local_types.insert(
            "B".to_string(),
            LocalTypeR::Recv {
                partner: "A".to_string(),
                branches: vec![
                    (
                        Label::new("m"),
                        Some(telltale_types::ValType::Bool),
                        LocalTypeR::End,
                    ),
                ],
            },
        );
        let global = GlobalType::send("A", "B", Label::new("m"), GlobalType::End);
        CodeImage::from_local_types(&local_types, &global)
    }

    fn single_role_end_image(program: Vec<Instr>) -> CodeImage {
        CodeImage {
            programs: {
                let mut programs = BTreeMap::new();
                programs.insert("A".to_string(), program);
                programs
            },
            global_type: GlobalType::End,
            local_types: {
                let mut local_types = BTreeMap::new();
                local_types.insert("A".to_string(), LocalTypeR::End);
                local_types
            },
        }
    }

    struct SemanticStatePassthroughHandler;

    impl EffectHandler for SemanticStatePassthroughHandler {
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
            EffectResult::success(labels.first().cloned().expect("choice label"))
        }

        fn step(&self, _role: &str, _state: &mut Vec<Value>) -> EffectResult<()> {
            EffectResult::success(())
        }
    }

    struct PartitionOnTickZeroHandler;

    impl EffectHandler for PartitionOnTickZeroHandler {
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
            EffectResult::success(labels.first().cloned().expect("choice label"))
        }

        fn step(&self, _role: &str, _state: &mut Vec<Value>) -> EffectResult<()> {
            EffectResult::success(())
        }

        fn topology_events(&self, tick: u64) -> EffectResult<Vec<TopologyPerturbation>> {
            let events = match tick {
                1 => vec![TopologyPerturbation::Partition {
                    from: "A".to_string(),
                    to: "B".to_string(),
                }],
                2 => vec![TopologyPerturbation::Heal {
                    from: "A".to_string(),
                    to: "B".to_string(),
                }],
                _ => Vec::new(),
            };
            EffectResult::success(events)
        }
    }

    struct BlockedInvokeHandler;

    impl EffectHandler for BlockedInvokeHandler {
        fn handle_send(
            &self,
            _role: &str,
            _partner: &str,
            _label: &str,
            _state: &[Value],
        ) -> EffectResult<Value> {
            EffectResult::success(Value::Unit)
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
            EffectResult::success(labels.first().cloned().expect("choice label"))
        }

        fn step(&self, _role: &str, _state: &mut Vec<Value>) -> EffectResult<()> {
            EffectResult::Blocked
        }
    }

    struct FailingInvokeHandler;

    impl EffectHandler for FailingInvokeHandler {
        fn handle_send(
            &self,
            _role: &str,
            _partner: &str,
            _label: &str,
            _state: &[Value],
        ) -> EffectResult<Value> {
            EffectResult::success(Value::Unit)
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
            EffectResult::success(labels.first().cloned().expect("choice label"))
        }

        fn step(&self, _role: &str, _state: &mut Vec<Value>) -> EffectResult<()> {
            EffectResult::failure(EffectFailure::contract_violation("invoke failed"))
        }
    }

    struct MismatchedSendDecisionHandler;

    impl EffectHandler for MismatchedSendDecisionHandler {
        fn handle_send(
            &self,
            _role: &str,
            _partner: &str,
            _label: &str,
            _state: &[Value],
        ) -> EffectResult<Value> {
            EffectResult::success(Value::Unit)
        }

        fn send_decision(&self, _input: SendDecisionInput<'_>) -> EffectResult<SendDecision> {
            EffectResult::success(SendDecision::Deliver(Value::Nat(7)))
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
            EffectResult::success(labels.first().cloned().expect("choice label"))
        }

        fn step(&self, _role: &str, _state: &mut Vec<Value>) -> EffectResult<()> {
            EffectResult::success(())
        }
    }

    #[test]
    fn runtime_semantic_state_records_completed_operations() {
        let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
        machine.load_choreography(&simple_send_recv_image())
            .expect("load simple image");

        for _ in 0..4 {
            if matches!(
                machine.step(&SemanticStatePassthroughHandler),
                Ok(StepResult::AllDone)
            ) {
                break;
            }
        }

        assert!(
            machine.operation_instances()
                .iter()
                .any(|operation| operation.terminal_publication == Some("effect.succeeded".to_string())),
            "successful runtime effects should materialize terminal operation state"
        );
    }

    #[test]
    fn runtime_semantic_state_tracks_blocked_outstanding_effects() {
        let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
        machine.load_choreography(&simple_send_recv_image())
            .expect("load simple image");

        let step = machine
            .step(&PartitionOnTickZeroHandler)
            .expect("step simple image");
        assert!(matches!(step, StepResult::Continue));
        let blocked = machine
            .outstanding_effects()
            .iter()
            .find(|effect| effect.effect_kind == "send_decision")
            .expect("blocked send decision");
        assert_eq!(blocked.status, OutstandingEffectStatus::Blocked);
        assert!(machine.effect_trace().iter().all(|effect| effect.effect_id != blocked.effect_id));
    }

    #[test]
    fn runtime_semantic_state_rejects_late_results_without_live_effect() {
        let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
        let effect_id = machine.issue_runtime_effect(
            "invoke_step",
            None,
            "test/handler",
            serde_json::json!({ "session": 0 }),
        );
        machine.complete_runtime_effect(
            effect_id,
            OutstandingEffectStatus::Succeeded,
            serde_json::json!({ "status": "success" }),
        )
        .expect("complete live effect");

        let err = machine
            .complete_runtime_effect(
                effect_id,
                OutstandingEffectStatus::Succeeded,
                serde_json::json!({ "status": "success" }),
            )
            .expect_err("late result must be rejected");
        assert!(
            err.to_string().contains("late result"),
            "expected late-result rejection, got {err}"
        );
    }

    #[test]
    fn blocked_send_retry_preserves_original_blocked_effect_and_creates_new_success() {
        let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
        machine
            .load_choreography(&simple_send_recv_image())
            .expect("load simple image");

        let first = machine
            .step(&PartitionOnTickZeroHandler)
            .expect("initial blocked send step");
        assert!(matches!(first, StepResult::Continue));

        let blocked_send = machine
            .outstanding_effects()
            .iter()
            .find(|effect| effect.effect_kind == "send_decision")
            .expect("blocked send decision")
            .clone();
        assert_eq!(blocked_send.status, OutstandingEffectStatus::Blocked);

        for _ in 0..3 {
            let step = machine
                .step(&PartitionOnTickZeroHandler)
                .expect("retry/unblock step");
            assert!(matches!(step, StepResult::Continue | StepResult::AllDone | StepResult::Stuck));
            let send_count = machine
                .outstanding_effects()
                .iter()
                .filter(|effect| effect.effect_kind == "send_decision")
                .count();
            if send_count >= 2 {
                break;
            }
        }

        let send_effects: Vec<_> = machine
            .outstanding_effects()
            .iter()
            .filter(|effect| effect.effect_kind == "send_decision")
            .cloned()
            .collect();
        let send_exchanges: Vec<_> = machine
            .effect_exchanges()
            .iter()
            .filter(|exchange| {
                matches!(
                    exchange.request.body,
                    crate::effect::EffectRequestBody::SendDecision { .. }
                )
            })
            .collect();
        assert_eq!(
            send_exchanges.len(),
            2,
            "retry should issue one blocked exchange and one successful retry exchange"
        );
        assert!(
            send_effects.iter().any(|effect| effect.effect_id == blocked_send.effect_id
                && effect.status == OutstandingEffectStatus::Blocked),
            "original blocked effect must remain blocked"
        );
        assert!(
            send_effects.iter().any(|effect| effect.effect_id != blocked_send.effect_id
                && effect.status == OutstandingEffectStatus::Succeeded),
            "retry should create a new succeeded effect"
        );
        assert!(
            machine
                .effect_trace()
                .iter()
                .all(|effect| effect.effect_id != blocked_send.effect_id),
            "blocked effect must not leak a committed trace entry"
        );
    }

    #[test]
    fn blocked_invoke_observation_survives_contract_fault() {
        let image = single_role_end_image(vec![
            Instr::Invoke {
                action: InvokeAction::Reg(0),
            },
            Instr::Halt,
        ]);
        let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
        machine.load_choreography(&image).expect("load invoke image");

        let err = machine
            .step(&BlockedInvokeHandler)
            .expect_err("blocked invoke should fault");
        assert!(matches!(err, ProtocolMachineError::Fault { .. }));

        let invoke_exchange = machine
            .effect_exchanges()
            .iter()
            .find(|exchange| {
                matches!(
                    exchange.request.body,
                    crate::effect::EffectRequestBody::InvokeStep { .. }
                )
            })
            .expect("invoke observation should be recorded");
        assert!(matches!(
            invoke_exchange.outcome.status,
            crate::effect::EffectOutcomeStatus::Blocked
        ));

        let invoke_effect = machine
            .outstanding_effects()
            .iter()
            .find(|effect| effect.effect_kind == "invoke_step")
            .expect("blocked invoke effect");
        assert_eq!(invoke_effect.status, OutstandingEffectStatus::Blocked);
        assert!(
            machine
                .effect_trace()
                .iter()
                .all(|effect| effect.effect_id != invoke_effect.effect_id),
            "blocked invoke must not leak a committed trace entry"
        );
        assert!(
            machine.operation_instances().iter().any(|operation| {
                operation.operation_id == invoke_effect.operation_id
                    && operation.phase == OperationPhase::Blocked
                    && operation.terminal_publication.as_deref() == Some("effect.blocked")
            }),
            "blocked invoke should remain blocked in semantic operation state"
        );
    }

    #[test]
    fn failed_invoke_observation_survives_fault_path() {
        let image = single_role_end_image(vec![
            Instr::Invoke {
                action: InvokeAction::Reg(0),
            },
            Instr::Halt,
        ]);
        let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
        machine.load_choreography(&image).expect("load invoke image");

        let err = machine
            .step(&FailingInvokeHandler)
            .expect_err("failing invoke should fault");
        assert!(matches!(err, ProtocolMachineError::Fault { .. }));

        let invoke_exchange = machine
            .effect_exchanges()
            .iter()
            .find(|exchange| {
                matches!(
                    exchange.request.body,
                    crate::effect::EffectRequestBody::InvokeStep { .. }
                )
            })
            .expect("failed invoke observation should be recorded");
        assert!(matches!(
            invoke_exchange.outcome.status,
            crate::effect::EffectOutcomeStatus::Failure { .. }
        ));

        let invoke_effect = machine
            .outstanding_effects()
            .iter()
            .find(|effect| effect.effect_kind == "invoke_step")
            .expect("failed invoke effect");
        assert_eq!(invoke_effect.status, OutstandingEffectStatus::Failed);
        assert!(
            machine
                .effect_trace()
                .iter()
                .all(|effect| effect.effect_id != invoke_effect.effect_id),
            "failed invoke must not leak a committed trace entry"
        );
    }

    #[test]
    fn successful_send_observation_survives_later_validation_fault() {
        let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
        machine
            .load_choreography(&bool_send_recv_image())
            .expect("load typed send image");

        let err = machine
            .step(&MismatchedSendDecisionHandler)
            .expect_err("payload mismatch should fault");
        assert!(matches!(err, ProtocolMachineError::Fault { .. }));

        let send_exchange = machine
            .effect_exchanges()
            .iter()
            .find(|exchange| {
                matches!(
                    exchange.request.body,
                    crate::effect::EffectRequestBody::SendDecision { .. }
                )
            })
            .expect("send observation should be recorded");
        assert!(matches!(
            send_exchange.outcome.status,
            crate::effect::EffectOutcomeStatus::Success
        ));

        let send_effect = machine
            .outstanding_effects()
            .iter()
            .find(|effect| effect.effect_kind == "send_decision")
            .expect("send effect should survive validation fault");
        assert_eq!(send_effect.status, OutstandingEffectStatus::Succeeded);
        assert!(
            machine.effect_trace().is_empty(),
            "later validation fault must prevent committed trace entries"
        );
    }
