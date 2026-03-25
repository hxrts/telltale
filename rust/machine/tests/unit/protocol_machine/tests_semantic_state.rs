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
            if tick <= 1 {
                EffectResult::success(vec![TopologyPerturbation::Partition {
                    from: "A".to_string(),
                    to: "B".to_string(),
                }])
            } else {
                EffectResult::success(Vec::new())
            }
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
