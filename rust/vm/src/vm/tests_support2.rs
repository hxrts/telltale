
    #[derive(Default)]
    struct CallbackAuditHandler {
        send_decision_calls: AtomicUsize,
        handle_send_calls: AtomicUsize,
        handle_recv_calls: AtomicUsize,
        handle_choose_calls: AtomicUsize,
    }

    impl EffectHandler for CallbackAuditHandler {
        fn handle_send(
            &self,
            _role: &str,
            _partner: &str,
            _label: &str,
            _state: &[Value],
        ) -> Result<Value, String> {
            self.handle_send_calls.fetch_add(1, Ordering::Relaxed);
            Ok(Value::Nat(1))
        }

        fn send_decision(&self, input: SendDecisionInput<'_>) -> Result<SendDecision, String> {
            self.send_decision_calls.fetch_add(1, Ordering::Relaxed);
            Ok(SendDecision::Deliver(
                input.payload.unwrap_or(Value::Nat(1)),
            ))
        }

        fn handle_recv(
            &self,
            _role: &str,
            _partner: &str,
            _label: &str,
            _state: &mut Vec<Value>,
            _payload: &Value,
        ) -> Result<(), String> {
            self.handle_recv_calls.fetch_add(1, Ordering::Relaxed);
            Ok(())
        }

        fn handle_choose(
            &self,
            _role: &str,
            _partner: &str,
            labels: &[String],
            _state: &[Value],
        ) -> Result<String, String> {
            self.handle_choose_calls.fetch_add(1, Ordering::Relaxed);
            labels
                .first()
                .cloned()
                .ok_or_else(|| "no labels available".to_string())
        }

        fn step(&self, _role: &str, _state: &mut Vec<Value>) -> Result<(), String> {
            Ok(())
        }
    }

    struct AdversarialBoolSendHandler;

    impl EffectHandler for AdversarialBoolSendHandler {
        fn handle_send(
            &self,
            _role: &str,
            _partner: &str,
            _label: &str,
            _state: &[Value],
        ) -> Result<Value, String> {
            Ok(Value::Bool(true))
        }

        fn send_decision(&self, _input: SendDecisionInput<'_>) -> Result<SendDecision, String> {
            Ok(SendDecision::Deliver(Value::Bool(true)))
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

    struct OversizedPayloadSendHandler;

    impl EffectHandler for OversizedPayloadSendHandler {
        fn handle_send(
            &self,
            _role: &str,
            _partner: &str,
            _label: &str,
            _state: &[Value],
        ) -> Result<Value, String> {
            Ok(Value::Str("x".repeat(128)))
        }

        fn send_decision(&self, _input: SendDecisionInput<'_>) -> Result<SendDecision, String> {
            Ok(SendDecision::Deliver(Value::Str("x".repeat(128))))
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

    fn simple_send_recv_types() -> BTreeMap<String, LocalTypeR> {
        let mut m = BTreeMap::new();
        m.insert(
            "A".to_string(),
            LocalTypeR::Send {
                partner: "B".into(),
                branches: vec![(Label::new("msg"), None, LocalTypeR::End)],
            },
        );
        m.insert(
            "B".to_string(),
            LocalTypeR::Recv {
                partner: "A".into(),
                branches: vec![(Label::new("msg"), None, LocalTypeR::End)],
            },
        );
        m
    }

    fn typed_send_recv_types(expected: Option<ValType>) -> BTreeMap<String, LocalTypeR> {
        let mut m = BTreeMap::new();
        m.insert(
            "A".to_string(),
            LocalTypeR::Send {
                partner: "B".into(),
                branches: vec![(Label::new("msg"), expected.clone(), LocalTypeR::End)],
            },
        );
        m.insert(
            "B".to_string(),
            LocalTypeR::Recv {
                partner: "A".into(),
                branches: vec![(Label::new("msg"), expected, LocalTypeR::End)],
            },
        );
        m
    }

    fn choice_image_with_explicit_offer_choose() -> CodeImage {
        let mut local_types = BTreeMap::new();
        local_types.insert(
            "A".to_string(),
            LocalTypeR::Send {
                partner: "B".into(),
                branches: vec![
                    (Label::new("left"), None, LocalTypeR::End),
                    (Label::new("right"), None, LocalTypeR::End),
                ],
            },
        );
        local_types.insert(
            "B".to_string(),
            LocalTypeR::Recv {
                partner: "A".into(),
                branches: vec![
                    (Label::new("left"), None, LocalTypeR::End),
                    (Label::new("right"), None, LocalTypeR::End),
                ],
            },
        );

        let mut programs = BTreeMap::new();
        programs.insert(
            "A".to_string(),
            vec![
                Instr::Offer {
                    chan: 0,
                    label: "left".to_string(),
                },
                Instr::Halt,
            ],
        );
        programs.insert(
            "B".to_string(),
            vec![
                Instr::Choose {
                    chan: 0,
                    table: vec![("left".to_string(), 1), ("right".to_string(), 1)],
                },
                Instr::Halt,
            ],
        );

        CodeImage {
            programs,
            global_type: GlobalType::Comm {
                sender: "A".into(),
                receiver: "B".into(),
                branches: vec![
                    (Label::new("left"), GlobalType::End),
                    (Label::new("right"), GlobalType::End),
                ],
            },
            local_types,
        }
    }

