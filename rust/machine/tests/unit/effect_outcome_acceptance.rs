use super::*;

#[test]
fn all_nine_request_kinds_require_their_exact_success_response() {
    let sync = crate::durable::WalSyncRequest {
        operation_id: "original".into(),
        downstream_coroutine_id: "coro:0".into(),
        gate_level: crate::semantic_objects::AgreementLevel::None,
        agreement_state: None,
        agreement_evidence: vec![],
        tick: 0,
    };
    let requests = [
        EffectRequest::send_decision(0, 1, None, "A", "B", "m", &[], None),
        EffectRequest::receive(0, Some(1), None, "A", "B", "m", &[], Value::Unit),
        EffectRequest::choose(0, Some(1), None, "A", "B", &[], &[]),
        EffectRequest::invoke_step(0, Some(1), None, "A", &[]),
        EffectRequest::acquire(0, 1, None, "A", "guard", &[]),
        EffectRequest::release(0, 1, None, "A", "guard", &Value::Unit, &[]),
        EffectRequest::topology_events(0),
        EffectRequest::wal_sync(0, "original", sync),
        EffectRequest::output_condition_hint(0, 1, None, "A", &[]),
    ];
    let responses = [
        EffectResponse::SendDecision {
            decision: SendDecision::Deliver(Value::Unit),
        },
        EffectResponse::Receive { state: vec![] },
        EffectResponse::Choose { label: "m".into() },
        EffectResponse::InvokeStep { state: vec![] },
        EffectResponse::Acquire {
            evidence: Value::Unit,
        },
        EffectResponse::Release,
        EffectResponse::TopologyEvents { events: vec![] },
        EffectResponse::WalSync,
        EffectResponse::OutputConditionHint { hint: None },
    ];
    for (request_index, request) in requests.iter().enumerate() {
        for (response_index, response) in responses.iter().enumerate() {
            let outcome = EffectOutcome::success(response.clone());
            assert_eq!(
                outcome.accepted_status(&request.body).is_success(),
                request_index == response_index
            );
            let exchange = EffectExchangeRecord {
                effect_id: 0,
                handler_identity: "original".into(),
                ordering_key: 0,
                request: request.clone(),
                outcome,
            };
            assert_eq!(exchange.succeeded(), request_index == response_index);
            for policy in [
                EffectCompositionPolicy::All,
                EffectCompositionPolicy::First,
                EffectCompositionPolicy::Threshold {
                    required_successes: 1,
                },
            ] {
                assert_eq!(
                    policy.commitment_resolved(std::slice::from_ref(&exchange)),
                    request_index == response_index
                );
            }
        }
        let missing = EffectOutcome {
            status: EffectOutcomeStatus::Success,
            response: None,
        };
        assert!(!missing.accepted_status(&request.body).is_success());
    }
    assert_instruction_context_and_original_failure();
}

fn assert_instruction_context_and_original_failure() {
    let plain = EffectRequest::receive(0, Some(1), None, "A", "B", "m", &[], Value::Unit);
    let empty = EffectOutcome::success(EffectResponse::Receive { state: vec![] });
    // Branch receive / wrapper calls perform no destination-register write.
    assert!(empty.accepted_status(&plain.body).is_success());
    let legacy = serde_json::to_value(&plain).unwrap();
    assert!(legacy["body"].get("destination").is_none());
    let decoded: EffectRequest = serde_json::from_value(legacy).unwrap();
    assert_eq!(decoded, plain);
    let actual = plain.with_receive_destination(1);
    assert!(!empty.accepted_status(&actual.body).is_success());
    assert!(empty.into_receive_state_for(&actual.body).is_err());
    let resized = EffectOutcome::success(EffectResponse::Receive {
        state: vec![Value::Unit, Value::Unit],
    });
    assert!(resized.accepted_status(&actual.body).is_success());
    // Handler-only context permits resizing; actual VM configured width does not.
    let actual = actual.with_register_width(4);
    assert!(!resized.accepted_status(&actual.body).is_success());
    assert!(resized.into_receive_state_for(&actual.body).is_err());
    let failure = EffectFailure::denied("original malformed-state refusal");
    let original_message = failure.message.as_ptr();
    let failed = EffectOutcome {
        status: EffectOutcomeStatus::Failure { failure },
        response: Some(EffectResponse::Receive { state: vec![] }),
    };
    let EffectResult::Failure(retained) = failed.into_receive_state_for(&actual.body).unwrap()
    else {
        panic!("original failure required")
    };
    assert_eq!(retained.message.as_ptr(), original_message);
}

#[test]
fn typed_state_extraction_preserves_original_failure_before_attached_response() {
    for receive in [false, true] {
        let failure = EffectFailure::denied("original owned typed failure");
        let original_message = failure.message.as_ptr();
        let outcome = EffectOutcome {
            status: EffectOutcomeStatus::Failure { failure },
            response: Some(EffectResponse::InvokeStep {
                state: vec![Value::Nat(999)],
            }),
        };
        let result = if receive {
            outcome.into_receive_state()
        } else {
            outcome.into_invoke_state()
        }
        .unwrap();
        let EffectResult::Failure(retained) = result else {
            panic!("original failure required")
        };
        assert_eq!(retained.message.as_ptr(), original_message);
        assert_eq!(retained.kind, EffectFailureKind::Denied);
        let blocked = EffectOutcome {
            status: EffectOutcomeStatus::Blocked,
            response: Some(EffectResponse::InvokeStep {
                state: vec![Value::Nat(999)],
            }),
        };
        let result = if receive {
            blocked.into_receive_state()
        } else {
            blocked.into_invoke_state()
        }
        .unwrap();
        assert!(matches!(result, EffectResult::Blocked));
    }
}

#[test]
fn unit_conversion_cannot_accept_a_different_unit_like_response() {
    let kinds = ["handle_recv", "invoke_step", "handle_release", "wal_sync"];
    let responses = [
        EffectResponse::Receive { state: vec![] },
        EffectResponse::InvokeStep { state: vec![] },
        EffectResponse::Release,
        EffectResponse::WalSync,
    ];
    for (expected, name) in kinds.iter().enumerate() {
        for (actual, response) in responses.iter().enumerate() {
            assert_eq!(
                EffectOutcome::success(response.clone())
                    .into_unit(name)
                    .is_ok(),
                actual == expected
            );
        }
    }
}

#[test]
fn replay_state_updates_require_the_original_successful_response() {
    for receive in [false, true] {
        for outcome in [
            EffectOutcome {
                status: EffectOutcomeStatus::Failure {
                    failure: EffectFailure::denied("original replay refusal"),
                },
                response: Some(EffectResponse::InvokeStep {
                    state: vec![Value::Nat(999)],
                }),
            },
            EffectOutcome {
                status: EffectOutcomeStatus::Blocked,
                response: Some(EffectResponse::Receive {
                    state: vec![Value::Nat(999)],
                }),
            },
        ] {
            let tape = EffectTraceTape::new();
            let state = vec![Value::Nat(7)];
            let request = if receive {
                EffectRequest::receive(0, None, None, "A", "B", "m", &state, Value::Unit)
            } else {
                EffectRequest::invoke_step(0, None, None, "A", &state)
            };
            tape.record_exchange(request, outcome.clone(), "original", None);
            let replay = ReplayEffectHandler::new(tape.entries());
            let mut actual = state.clone();
            let original_allocation = actual.as_ptr();
            let result = if receive {
                replay.handle_recv("A", "B", "m", &mut actual, &Value::Unit)
            } else {
                replay.step("A", &mut actual)
            };
            assert!(!matches!(result, EffectResult::Success(())));
            assert_eq!(actual, state);
            assert_eq!(actual.as_ptr(), original_allocation);
        }
    }
}

#[cfg(not(target_arch = "wasm32"))]
mod concurrent_recording {
    use super::*;
    use std::sync::Condvar;

    #[derive(Default)]
    struct Gate {
        state: Mutex<(bool, bool, bool)>,
        changed: Condvar,
    }
    impl Gate {
        fn recorded_and_wait(&self) {
            let mut state = self.state.lock().unwrap_or_else(|p| p.into_inner());
            state.0 = true;
            self.changed.notify_all();
            while !state.1 {
                state = self.changed.wait(state).unwrap_or_else(|p| p.into_inner());
            }
        }
        fn release(&self) {
            self.state.lock().unwrap_or_else(|p| p.into_inner()).1 = true;
            self.changed.notify_all();
        }
        fn completed(&self) {
            self.state.lock().unwrap_or_else(|p| p.into_inner()).2 = true;
            self.changed.notify_all();
        }
        fn entered_or_completed(&self) -> bool {
            let mut state = self.state.lock().unwrap_or_else(|p| p.into_inner());
            while !state.0 && !state.2 {
                state = self.changed.wait(state).unwrap_or_else(|p| p.into_inner());
            }
            state.0
        }
    }
    struct Release<'a>(&'a Gate);
    impl Drop for Release<'_> {
        fn drop(&mut self) {
            self.0.release();
        }
    }
    struct Complete<'a>(&'a Gate);
    impl Drop for Complete<'_> {
        fn drop(&mut self) {
            self.0.completed();
        }
    }
    struct Replies;
    impl EffectHandler for Replies {
        fn handle_effect(&self, request: EffectRequest) -> EffectOutcome {
            match request.body {
                EffectRequestBody::InvokeStep { role, .. } => {
                    EffectOutcome::success(EffectResponse::InvokeStep {
                        state: vec![Value::Nat(if role == "A" { 1 } else { 2 })],
                    })
                }
                EffectRequestBody::Receive { role, .. } => {
                    EffectOutcome::success(EffectResponse::Receive {
                        state: vec![Value::Nat(if role == "A" { 1 } else { 2 })],
                    })
                }
                _ => unreachable!("actual state-bearing requests only"),
            }
        }
        fn handle_send(&self, _: &str, _: &str, _: &str, _: &[Value]) -> EffectResult<Value> {
            unreachable!()
        }
        fn handle_recv(
            &self,
            _: &str,
            _: &str,
            _: &str,
            _: &mut Vec<Value>,
            _: &Value,
        ) -> EffectResult<()> {
            unreachable!()
        }
        fn handle_choose(
            &self,
            _: &str,
            _: &str,
            _: &[String],
            _: &[Value],
        ) -> EffectResult<String> {
            unreachable!()
        }
        fn step(&self, _: &str, _: &mut Vec<Value>) -> EffectResult<()> {
            unreachable!()
        }
    }

    #[test]
    fn actual_interleaved_recording_never_substitutes_the_other_returned_state() {
        for receive in [false, true] {
            let gate = Gate::default();
            let observe = |request: &EffectRequest| {
                let role = match &request.body {
                    EffectRequestBody::InvokeStep { role, .. }
                    | EffectRequestBody::Receive { role, .. } => role,
                    _ => unreachable!(),
                };
                if role == "A" {
                    gate.recorded_and_wait();
                }
            };
            let mut wrapper = RecordingEffectHandler::new(&Replies);
            wrapper.after_record = Some(&observe);
            std::thread::scope(|scope| {
                let release = Release(&gate);
                let first = scope.spawn(|| {
                    let _complete = Complete(&gate);
                    let mut state = vec![Value::Nat(0)];
                    let result = if receive {
                        wrapper.handle_recv("A", "B", "m", &mut state, &Value::Unit)
                    } else {
                        wrapper.step("A", &mut state)
                    };
                    (result, state)
                });
                let actual_recorded_pending = gate.entered_or_completed();
                let mut second_state = vec![Value::Nat(0)];
                let second = if receive {
                    wrapper.handle_recv("B", "A", "m", &mut second_state, &Value::Unit)
                } else {
                    wrapper.step("B", &mut second_state)
                };
                drop(release);
                let first = first.join();
                assert!(actual_recorded_pending);
                let (result, first_state) = first.unwrap();
                assert!(matches!(result, EffectResult::Success(())));
                assert!(matches!(second, EffectResult::Success(())));
                assert_eq!(first_state, vec![Value::Nat(1)]);
                assert_eq!(second_state, vec![Value::Nat(2)]);
                assert_eq!(wrapper.effect_exchanges().len(), 2);
            });
        }
    }
}
