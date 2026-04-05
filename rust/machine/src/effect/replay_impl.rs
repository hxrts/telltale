// Replay effect handler that replays recorded effect exchanges.
impl EffectHandler for ReplayEffectHandler<'_> {
    fn handler_identity(&self) -> String {
        "replay_handler".to_string()
    }

    #[allow(clippy::too_many_lines)]
    fn handle_effect(&self, request: EffectRequest) -> EffectOutcome {
        let expected_kind = match &request.body {
            EffectRequestBody::SendDecision { .. } => "send_decision",
            EffectRequestBody::Receive { .. } => "handle_recv",
            EffectRequestBody::Choose { .. } => "handle_choose",
            EffectRequestBody::InvokeStep { .. } => "invoke_step",
            EffectRequestBody::Acquire { .. } => "handle_acquire",
            EffectRequestBody::Release { .. } => "handle_release",
            EffectRequestBody::TopologyEvents { .. } => "topology_events",
            EffectRequestBody::WalSync { .. } => "wal_sync",
            EffectRequestBody::OutputConditionHint { .. } => "output_condition_hint",
        };
        let entry = match self.next_entry(expected_kind) {
            Ok(entry) => entry,
            Err(message) => return EffectOutcome::failure(EffectFailure::determinism(message)),
        };
        if let Ok(outcome) = serde_json::from_value::<EffectOutcome>(entry.outputs.clone()) {
            return outcome;
        }

        match expected_kind {
            "send_decision" => {
                let payload = match &request.body {
                    EffectRequestBody::SendDecision { payload, .. } => payload.clone(),
                    _ => None,
                };
                if let Some(outcome) = Self::parse_send_decision(&entry.outputs, payload) {
                    return match outcome {
                        EffectResult::Success(decision) => {
                            EffectOutcome::success(EffectResponse::SendDecision { decision })
                        }
                        EffectResult::Blocked => EffectOutcome::blocked(),
                        EffectResult::Failure(failure) => EffectOutcome::failure(failure),
                    };
                }
            }
            "handle_recv" | "invoke_step" | "handle_release" | "wal_sync" => {
                if let Some(outcome) = decode_effect_result::<()>(&entry.outputs) {
                    return match outcome {
                        EffectResult::Success(()) => match request.body {
                            EffectRequestBody::Receive { state, .. } => {
                                EffectOutcome::success(EffectResponse::Receive { state })
                            }
                            EffectRequestBody::InvokeStep { state, .. } => {
                                EffectOutcome::success(EffectResponse::InvokeStep { state })
                            }
                            EffectRequestBody::WalSync { .. } => {
                                EffectOutcome::success(EffectResponse::WalSync)
                            }
                            _ => EffectOutcome::success(EffectResponse::Release),
                        },
                        EffectResult::Blocked => EffectOutcome::blocked(),
                        EffectResult::Failure(failure) => EffectOutcome::failure(failure),
                    };
                }
            }
            "handle_choose" => {
                if let Some(outcome) = decode_effect_result::<String>(&entry.outputs) {
                    return match outcome {
                        EffectResult::Success(label) => {
                            EffectOutcome::success(EffectResponse::Choose { label })
                        }
                        EffectResult::Blocked => EffectOutcome::blocked(),
                        EffectResult::Failure(failure) => EffectOutcome::failure(failure),
                    };
                }
            }
            "handle_acquire" => {
                if let Some(outcome) = decode_effect_result::<Value>(&entry.outputs) {
                    return match outcome {
                        EffectResult::Success(evidence) => {
                            EffectOutcome::success(EffectResponse::Acquire { evidence })
                        }
                        EffectResult::Blocked => EffectOutcome::blocked(),
                        EffectResult::Failure(failure) => EffectOutcome::failure(failure),
                    };
                }
            }
            "topology_events" => {
                if let Some(outcome) = decode_effect_result::<Vec<TopologyPerturbation>>(&entry.outputs) {
                    return match outcome {
                        EffectResult::Success(events) => {
                            EffectOutcome::success(EffectResponse::TopologyEvents { events })
                        }
                        EffectResult::Blocked => EffectOutcome::blocked(),
                        EffectResult::Failure(failure) => EffectOutcome::failure(failure),
                    };
                }
            }
            "output_condition_hint" => {
                return EffectOutcome::success(EffectResponse::OutputConditionHint {
                    hint: self.fallback.and_then(|fallback| match request.body {
                        EffectRequestBody::OutputConditionHint { role, state } => request
                            .session
                            .and_then(|sid| fallback.output_condition_hint(sid, &role, &state)),
                        _ => None,
                    }),
                });
            }
            _ => {}
        }

        if let Some(fallback) = self.fallback {
            return fallback.handle_effect(request);
        }

        EffectOutcome::failure(EffectFailure::determinism(format!(
            "replay {expected_kind} missing typed outcome"
        )))
    }

    fn handle_send(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        state: &[Value],
    ) -> EffectResult<Value> {
        if let Some(fallback) = self.fallback {
            fallback.handle_send(role, partner, label, state)
        } else {
            EffectResult::success(Value::Unit)
        }
    }

    fn send_decision(&self, input: SendDecisionInput<'_>) -> EffectResult<SendDecision> {
        self.handle_effect(EffectRequest::send_decision(
            0,
            input.sid,
            None,
            input.role,
            input.partner,
            input.label,
            input.state,
            input.payload,
        ))
        .into_send_decision()
        .unwrap_or_else(EffectResult::failure)
    }

    fn handle_recv(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        state: &mut Vec<Value>,
        payload: &Value,
    ) -> EffectResult<()> {
        let outcome = self.handle_effect(EffectRequest::receive(
            0,
            None,
            None,
            role,
            partner,
            label,
            state,
            payload.clone(),
        ));
        if let Some(EffectResponse::Receive { state: new_state }) = outcome.response.clone() {
            *state = new_state;
        }
        outcome
            .into_unit("handle_recv")
            .unwrap_or_else(EffectResult::failure)
    }

    fn handle_choose(
        &self,
        role: &str,
        partner: &str,
        labels: &[String],
        state: &[Value],
    ) -> EffectResult<String> {
        self.handle_effect(EffectRequest::choose(
            0,
            None,
            None,
            role,
            partner,
            labels,
            state,
        ))
        .into_label()
        .unwrap_or_else(EffectResult::failure)
    }

    fn step(&self, role: &str, state: &mut Vec<Value>) -> EffectResult<()> {
        let outcome = self.handle_effect(EffectRequest::invoke_step(0, None, None, role, state));
        if let Some(EffectResponse::InvokeStep { state: new_state }) = outcome.response.clone() {
            *state = new_state;
        }
        outcome
            .into_unit("invoke_step")
            .unwrap_or_else(EffectResult::failure)
    }

    fn handle_acquire(
        &self,
        sid: SessionId,
        role: &str,
        layer: &str,
        state: &[Value],
    ) -> EffectResult<Value> {
        self.handle_effect(EffectRequest::acquire(0, sid, None, role, layer, state))
            .into_value("acquire")
            .unwrap_or_else(EffectResult::failure)
    }

    fn handle_release(
        &self,
        sid: SessionId,
        role: &str,
        layer: &str,
        evidence: &Value,
        state: &[Value],
    ) -> EffectResult<()> {
        self.handle_effect(EffectRequest::release(0, sid, None, role, layer, evidence, state))
            .into_unit("handle_release")
            .unwrap_or_else(EffectResult::failure)
    }

    fn topology_events(&self, tick: u64) -> EffectResult<Vec<TopologyPerturbation>> {
        self.handle_effect(EffectRequest::topology_events(tick))
            .into_topology()
            .unwrap_or_else(EffectResult::failure)
    }

    fn output_condition_hint(
        &self,
        sid: SessionId,
        role: &str,
        state: &[Value],
    ) -> Option<OutputConditionHint> {
        self.handle_effect(EffectRequest::output_condition_hint(0, sid, None, role, state))
            .into_output_condition_hint()
            .ok()
            .flatten()
    }

    fn supports_wal_sync(&self) -> bool {
        true
    }

    fn wal_sync(&self, sync: &crate::durable::WalSyncRequest) -> EffectResult<()> {
        self.handle_effect(EffectRequest::wal_sync(
            sync.tick,
            sync.operation_id.clone(),
            sync.clone(),
        ))
        .into_unit("wal_sync")
        .unwrap_or_else(EffectResult::failure)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};

    struct AlternatingHandler {
        counter: AtomicUsize,
    }

    impl AlternatingHandler {
        fn new() -> Self {
            Self {
                counter: AtomicUsize::new(0),
            }
        }
    }

    impl EffectHandler for AlternatingHandler {
        fn handle_send(
            &self,
            _role: &str,
            _partner: &str,
            _label: &str,
            _state: &[Value],
        ) -> EffectResult<Value> {
            EffectResult::success(Value::Nat(1))
        }

        #[allow(clippy::as_conversions, clippy::cast_possible_wrap)]
        fn send_decision(&self, input: SendDecisionInput<'_>) -> EffectResult<SendDecision> {
            let idx = self.counter.fetch_add(1, Ordering::Relaxed);
            if idx % 2 == 0 {
                EffectResult::success(SendDecision::Deliver(
                    input.payload.unwrap_or(Value::Nat(idx as u64)),
                ))
            } else {
                EffectResult::success(SendDecision::Drop)
            }
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
                None => EffectResult::failure(EffectFailure::invalid_input("no labels")),
            }
        }

        fn step(&self, _role: &str, _state: &mut Vec<Value>) -> EffectResult<()> {
            EffectResult::success(())
        }
    }

    #[test]
    fn recording_and_replay_send_decisions_roundtrip() {
        let base = AlternatingHandler::new();
        let recorder = RecordingEffectHandler::new(&base);

        let first = recorder
            .send_decision(SendDecisionInput {
                sid: 0,
                role: "A",
                partner: "B",
                label: "m",
                state: &[],
                payload: Some(Value::Nat(7)),
            })
            .expect_success(|| EffectFailure::contract_violation("decision blocked"))
            .expect("first decision");
        let second = recorder
            .send_decision(SendDecisionInput {
                sid: 0,
                role: "A",
                partner: "B",
                label: "m",
                state: &[],
                payload: Some(Value::Nat(8)),
            })
            .expect_success(|| EffectFailure::contract_violation("decision blocked"))
            .expect("second decision");
        assert!(matches!(first, SendDecision::Deliver(_)));
        assert!(matches!(second, SendDecision::Drop));

        let replay = ReplayEffectHandler::new(recorder.effect_trace());
        let replay_first = replay
            .send_decision(SendDecisionInput {
                sid: 0,
                role: "A",
                partner: "B",
                label: "m",
                state: &[],
                payload: Some(Value::Nat(0)),
            })
            .expect_success(|| EffectFailure::contract_violation("decision blocked"))
            .expect("replay first decision");
        let replay_second = replay
            .send_decision(SendDecisionInput {
                sid: 0,
                role: "A",
                partner: "B",
                label: "m",
                state: &[],
                payload: Some(Value::Nat(0)),
            })
            .expect_success(|| EffectFailure::contract_violation("decision blocked"))
            .expect("replay second decision");
        assert!(matches!(replay_first, SendDecision::Deliver(_)));
        assert!(matches!(replay_second, SendDecision::Drop));
        assert_eq!(replay.remaining(), 0);
    }

    #[test]
    fn typed_effect_outcomes_serialize_and_roundtrip() {
        let blocked_json = serde_json::json!({
            "status": "blocked",
        });
        let blocked = decode_effect_result::<SendDecision>(&blocked_json)
            .expect("blocked outcome should decode");
        assert!(matches!(blocked, EffectResult::Blocked));

        let failure_json = serde_json::json!({
            "status": "failure",
            "failure": EffectFailure::timeout("send timed out"),
        });
        let failure = decode_effect_result::<SendDecision>(&failure_json)
            .expect("failure outcome should decode");
        assert_eq!(
            failure,
            EffectResult::Failure(EffectFailure::timeout("send timed out"))
        );
    }

    #[test]
    fn recording_and_replay_topology_events_roundtrip() {
        struct TopologyOnce {
            emitted: AtomicUsize,
        }

        impl EffectHandler for TopologyOnce {
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
                match labels.first().cloned() {
                    Some(label) => EffectResult::success(label),
                    None => EffectResult::failure(EffectFailure::invalid_input("no labels")),
                }
            }

            fn step(&self, _role: &str, _state: &mut Vec<Value>) -> EffectResult<()> {
                EffectResult::success(())
            }

            fn topology_events(&self, _tick: u64) -> EffectResult<Vec<TopologyPerturbation>> {
                let idx = self.emitted.fetch_add(1, Ordering::Relaxed);
                if idx == 0 {
                    EffectResult::success(vec![TopologyPerturbation::Crash {
                        site: "node-a".to_string(),
                    }])
                } else {
                    EffectResult::success(Vec::new())
                }
            }
        }

        let base = TopologyOnce {
            emitted: AtomicUsize::new(0),
        };
        let recorder = RecordingEffectHandler::new(&base);
        let first = recorder
            .topology_events(1)
            .expect_success(|| EffectFailure::contract_violation("topology blocked"))
            .expect("record topology");
        let second = recorder
            .topology_events(2)
            .expect_success(|| EffectFailure::contract_violation("topology blocked"))
            .expect("record topology");
        assert_eq!(first.len(), 1);
        assert!(second.is_empty());

        let replay = ReplayEffectHandler::new(recorder.effect_trace());
        let replay_first = replay
            .topology_events(1)
            .expect_success(|| EffectFailure::contract_violation("topology blocked"))
            .expect("replay topology");
        let replay_second = replay
            .topology_events(2)
            .expect_success(|| EffectFailure::contract_violation("topology blocked"))
            .expect("replay topology");
        assert_eq!(replay_first.len(), 1);
        assert!(replay_second.is_empty());
        assert_eq!(replay.remaining(), 0);
    }

    #[test]
    fn effect_failure_constructors_preserve_typed_kinds() {
        assert_eq!(
            EffectFailure::timeout("timed out waiting for recv").kind,
            EffectFailureKind::Timeout
        );
        assert_eq!(
            EffectFailure::topology_disruption("topology partition mismatch").kind,
            EffectFailureKind::TopologyDisruption
        );
        assert_eq!(
            EffectFailure::determinism("replay trace kind mismatch").kind,
            EffectFailureKind::Determinism
        );
        assert_eq!(
            EffectFailure::contract_violation("handler identity contract violated").kind,
            EffectFailureKind::ContractViolation
        );
        assert_eq!(
            EffectFailure::unavailable("channel unavailable").kind,
            EffectFailureKind::Unavailable
        );
        assert_eq!(
            EffectFailure::invalid_input("invalid payload type").kind,
            EffectFailureKind::InvalidInput
        );
    }

}
