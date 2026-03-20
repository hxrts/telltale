impl EffectHandler for ReplayEffectHandler<'_> {
    fn handler_identity(&self) -> String {
        "replay_handler".to_string()
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
        let entry = match self.next_entry("send_decision") {
            Ok(entry) => entry,
            Err(message) => return EffectResult::failure(EffectFailure::determinism(message)),
        };
        if let Some(decision) = Self::parse_send_decision(&entry.outputs, input.payload.clone()) {
            return decision;
        }
        if let Some(committed) = entry.outputs.get("committed").and_then(JsonValue::as_bool) {
            if committed {
                return EffectResult::success(SendDecision::Deliver(
                    input.payload.unwrap_or(Value::Unit),
                ));
            }
        }
        if let Some(fallback) = self.fallback {
            return fallback.send_decision(input);
        }
        EffectResult::failure(EffectFailure::determinism(
            "replay send_decision missing typed outcome",
        ))
    }

    fn handle_recv(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        state: &mut Vec<Value>,
        payload: &Value,
    ) -> EffectResult<()> {
        let entry = match self.next_entry("handle_recv") {
            Ok(entry) => entry,
            Err(message) => return EffectResult::failure(EffectFailure::determinism(message)),
        };
        if let Some(outcome) = decode_effect_result::<()>(&entry.outputs) {
            return outcome;
        }
        if let Some(fallback) = self.fallback {
            return fallback.handle_recv(role, partner, label, state, payload);
        }
        EffectResult::failure(EffectFailure::determinism(
            "replay handle_recv missing typed outcome",
        ))
    }

    fn handle_choose(
        &self,
        role: &str,
        partner: &str,
        labels: &[String],
        state: &[Value],
    ) -> EffectResult<String> {
        let entry = match self.next_entry("handle_choose") {
            Ok(entry) => entry,
            Err(message) => return EffectResult::failure(EffectFailure::determinism(message)),
        };
        if let Some(chosen) = decode_effect_result::<String>(&entry.outputs) {
            return chosen;
        }
        if let Some(fallback) = self.fallback {
            return fallback.handle_choose(role, partner, labels, state);
        }
        EffectResult::failure(EffectFailure::determinism(
            "replay handle_choose missing typed outcome",
        ))
    }

    fn step(&self, role: &str, state: &mut Vec<Value>) -> EffectResult<()> {
        let entry = match self.next_entry("invoke_step") {
            Ok(entry) => entry,
            Err(message) => return EffectResult::failure(EffectFailure::determinism(message)),
        };
        if let Some(outcome) = decode_effect_result::<()>(&entry.outputs) {
            return outcome;
        }
        if let Some(fallback) = self.fallback {
            return fallback.step(role, state);
        }
        EffectResult::failure(EffectFailure::determinism(
            "replay invoke_step missing typed outcome",
        ))
    }

    fn handle_acquire(
        &self,
        sid: SessionId,
        role: &str,
        layer: &str,
        state: &[Value],
    ) -> EffectResult<Value> {
        let entry = match self.next_entry("handle_acquire") {
            Ok(entry) => entry,
            Err(message) => return EffectResult::failure(EffectFailure::determinism(message)),
        };
        if let Some(decision) = decode_effect_result::<Value>(&entry.outputs) {
            return decision;
        }
        if let Some(fallback) = self.fallback {
            return fallback.handle_acquire(sid, role, layer, state);
        }
        EffectResult::failure(EffectFailure::determinism(
            "replay handle_acquire missing typed outcome",
        ))
    }

    fn handle_release(
        &self,
        sid: SessionId,
        role: &str,
        layer: &str,
        evidence: &Value,
        state: &[Value],
    ) -> EffectResult<()> {
        let entry = match self.next_entry("handle_release") {
            Ok(entry) => entry,
            Err(message) => return EffectResult::failure(EffectFailure::determinism(message)),
        };
        if let Some(outcome) = decode_effect_result::<()>(&entry.outputs) {
            return outcome;
        }
        if let Some(fallback) = self.fallback {
            return fallback.handle_release(sid, role, layer, evidence, state);
        }
        EffectResult::failure(EffectFailure::determinism(
            "replay handle_release missing typed outcome",
        ))
    }

    fn topology_events(&self, _tick: u64) -> EffectResult<Vec<TopologyPerturbation>> {
        let entry = match self.next_entry("topology_events") {
            Ok(entry) => entry,
            Err(message) => return EffectResult::failure(EffectFailure::determinism(message)),
        };
        if let Some(outcome) = decode_effect_result::<Vec<TopologyPerturbation>>(&entry.outputs) {
            return outcome;
        }
        EffectResult::failure(EffectFailure::determinism(
            "replay topology_events missing typed outcome",
        ))
    }

    fn output_condition_hint(
        &self,
        sid: SessionId,
        role: &str,
        state: &[Value],
    ) -> Option<OutputConditionHint> {
        self.fallback
            .and_then(|fallback| fallback.output_condition_hint(sid, role, state))
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
        let blocked_json = encode_effect_result::<SendDecision>(&EffectResult::Blocked);
        let blocked = decode_effect_result::<SendDecision>(&blocked_json)
            .expect("blocked outcome should decode");
        assert!(matches!(blocked, EffectResult::Blocked));

        let failure_json = encode_effect_result::<SendDecision>(&EffectResult::failure(
            EffectFailure::timeout("send timed out"),
        ));
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

    #[test]
    fn send_fast_path_key_is_deterministic_for_same_inputs() {
        let left = send_fast_path_key(7, "A", "B", "msg", Some(SendPayloadKind::Nat));
        let right = send_fast_path_key(7, "A", "B", "msg", Some(SendPayloadKind::Nat));
        assert_eq!(left, right);
        assert_ne!(
            left,
            send_fast_path_key(7, "A", "B", "msg2", Some(SendPayloadKind::Nat))
        );
    }
}
