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
    ) -> Result<Value, String> {
        if let Some(fallback) = self.fallback {
            fallback.handle_send(role, partner, label, state)
        } else {
            Ok(Value::Unit)
        }
    }

    fn send_decision(&self, input: SendDecisionInput<'_>) -> Result<SendDecision, String> {
        let entry = self.next_entry("send_decision")?;
        if let Some(decision) = Self::parse_send_decision(&entry.outputs, input.payload.clone()) {
            return Ok(decision);
        }
        if let Some(committed) = entry.outputs.get("committed").and_then(JsonValue::as_bool) {
            if committed {
                return Ok(SendDecision::Deliver(input.payload.unwrap_or(Value::Unit)));
            }
        }
        if let Some(fallback) = self.fallback {
            return fallback.send_decision(input);
        }
        Err("replay send_decision missing decision payload".to_string())
    }

    fn handle_recv(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        state: &mut Vec<Value>,
        payload: &Value,
    ) -> Result<(), String> {
        self.next_entry("handle_recv")?;
        if let Some(fallback) = self.fallback {
            return fallback.handle_recv(role, partner, label, state, payload);
        }
        Ok(())
    }

    fn handle_choose(
        &self,
        role: &str,
        partner: &str,
        labels: &[String],
        state: &[Value],
    ) -> Result<String, String> {
        let entry = self.next_entry("handle_choose")?;
        if let Some(chosen) = entry.outputs.get("label").and_then(JsonValue::as_str) {
            return Ok(chosen.to_string());
        }
        if let Some(fallback) = self.fallback {
            return fallback.handle_choose(role, partner, labels, state);
        }
        Err("replay handle_choose missing chosen label".to_string())
    }

    fn step(&self, role: &str, state: &mut Vec<Value>) -> Result<(), String> {
        self.next_entry("invoke_step")?;
        if let Some(fallback) = self.fallback {
            return fallback.step(role, state);
        }
        Ok(())
    }

    fn handle_acquire(
        &self,
        sid: SessionId,
        role: &str,
        layer: &str,
        state: &[Value],
    ) -> Result<AcquireDecision, String> {
        let entry = self.next_entry("handle_acquire")?;
        if let Some(decision) = Self::parse_acquire_decision(&entry.outputs) {
            return Ok(decision);
        }
        if let Some(granted) = entry.outputs.get("granted").and_then(JsonValue::as_bool) {
            if granted {
                return Ok(AcquireDecision::Grant(Value::Unit));
            }
        }
        if let Some(fallback) = self.fallback {
            return fallback.handle_acquire(sid, role, layer, state);
        }
        Err("replay handle_acquire missing acquire decision".to_string())
    }

    fn handle_release(
        &self,
        sid: SessionId,
        role: &str,
        layer: &str,
        evidence: &Value,
        state: &[Value],
    ) -> Result<(), String> {
        self.next_entry("handle_release")?;
        if let Some(fallback) = self.fallback {
            return fallback.handle_release(sid, role, layer, evidence, state);
        }
        Ok(())
    }

    fn topology_events(&self, _tick: u64) -> Result<Vec<TopologyPerturbation>, String> {
        let mut events = Vec::new();
        while self.peek_entry_kind().as_deref() == Some("topology_event") {
            let entry = self.next_entry("topology_event")?;
            if let Some(topology) = entry.topology {
                events.push(topology);
                continue;
            }
            if let Some(raw) = entry.outputs.get("topology") {
                if let Ok(topology) = serde_json::from_value::<TopologyPerturbation>(raw.clone()) {
                    events.push(topology);
                }
            }
        }
        Ok(events)
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
        ) -> Result<Value, String> {
            Ok(Value::Nat(1))
        }

        #[allow(clippy::as_conversions, clippy::cast_possible_wrap)]
        fn send_decision(&self, input: SendDecisionInput<'_>) -> Result<SendDecision, String> {
            let idx = self.counter.fetch_add(1, Ordering::Relaxed);
            if idx % 2 == 0 {
                Ok(SendDecision::Deliver(
                    input.payload.unwrap_or(Value::Nat(idx as u64)),
                ))
            } else {
                Ok(SendDecision::Drop)
            }
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
                .ok_or_else(|| "no labels".to_string())
        }

        fn step(&self, _role: &str, _state: &mut Vec<Value>) -> Result<(), String> {
            Ok(())
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
            .expect("replay second decision");
        assert!(matches!(replay_first, SendDecision::Deliver(_)));
        assert!(matches!(replay_second, SendDecision::Drop));
        assert_eq!(replay.remaining(), 0);
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
            ) -> Result<Value, String> {
                Ok(Value::Unit)
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
                    .ok_or_else(|| "no labels".to_string())
            }

            fn step(&self, _role: &str, _state: &mut Vec<Value>) -> Result<(), String> {
                Ok(())
            }

            fn topology_events(&self, _tick: u64) -> Result<Vec<TopologyPerturbation>, String> {
                let idx = self.emitted.fetch_add(1, Ordering::Relaxed);
                if idx == 0 {
                    Ok(vec![TopologyPerturbation::Crash {
                        site: "node-a".to_string(),
                    }])
                } else {
                    Ok(Vec::new())
                }
            }
        }

        let base = TopologyOnce {
            emitted: AtomicUsize::new(0),
        };
        let recorder = RecordingEffectHandler::new(&base);
        let first = recorder.topology_events(1).expect("record topology");
        let second = recorder.topology_events(2).expect("record topology");
        assert_eq!(first.len(), 1);
        assert!(second.is_empty());

        let replay = ReplayEffectHandler::new(recorder.effect_trace());
        let replay_first = replay.topology_events(1).expect("replay topology");
        let replay_second = replay.topology_events(2).expect("replay topology");
        assert_eq!(replay_first.len(), 1);
        assert!(replay_second.is_empty());
        assert_eq!(replay.remaining(), 0);
    }

    #[test]
    fn classify_effect_error_categories_from_strings() {
        assert_eq!(
            classify_effect_error("timed out waiting for recv"),
            EffectErrorCategory::Timeout
        );
        assert_eq!(
            classify_effect_error("topology partition mismatch"),
            EffectErrorCategory::Topology
        );
        assert_eq!(
            classify_effect_error("replay trace kind mismatch"),
            EffectErrorCategory::Determinism
        );
        assert_eq!(
            classify_effect_error("handler identity contract violated"),
            EffectErrorCategory::ContractViolation
        );
        assert_eq!(
            classify_effect_error("channel unavailable"),
            EffectErrorCategory::Unavailable
        );
        assert_eq!(
            classify_effect_error("invalid payload type"),
            EffectErrorCategory::InvalidInput
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
