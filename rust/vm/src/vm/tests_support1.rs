    use super::*;
    use crate::instr::Instr;
    use crate::loader::CodeImage;
    use crate::persistence::PersistenceModel;
    use std::collections::{BTreeMap, BTreeSet};
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::time::Duration;
    use telltale_types::{GlobalType, Label, LocalTypeR, ValType};

    /// Trivial handler that passes values through.
    struct PassthroughHandler;

    impl EffectHandler for PassthroughHandler {
        fn handle_send(
            &self,
            _role: &str,
            _partner: &str,
            _label: &str,
            _state: &[Value],
        ) -> Result<Value, String> {
            Ok(Value::Nat(42))
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
                .ok_or_else(|| "no labels available".into())
        }

        fn step(&self, _role: &str, _state: &mut Vec<Value>) -> Result<(), String> {
            Ok(())
        }
    }

    /// Handler that deterministically fails on send.
    struct FailingSendHandler;

    impl EffectHandler for FailingSendHandler {
        fn handle_send(
            &self,
            _role: &str,
            _partner: &str,
            _label: &str,
            _state: &[Value],
        ) -> Result<Value, String> {
            Err("send failed".to_string())
        }

        fn send_decision(&self, _input: SendDecisionInput<'_>) -> Result<SendDecision, String> {
            Err("send failed".to_string())
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

    #[derive(Debug, Clone, Copy, Default)]
    struct RecordingPersistence;

    impl PersistenceModel for RecordingPersistence {
        type PState = Vec<String>;
        type Delta = String;

        fn apply(state: &mut Self::PState, delta: &Self::Delta) -> Result<(), String> {
            state.push(delta.clone());
            Ok(())
        }

        fn derive(_before: &Self::PState, _after: &Self::PState) -> Result<Self::Delta, String> {
            Ok("derive".to_string())
        }

        fn open_delta(session: SessionId) -> Self::Delta {
            format!("open:{session}")
        }

        fn close_delta(session: SessionId) -> Self::Delta {
            format!("close:{session}")
        }

        fn invoke_delta(session: SessionId, action: &str) -> Option<Self::Delta> {
            Some(format!("invoke:{session}:{action}"))
        }
    }

    struct TimeoutOnTickOneHandler;

    impl EffectHandler for TimeoutOnTickOneHandler {
        fn handle_send(
            &self,
            _role: &str,
            _partner: &str,
            _label: &str,
            _state: &[Value],
        ) -> Result<Value, String> {
            Ok(Value::Nat(1))
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

        fn topology_events(&self, tick: u64) -> Result<Vec<TopologyPerturbation>, String> {
            if tick == 1 {
                Ok(vec![TopologyPerturbation::Timeout {
                    site: "A".to_string(),
                    duration: Duration::from_millis(20),
                }])
            } else {
                Ok(Vec::new())
            }
        }
    }

    struct CorruptOnTickOneHandler;

    impl EffectHandler for CorruptOnTickOneHandler {
        fn handle_send(
            &self,
            _role: &str,
            _partner: &str,
            _label: &str,
            _state: &[Value],
        ) -> Result<Value, String> {
            Ok(Value::Nat(0))
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

        fn topology_events(&self, tick: u64) -> Result<Vec<TopologyPerturbation>, String> {
            if tick == 1 {
                Ok(vec![TopologyPerturbation::Corrupt {
                    from: "A".to_string(),
                    to: "B".to_string(),
                    corruption: CorruptionType::BitFlip,
                }])
            } else {
                Ok(Vec::new())
            }
        }
    }

    struct CrashOnTickOneHandler;

    impl EffectHandler for CrashOnTickOneHandler {
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
                .ok_or_else(|| "no labels available".to_string())
        }

        fn step(&self, _role: &str, _state: &mut Vec<Value>) -> Result<(), String> {
            Ok(())
        }

        fn topology_events(&self, tick: u64) -> Result<Vec<TopologyPerturbation>, String> {
            if tick == 1 {
                Ok(vec![TopologyPerturbation::Crash {
                    site: "A".to_string(),
                }])
            } else {
                Ok(Vec::new())
            }
        }
    }

    struct IdentityFlappingHandler {
        calls: AtomicUsize,
    }

    impl IdentityFlappingHandler {
        fn new() -> Self {
            Self {
                calls: AtomicUsize::new(0),
            }
        }
    }

    impl EffectHandler for IdentityFlappingHandler {
        fn handler_identity(&self) -> String {
            if self.calls.fetch_add(1, Ordering::Relaxed) % 2 == 0 {
                "handler_a".to_string()
            } else {
                "handler_b".to_string()
            }
        }

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
                .ok_or_else(|| "no labels available".to_string())
        }

        fn step(&self, _role: &str, _state: &mut Vec<Value>) -> Result<(), String> {
            Ok(())
        }
    }

    struct UnsortedTopologyHandler;

    impl EffectHandler for UnsortedTopologyHandler {
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
                .ok_or_else(|| "no labels available".to_string())
        }

        fn step(&self, _role: &str, _state: &mut Vec<Value>) -> Result<(), String> {
            Ok(())
        }

        fn topology_events(&self, tick: u64) -> Result<Vec<TopologyPerturbation>, String> {
            if tick == 1 {
                Ok(vec![
                    TopologyPerturbation::Timeout {
                        site: "B".to_string(),
                        duration: Duration::from_millis(1),
                    },
                    TopologyPerturbation::Crash {
                        site: "A".to_string(),
                    },
                ])
            } else {
                Ok(Vec::new())
            }
        }
    }
