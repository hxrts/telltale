//! First-party integration harness utilities.
//!
//! These helpers validate host integration behavior without changing VM
//! semantics. They run on top of the canonical VM APIs.

use crate::determinism::{replay_consistent, DeterminismMode};
use crate::effect::{EffectHandler, RecordingEffectHandler};
use crate::vm::{VMError, VM};
use serde::{Deserialize, Serialize};

/// Summary from loaded-VM record/replay conformance execution.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct LoadedVmReplayConformance {
    /// Determinism mode used for replay consistency checks.
    pub determinism_mode: DeterminismMode,
    /// Profile-aware consistency outcome.
    pub replay_consistent: bool,
    /// Consistency outcome under `VMConfig.determinism_mode`.
    pub config_mode_consistent: bool,
    /// Exact observable trace equality.
    pub exact_trace_match: bool,
    /// Exact effect-trace equality.
    pub exact_effect_trace_match: bool,
    /// Number of recorded effect entries used for replay.
    pub recorded_effect_count: usize,
    /// Baseline observable event count.
    pub baseline_event_count: usize,
    /// Replay observable event count.
    pub replay_event_count: usize,
}

/// Run record-and-replay conformance against a loaded VM.
///
/// The helper snapshots the provided VM, executes a baseline run with
/// `RecordingEffectHandler`, then replays the recorded effect trace from the
/// snapshot state. The input `vm` is left in the baseline post-run state.
///
/// # Errors
///
/// Returns `VMError` if baseline run, replay run, or snapshot encode/decode fails.
pub fn run_loaded_vm_record_replay_conformance(
    vm: &mut VM,
    handler: &dyn EffectHandler,
    max_steps: usize,
) -> Result<LoadedVmReplayConformance, VMError> {
    let snapshot = serde_yaml::to_string(vm).map_err(|e| {
        VMError::PersistenceError(format!("integration snapshot encode failed: {e}"))
    })?;

    let recording = RecordingEffectHandler::new(handler);
    vm.run(&recording, max_steps)?;

    let recorded_effects = recording.effect_trace();
    let baseline_trace = vm.trace().to_vec();
    let baseline_effect_trace = vm.effect_trace().to_vec();
    let determinism_mode = vm.config().determinism_mode;

    let mut replay_vm: VM = serde_yaml::from_str(&snapshot).map_err(|e| {
        VMError::PersistenceError(format!("integration snapshot decode failed: {e}"))
    })?;
    replay_vm.run_replay(handler, &recorded_effects, max_steps)?;

    let replay_trace = replay_vm.trace().to_vec();
    let replay_effect_trace = replay_vm.effect_trace().to_vec();
    let replay_mode_consistent = replay_consistent(
        DeterminismMode::Replay,
        &baseline_trace,
        &replay_trace,
        &baseline_effect_trace,
        &replay_effect_trace,
    );
    let config_mode_consistent = replay_consistent(
        determinism_mode,
        &baseline_trace,
        &replay_trace,
        &baseline_effect_trace,
        &replay_effect_trace,
    );

    Ok(LoadedVmReplayConformance {
        determinism_mode,
        replay_consistent: replay_mode_consistent,
        config_mode_consistent,
        exact_trace_match: baseline_trace == replay_trace,
        exact_effect_trace_match: baseline_effect_trace == replay_effect_trace,
        recorded_effect_count: recorded_effects.len(),
        baseline_event_count: baseline_trace.len(),
        replay_event_count: replay_trace.len(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::coroutine::Value;
    use crate::effect::{SendDecision, SendDecisionInput};
    use crate::loader::CodeImage;
    use crate::vm::VMConfig;
    use std::collections::BTreeMap;
    use telltale_types::{GlobalType, Label, LocalTypeR};

    struct DeterministicHandler;

    impl EffectHandler for DeterministicHandler {
        fn handle_send(
            &self,
            _role: &str,
            _partner: &str,
            _label: &str,
            _state: &[Value],
        ) -> Result<Value, String> {
            Ok(Value::Nat(1))
        }

        fn send_decision(&self, input: SendDecisionInput<'_>) -> Result<SendDecision, String> {
            Ok(SendDecision::Deliver(input.payload.unwrap_or(Value::Unit)))
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

    fn simple_send_recv_image() -> CodeImage {
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
        CodeImage::from_local_types(&local_types, &global)
    }

    #[test]
    fn loaded_vm_harness_reports_replay_conformance() {
        let image = simple_send_recv_image();
        let mut vm = VM::new(VMConfig::default());
        vm.load_choreography(&image).expect("load choreography");

        let report = run_loaded_vm_record_replay_conformance(&mut vm, &DeterministicHandler, 100)
            .expect("harness run should succeed");

        assert!(report.replay_consistent);
        assert!(!report.config_mode_consistent);
        assert!(report.exact_trace_match);
        assert!(!report.exact_effect_trace_match);
        assert!(report.recorded_effect_count > 0);
        assert!(report.baseline_event_count > 0);
    }
}
