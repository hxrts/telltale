#![cfg(not(target_arch = "wasm32"))]
#![allow(clippy::expect_used)]
//! Reduced semantic-effect parity checks against Lean fixtures.

#[allow(dead_code, unreachable_pub)]
#[path = "support/mod.rs"]
mod test_support;

use std::path::{Path, PathBuf};
use std::process::Command;

use serde::Deserialize;
use telltale_machine::durable::WalSyncRequest;
use telltale_machine::model::effects::{
    EffectFailure, EffectHandler, EffectRequestBody, EffectResult, SendDecision, SendDecisionInput,
    TopologyPerturbation,
};
use telltale_machine::model::output_condition::OutputConditionHint;
use telltale_machine::semantic_objects::OutstandingEffectStatus;
use telltale_machine::{ProtocolMachine, ProtocolMachineConfig};
use test_support::simple_send_recv_image;

#[derive(Debug, Clone, Deserialize, PartialEq, Eq, PartialOrd, Ord)]
struct ReducedSemanticEffectFixture {
    name: String,
    effect_kind: String,
    lifecycle: String,
    interface_name: String,
    operation_name: String,
    publication_materialized: bool,
    output_predicate: Option<String>,
}

#[derive(Debug, Deserialize)]
struct ReducedSemanticEffectBundle {
    schema_version: String,
    fixtures: Vec<ReducedSemanticEffectFixture>,
}

#[derive(Debug, Clone, Copy)]
struct BlockedSendHandler;

impl EffectHandler for BlockedSendHandler {
    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &[telltale_machine::Value],
    ) -> EffectResult<telltale_machine::Value> {
        EffectResult::success(telltale_machine::Value::Unit)
    }

    fn send_decision(&self, input: SendDecisionInput<'_>) -> EffectResult<SendDecision> {
        EffectResult::success(SendDecision::Deliver(
            input.payload.unwrap_or(telltale_machine::Value::Unit),
        ))
    }

    fn handle_recv(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &mut Vec<telltale_machine::Value>,
        _payload: &telltale_machine::Value,
    ) -> EffectResult<()> {
        EffectResult::success(())
    }

    fn handle_choose(
        &self,
        _role: &str,
        _partner: &str,
        labels: &[String],
        _state: &[telltale_machine::Value],
    ) -> EffectResult<String> {
        labels.first().cloned().map_or_else(
            || EffectResult::failure(EffectFailure::invalid_input("no labels")),
            EffectResult::success,
        )
    }

    fn step(&self, _role: &str, _state: &mut Vec<telltale_machine::Value>) -> EffectResult<()> {
        EffectResult::success(())
    }

    fn topology_events(&self, tick: u64) -> EffectResult<Vec<TopologyPerturbation>> {
        let events = if tick == 1 {
            vec![TopologyPerturbation::Partition {
                from: "A".to_string(),
                to: "B".to_string(),
            }]
        } else {
            Vec::new()
        };
        EffectResult::success(events)
    }
}

#[derive(Debug, Clone, Copy)]
struct InternalEffectReplayHandler;

impl EffectHandler for InternalEffectReplayHandler {
    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        label: &str,
        _state: &[telltale_machine::Value],
    ) -> EffectResult<telltale_machine::Value> {
        EffectResult::success(telltale_machine::Value::Str(label.to_string()))
    }

    fn send_decision(&self, input: SendDecisionInput<'_>) -> EffectResult<SendDecision> {
        EffectResult::success(SendDecision::Deliver(
            input.payload.unwrap_or(telltale_machine::Value::Unit),
        ))
    }

    fn handle_recv(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &mut Vec<telltale_machine::Value>,
        _payload: &telltale_machine::Value,
    ) -> EffectResult<()> {
        EffectResult::success(())
    }

    fn handle_choose(
        &self,
        _role: &str,
        _partner: &str,
        labels: &[String],
        _state: &[telltale_machine::Value],
    ) -> EffectResult<String> {
        labels.first().cloned().map_or_else(
            || EffectResult::failure(EffectFailure::invalid_input("no labels")),
            EffectResult::success,
        )
    }

    fn step(&self, _role: &str, _state: &mut Vec<telltale_machine::Value>) -> EffectResult<()> {
        EffectResult::success(())
    }

    fn output_condition_hint(
        &self,
        sid: usize,
        role: &str,
        _state: &[telltale_machine::Value],
    ) -> Option<OutputConditionHint> {
        Some(OutputConditionHint {
            predicate_ref: "machine.replay.internal_effects".to_string(),
            witness_ref: Some(format!("sid:{sid}:role:{role}")),
        })
    }

    fn supports_wal_sync(&self) -> bool {
        true
    }

    fn wal_sync(&self, _sync: &WalSyncRequest) -> EffectResult<()> {
        EffectResult::success(())
    }
}

fn semantic_effect_runner_path() -> Option<PathBuf> {
    let crate_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let path = crate_dir
        .parent()
        .and_then(Path::parent)
        .map(|root| root.join("lean/.lake/build/bin/semantic_effect_parity_runner"))?;
    path.is_file().then_some(path)
}

fn load_lean_fixtures() -> Option<Vec<ReducedSemanticEffectFixture>> {
    let runner = semantic_effect_runner_path()?;
    let output = Command::new(runner).output().ok()?;
    if !output.status.success() {
        return None;
    }
    let bundle: ReducedSemanticEffectBundle = serde_json::from_slice(&output.stdout).ok()?;
    assert_eq!(bundle.schema_version, "semantic_effect_parity_v1");
    Some(bundle.fixtures)
}

fn machine_fixtures() -> Vec<ReducedSemanticEffectFixture> {
    let mut blocked_machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    blocked_machine
        .load_choreography(&simple_send_recv_image("A", "B", "m"))
        .expect("load blocked-send machine");
    blocked_machine
        .step(&BlockedSendHandler)
        .expect("run blocked-send step");
    let blocked_effect = blocked_machine
        .outstanding_effects()
        .iter()
        .find(|effect| {
            effect.effect_kind == "send_decision"
                && effect.status == OutstandingEffectStatus::Blocked
        })
        .expect("blocked send effect");
    let blocked_exchange = blocked_machine
        .effect_exchanges()
        .iter()
        .find(|exchange| exchange.effect_id == blocked_effect.effect_id)
        .expect("matching blocked send exchange");

    let mut internal_machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    internal_machine
        .load_choreography(&simple_send_recv_image("A", "B", "m"))
        .expect("load internal-effects machine");
    internal_machine
        .run(&InternalEffectReplayHandler, 64)
        .expect("run internal-effects machine");
    let predicate = internal_machine
        .output_condition_checks()
        .first()
        .map(|check| check.meta.predicate_ref.clone());
    let send_success = internal_machine
        .effect_exchanges()
        .iter()
        .find(|exchange| {
            matches!(
                exchange.request.body,
                EffectRequestBody::SendDecision { .. }
            ) && exchange.succeeded()
        })
        .expect("successful send exchange");
    let output_hint = internal_machine
        .effect_exchanges()
        .iter()
        .find(|exchange| {
            matches!(
                exchange.request.body,
                EffectRequestBody::OutputConditionHint { .. }
            )
        })
        .expect("output-condition hint exchange");
    let wal_sync = internal_machine
        .effect_exchanges()
        .iter()
        .find(|exchange| matches!(exchange.request.body, EffectRequestBody::WalSync { .. }))
        .expect("wal-sync exchange");
    let publication_materialized = !internal_machine
        .semantic_objects()
        .publication_events
        .is_empty()
        && internal_machine
            .semantic_objects()
            .canonical_handles
            .iter()
            .any(|handle| {
                matches!(
                    handle.kind,
                    telltale_machine::CanonicalHandleKind::Materialization
                )
            });

    let mut fixtures = vec![
        ReducedSemanticEffectFixture {
            name: "blocked_send".to_string(),
            effect_kind: "send_decision".to_string(),
            lifecycle: "blocked".to_string(),
            interface_name: blocked_exchange.request.metadata.interface_name.clone(),
            operation_name: blocked_exchange.request.metadata.operation_name.clone(),
            publication_materialized: false,
            output_predicate: None,
        },
        ReducedSemanticEffectFixture {
            name: "send_publication".to_string(),
            effect_kind: "send_decision".to_string(),
            lifecycle: "succeeded".to_string(),
            interface_name: send_success.request.metadata.interface_name.clone(),
            operation_name: send_success.request.metadata.operation_name.clone(),
            publication_materialized,
            output_predicate: predicate.clone(),
        },
        ReducedSemanticEffectFixture {
            name: "output_condition_hint".to_string(),
            effect_kind: "output_condition_hint".to_string(),
            lifecycle: "succeeded".to_string(),
            interface_name: output_hint.request.metadata.interface_name.clone(),
            operation_name: output_hint.request.metadata.operation_name.clone(),
            publication_materialized: false,
            output_predicate: predicate,
        },
        ReducedSemanticEffectFixture {
            name: "wal_sync".to_string(),
            effect_kind: "wal_sync".to_string(),
            lifecycle: "succeeded".to_string(),
            interface_name: wal_sync.request.metadata.interface_name.clone(),
            operation_name: wal_sync.request.metadata.operation_name.clone(),
            publication_materialized: false,
            output_predicate: None,
        },
    ];
    fixtures.sort();
    fixtures
}

#[test]
fn machine_semantic_effects_match_lean_reduced_fixture_surface() {
    let Some(mut expected) = load_lean_fixtures() else {
        eprintln!(
            "semantic_effect_parity_runner not available; build with: cd lean && lake build semantic_effect_parity_runner"
        );
        return;
    };
    expected.sort();
    assert_eq!(machine_fixtures(), expected);
}
