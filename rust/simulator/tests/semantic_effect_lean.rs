#![allow(clippy::expect_used)]
//! Reduced semantic-effect parity checks against Lean fixtures.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;

use serde::Deserialize;
use telltale_machine::durable::WalSyncRequest;
use telltale_machine::model::effects::{
    EffectFailure, EffectHandler, EffectRequestBody, EffectResult, SendDecision, SendDecisionInput,
    TopologyPerturbation,
};
use telltale_machine::model::output_condition::OutputConditionHint;
use telltale_machine::semantic_objects::{OperationPhase, OutstandingEffectStatus};
use telltale_simulator::runner::{canonical_replay_scenario, run_with_scenario, ScenarioResult};
use telltale_simulator::scenario::Scenario;
use telltale_types::{FixedQ32, GlobalType, Label, LocalTypeR};

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
struct SimulatorSemanticEffectHandler;

impl EffectHandler for SimulatorSemanticEffectHandler {
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

fn simple_send_recv_protocol() -> (GlobalType, BTreeMap<String, LocalTypeR>) {
    let global = GlobalType::send("A", "B", Label::new("m"), GlobalType::End);
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
    (global, local_types)
}

fn initial_states() -> BTreeMap<String, Vec<FixedQ32>> {
    BTreeMap::from([
        ("A".to_string(), vec![FixedQ32::zero()]),
        ("B".to_string(), vec![FixedQ32::zero()]),
    ])
}

fn scenario_with_backend(name: &str, backend: &str, steps: u64) -> Scenario {
    let worker_threads = if backend == "canonical" { 1 } else { 2 };
    let toml = format!(
        r#"
name = "{name}"
roles = ["A", "B"]
steps = {steps}
seed = 7

[execution]
backend = "{backend}"
scheduler_concurrency = 1
worker_threads = {worker_threads}

[field]
layer = "mean_field"

[field.params]
beta = "1.0"
species = ["up", "down"]
initial_state = ["0.5", "0.5"]
step_size = "0.01"
"#
    );
    Scenario::parse(&toml).expect("parse scenario")
}

fn blocked_send_fixture_from_result(result: &ScenarioResult) -> ReducedSemanticEffectFixture {
    let blocked_exchange = result
        .replay
        .semantic_objects
        .outstanding_effects
        .iter()
        .find(|effect| {
            effect.effect_kind == "send_decision"
                && effect.status == OutstandingEffectStatus::Blocked
        })
        .and_then(|effect| {
            result
                .replay
                .effect_exchanges
                .iter()
                .find(|exchange| exchange.effect_id == effect.effect_id)
        })
        .or_else(|| {
            result
                .replay
                .semantic_objects
                .operation_instances
                .iter()
                .find(|operation| {
                    operation.kind == "send_decision" && operation.phase == OperationPhase::Blocked
                })
                .and_then(|operation| {
                    operation.effect_ids.first().and_then(|effect_id| {
                        result
                            .replay
                            .effect_exchanges
                            .iter()
                            .find(|exchange| exchange.effect_id == *effect_id)
                    })
                })
        })
        .unwrap_or_else(|| {
            panic!(
                "blocked send effect: outstanding={:?}; operations={:?}; exchanges={:?}",
                result.replay.semantic_objects.outstanding_effects,
                result.replay.semantic_objects.operation_instances,
                result
                    .replay
                    .effect_exchanges
                    .iter()
                    .map(|exchange| (
                        exchange.effect_id,
                        exchange.request.metadata.interface_name.clone(),
                        exchange.request.metadata.operation_name.clone(),
                        format!("{:?}", exchange.request.body),
                        format!("{:?}", exchange.outcome.status)
                    ))
                    .collect::<Vec<_>>()
            )
        });
    ReducedSemanticEffectFixture {
        name: "blocked_send".to_string(),
        effect_kind: "send_decision".to_string(),
        lifecycle: "blocked".to_string(),
        interface_name: blocked_exchange.request.metadata.interface_name.clone(),
        operation_name: blocked_exchange.request.metadata.operation_name.clone(),
        publication_materialized: false,
        output_predicate: None,
    }
}

fn internal_fixtures_from_result(result: &ScenarioResult) -> Vec<ReducedSemanticEffectFixture> {
    let predicate = result
        .replay
        .output_condition_trace
        .first()
        .map(|check| check.meta.predicate_ref.clone());
    let send_success = result
        .replay
        .effect_exchanges
        .iter()
        .find(|exchange| {
            matches!(
                exchange.request.body,
                EffectRequestBody::SendDecision { .. }
            ) && exchange.succeeded()
        })
        .expect("successful send exchange");
    let output_hint = result
        .replay
        .effect_exchanges
        .iter()
        .find(|exchange| {
            matches!(
                exchange.request.body,
                EffectRequestBody::OutputConditionHint { .. }
            )
        })
        .expect("output hint exchange");
    let wal_sync = result
        .replay
        .effect_exchanges
        .iter()
        .find(|exchange| matches!(exchange.request.body, EffectRequestBody::WalSync { .. }))
        .expect("wal sync exchange");
    let publication_materialized = !result.replay.semantic_objects.publication_events.is_empty()
        && result
            .replay
            .semantic_objects
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
fn simulator_semantic_effects_match_lean_reduced_fixture_surface() {
    let Some(mut expected) = load_lean_fixtures() else {
        eprintln!(
            "semantic_effect_parity_runner not available; build with: cd lean && lake build semantic_effect_parity_runner"
        );
        return;
    };
    expected.sort();

    let (global, local_types) = simple_send_recv_protocol();
    let initial = initial_states();
    let blocked = scenario_with_backend("semantic_effects_blocked", "canonical", 3);
    let canonical = scenario_with_backend("semantic_effects_canonical", "canonical", 8);
    let threaded = scenario_with_backend("semantic_effects_threaded", "threaded", 8);
    let replay = canonical_replay_scenario(&threaded);

    let blocked_result = run_with_scenario(
        &local_types,
        &global,
        &initial,
        &blocked,
        &SimulatorSemanticEffectHandler,
    )
    .expect("run blocked semantic-effect scenario");

    let canonical_result = run_with_scenario(
        &local_types,
        &global,
        &initial,
        &canonical,
        &SimulatorSemanticEffectHandler,
    )
    .expect("run canonical semantic-effect scenario");
    let threaded_result = run_with_scenario(
        &local_types,
        &global,
        &initial,
        &threaded,
        &SimulatorSemanticEffectHandler,
    )
    .expect("run threaded semantic-effect scenario");
    let replay_result = run_with_scenario(
        &local_types,
        &global,
        &initial,
        &replay,
        &SimulatorSemanticEffectHandler,
    )
    .expect("run replay semantic-effect scenario");

    let blocked_fixture = blocked_send_fixture_from_result(&blocked_result);
    let mut canonical_fixtures = internal_fixtures_from_result(&canonical_result);
    canonical_fixtures.push(blocked_fixture.clone());
    canonical_fixtures.sort();
    let mut threaded_fixtures = internal_fixtures_from_result(&threaded_result);
    threaded_fixtures.push(blocked_fixture.clone());
    threaded_fixtures.sort();
    let mut replay_fixtures = internal_fixtures_from_result(&replay_result);
    replay_fixtures.push(blocked_fixture);
    replay_fixtures.sort();

    assert_eq!(canonical_fixtures, expected);
    assert_eq!(threaded_fixtures, expected);
    assert_eq!(replay_fixtures, expected);
    assert_eq!(canonical_fixtures, threaded_fixtures);
    assert_eq!(canonical_fixtures, replay_fixtures);
}
