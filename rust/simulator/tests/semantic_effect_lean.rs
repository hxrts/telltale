#![allow(clippy::expect_used)]
//! Reduced semantic-effect parity checks against Lean fixtures.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;

use serde::Deserialize;
use telltale_machine::durable::WalSyncRequest;
use telltale_machine::instr::{ImmValue, Instr, InvokeAction};
use telltale_machine::model::effects::{
    EffectFailure, EffectHandler, EffectRequestBody, EffectResult, SendDecision, SendDecisionInput,
    TopologyPerturbation,
};
use telltale_machine::model::output_condition::OutputConditionHint;
use telltale_machine::runtime::loader::CodeImage;
use telltale_machine::semantic_objects::{OperationPhase, OutstandingEffectStatus};
use telltale_machine::{ProtocolMachine, ProtocolMachineConfig};
use telltale_simulator::backend::SimulationMachine;
use telltale_simulator::execution::{execute_scenario_rounds, ScenarioMiddleware};
use telltale_simulator::persistence::{PersistedReplayArtifact, PersistedReplayPayload};
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

fn single_role_end_image(program: Vec<Instr>) -> CodeImage {
    CodeImage {
        programs: {
            let mut programs = BTreeMap::new();
            programs.insert("A".to_string(), program);
            programs
        },
        global_type: GlobalType::End,
        local_types: {
            let mut local_types = BTreeMap::new();
            local_types.insert("A".to_string(), LocalTypeR::End);
            local_types
        },
    }
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

#[derive(Debug, Clone, Copy)]
struct FailedInvokeHandler;

impl EffectHandler for FailedInvokeHandler {
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
        EffectResult::failure(EffectFailure::contract_violation("invoke failed"))
    }
}

#[derive(Debug, Clone, Copy)]
struct SendThenFaultHandler;

impl EffectHandler for SendThenFaultHandler {
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

    fn step(&self, role: &str, _state: &mut Vec<telltale_machine::Value>) -> EffectResult<()> {
        if role == "B" {
            EffectResult::failure(EffectFailure::contract_violation("late fault"))
        } else {
            EffectResult::success(())
        }
    }
}

#[derive(Debug, Clone, Copy)]
struct ResumedSendHandler;

impl EffectHandler for ResumedSendHandler {
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

fn reduced_fixture(
    name: &str,
    effect_kind: &str,
    lifecycle: &str,
    interface_name: impl Into<String>,
    operation_name: impl Into<String>,
    publication_materialized: bool,
    output_predicate: Option<String>,
) -> ReducedSemanticEffectFixture {
    ReducedSemanticEffectFixture {
        name: name.to_string(),
        effect_kind: effect_kind.to_string(),
        lifecycle: lifecycle.to_string(),
        interface_name: interface_name.into(),
        operation_name: operation_name.into(),
        publication_materialized,
        output_predicate,
    }
}

fn semantic_effect_image() -> telltale_machine::runtime::loader::CodeImage {
    let (global, local_types) = simple_send_recv_protocol();
    telltale_machine::runtime::loader::CodeImage::from_local_types(&local_types, &global)
}

fn blocked_machine_fixture(
    image: &telltale_machine::runtime::loader::CodeImage,
) -> ReducedSemanticEffectFixture {
    let mut blocked_machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    blocked_machine
        .load_choreography(image)
        .expect("load blocked-send machine");
    blocked_machine
        .step(&SimulatorSemanticEffectHandler)
        .expect("run blocked send step");
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
    reduced_fixture(
        "blocked_send",
        "send_decision",
        "blocked",
        blocked_exchange.request.metadata.interface_name.clone(),
        blocked_exchange.request.metadata.operation_name.clone(),
        false,
        None,
    )
}

fn internal_machine_fixtures(
    image: &telltale_machine::runtime::loader::CodeImage,
) -> Vec<ReducedSemanticEffectFixture> {
    let mut internal_machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    internal_machine
        .load_choreography(image)
        .expect("load internal-effects machine");
    internal_machine
        .run(&SimulatorSemanticEffectHandler, 64)
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
        .expect("output hint exchange");
    let wal_sync = internal_machine
        .effect_exchanges()
        .iter()
        .find(|exchange| matches!(exchange.request.body, EffectRequestBody::WalSync { .. }))
        .expect("wal sync exchange");
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
    vec![
        reduced_fixture(
            "send_publication",
            "send_decision",
            "succeeded",
            send_success.request.metadata.interface_name.clone(),
            send_success.request.metadata.operation_name.clone(),
            publication_materialized,
            predicate.clone(),
        ),
        reduced_fixture(
            "output_condition_hint",
            "output_condition_hint",
            "succeeded",
            output_hint.request.metadata.interface_name.clone(),
            output_hint.request.metadata.operation_name.clone(),
            false,
            predicate,
        ),
        reduced_fixture(
            "wal_sync",
            "wal_sync",
            "succeeded",
            wal_sync.request.metadata.interface_name.clone(),
            wal_sync.request.metadata.operation_name.clone(),
            false,
            None,
        ),
    ]
}

fn machine_negative_fixtures() -> Vec<ReducedSemanticEffectFixture> {
    vec![
        reduced_fixture(
            "failed_invoke",
            "invoke_step",
            "failed",
            "Runtime",
            "invoke",
            false,
            None,
        ),
        reduced_fixture(
            "send_before_fault",
            "send_decision",
            "succeeded_then_faulted",
            "Transport",
            "sendDecision",
            false,
            None,
        ),
        reduced_fixture(
            "resumed_send",
            "send_decision",
            "resumed",
            "Transport",
            "sendDecision",
            false,
            None,
        ),
    ]
}

fn machine_fixture_bundle() -> Vec<ReducedSemanticEffectFixture> {
    let image = semantic_effect_image();
    let mut fixtures = vec![blocked_machine_fixture(&image)];
    fixtures.extend(internal_machine_fixtures(&image));
    fixtures.extend(machine_negative_fixtures());
    fixtures.sort();
    fixtures
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
    blocked_send_fixture_from_replay(&result.replay)
}

fn blocked_send_fixture_from_replay(
    replay: &telltale_simulator::runner::ScenarioReplayArtifact,
) -> ReducedSemanticEffectFixture {
    let blocked_exchange = replay
        .semantic_objects
        .outstanding_effects
        .iter()
        .find(|effect| {
            effect.effect_kind == "send_decision"
                && effect.status == OutstandingEffectStatus::Blocked
        })
        .and_then(|effect| {
            replay
                .effect_exchanges
                .iter()
                .find(|exchange| exchange.effect_id == effect.effect_id)
        })
        .or_else(|| {
            replay
                .semantic_objects
                .operation_instances
                .iter()
                .find(|operation| {
                    operation.kind == "send_decision" && operation.phase == OperationPhase::Blocked
                })
                .and_then(|operation| {
                    operation.effect_ids.first().and_then(|effect_id| {
                        replay
                            .effect_exchanges
                            .iter()
                            .find(|exchange| exchange.effect_id == *effect_id)
                    })
                })
        })
        .unwrap_or_else(|| {
            panic!(
                "blocked send effect: outstanding={:?}; operations={:?}; exchanges={:?}",
                replay.semantic_objects.outstanding_effects,
                replay.semantic_objects.operation_instances,
                replay
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
    internal_fixtures_from_replay(&result.replay)
}

fn internal_fixtures_from_replay(
    replay: &telltale_simulator::runner::ScenarioReplayArtifact,
) -> Vec<ReducedSemanticEffectFixture> {
    let predicate = replay
        .output_condition_trace
        .first()
        .map(|check| check.meta.predicate_ref.clone());
    let send_success = replay
        .effect_exchanges
        .iter()
        .find(|exchange| {
            matches!(
                exchange.request.body,
                EffectRequestBody::SendDecision { .. }
            ) && exchange.succeeded()
        })
        .expect("successful send exchange");
    let output_hint = replay
        .effect_exchanges
        .iter()
        .find(|exchange| {
            matches!(
                exchange.request.body,
                EffectRequestBody::OutputConditionHint { .. }
            )
        })
        .expect("output hint exchange");
    let wal_sync = replay
        .effect_exchanges
        .iter()
        .find(|exchange| matches!(exchange.request.body, EffectRequestBody::WalSync { .. }))
        .expect("wal sync exchange");
    let publication_materialized = !replay.semantic_objects.publication_events.is_empty()
        && replay
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

fn simulator_fixture_bundle() -> Vec<ReducedSemanticEffectFixture> {
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

    let mut bundle = canonical_fixtures.clone();
    bundle.extend(simulator_negative_fixture_bundle());
    bundle.sort();

    assert_eq!(canonical_fixtures, threaded_fixtures);
    assert_eq!(canonical_fixtures, replay_fixtures);
    bundle
}

fn canonical_semantic_effect_result() -> ScenarioResult {
    let (global, local_types) = simple_send_recv_protocol();
    let initial = initial_states();
    let canonical = scenario_with_backend("semantic_effects_canonical_phase5", "canonical", 8);
    run_with_scenario(
        &local_types,
        &global,
        &initial,
        &canonical,
        &SimulatorSemanticEffectHandler,
    )
    .expect("run canonical semantic-effect scenario")
}

fn blocked_semantic_effect_result() -> ScenarioResult {
    let (global, local_types) = simple_send_recv_protocol();
    let initial = initial_states();
    let blocked = scenario_with_backend("semantic_effects_blocked_phase5", "canonical", 3);
    run_with_scenario(
        &local_types,
        &global,
        &initial,
        &blocked,
        &SimulatorSemanticEffectHandler,
    )
    .expect("run blocked semantic-effect scenario")
}

fn scenario_for_low_level_backend(name: &str, backend: &str, steps: u64) -> Scenario {
    scenario_with_backend(name, backend, steps)
}

fn load_simulation_machine(
    backend: &str,
    scenario: &Scenario,
    image: &CodeImage,
) -> SimulationMachine {
    let resolved = scenario
        .resolved_execution()
        .expect("resolve simulator execution");
    let mut machine = SimulationMachine::new(ProtocolMachineConfig::default(), &resolved);
    machine
        .load_choreography_owned(image, format!("sim/{backend}/semantic_effects"))
        .expect("load choreography into simulator machine");
    machine
}

fn run_low_level_simulator(
    backend: &str,
    image: &CodeImage,
    scenario: &Scenario,
    handler: &dyn EffectHandler,
) -> SimulationMachine {
    let mut machine = load_simulation_machine(backend, scenario, image);
    let middleware =
        ScenarioMiddleware::from_scenario(scenario, handler, machine.clock().tick_duration)
            .expect("build simulator middleware");
    let resolved = scenario
        .resolved_execution()
        .expect("resolve simulator execution");
    match execute_scenario_rounds(
        &mut machine,
        scenario,
        &middleware,
        usize::try_from(resolved.scheduler_concurrency).unwrap_or(usize::MAX),
        scenario.steps,
        |_, _| Ok(()),
    ) {
        Ok(_) | Err(_) => {}
    }
    machine
}

fn assert_same_exchange_metadata(
    left: &telltale_machine::EffectExchangeRecord,
    right: &telltale_machine::EffectExchangeRecord,
) {
    assert_eq!(
        left.request.metadata.interface_name,
        right.request.metadata.interface_name
    );
    assert_eq!(
        left.request.metadata.operation_name,
        right.request.metadata.operation_name
    );
}

fn simulator_failed_invoke_negative_fixture() -> ReducedSemanticEffectFixture {
    let failed_invoke_image = single_role_end_image(vec![
        Instr::Set {
            dst: 1,
            val: ImmValue::Nat(1),
        },
        Instr::Invoke {
            action: InvokeAction::Reg(1),
        },
        Instr::Halt,
    ]);
    let failed_canonical_scenario =
        scenario_for_low_level_backend("failed_invoke_canonical", "canonical", 4);
    let failed_threaded_scenario =
        scenario_for_low_level_backend("failed_invoke_threaded", "threaded", 4);
    let failed_canonical_machine = run_low_level_simulator(
        "canonical",
        &failed_invoke_image,
        &failed_canonical_scenario,
        &FailedInvokeHandler,
    );
    let failed_threaded_machine = run_low_level_simulator(
        "threaded",
        &failed_invoke_image,
        &failed_threaded_scenario,
        &FailedInvokeHandler,
    );
    let failed_invoke_canonical = failed_canonical_machine
        .effect_exchanges()
        .iter()
        .find(|exchange| {
            matches!(exchange.request.body, EffectRequestBody::InvokeStep { .. })
                && !exchange.succeeded()
        })
        .expect("canonical failed invoke exchange");
    let failed_invoke_threaded = failed_threaded_machine
        .effect_exchanges()
        .iter()
        .find(|exchange| {
            matches!(exchange.request.body, EffectRequestBody::InvokeStep { .. })
                && !exchange.succeeded()
        })
        .expect("threaded failed invoke exchange");
    assert_same_exchange_metadata(failed_invoke_canonical, failed_invoke_threaded);
    reduced_fixture(
        "failed_invoke",
        "invoke_step",
        "failed",
        failed_invoke_canonical
            .request
            .metadata
            .interface_name
            .clone(),
        failed_invoke_canonical
            .request
            .metadata
            .operation_name
            .clone(),
        false,
        None,
    )
}

fn simulator_send_before_fault_negative_fixture() -> ReducedSemanticEffectFixture {
    let (send_recv_global, send_recv_locals) = simple_send_recv_protocol();
    let send_recv_image = telltale_machine::runtime::loader::CodeImage::from_local_types(
        &send_recv_locals,
        &send_recv_global,
    );
    let fault_canonical_scenario =
        scenario_for_low_level_backend("send_fault_canonical", "canonical", 8);
    let fault_threaded_scenario =
        scenario_for_low_level_backend("send_fault_threaded", "threaded", 8);
    let fault_canonical_machine = run_low_level_simulator(
        "canonical",
        &send_recv_image,
        &fault_canonical_scenario,
        &SendThenFaultHandler,
    );
    let fault_threaded_machine = run_low_level_simulator(
        "threaded",
        &send_recv_image,
        &fault_threaded_scenario,
        &SendThenFaultHandler,
    );
    let send_before_fault_canonical = fault_canonical_machine
        .effect_exchanges()
        .iter()
        .find(|exchange| {
            matches!(
                exchange.request.body,
                EffectRequestBody::SendDecision { .. }
            ) && exchange.succeeded()
        })
        .expect("canonical send before fault");
    let send_before_fault_threaded = fault_threaded_machine
        .effect_exchanges()
        .iter()
        .find(|exchange| {
            matches!(
                exchange.request.body,
                EffectRequestBody::SendDecision { .. }
            ) && exchange.succeeded()
        })
        .expect("threaded send before fault");
    assert_same_exchange_metadata(send_before_fault_canonical, send_before_fault_threaded);
    reduced_fixture(
        "send_before_fault",
        "send_decision",
        "succeeded_then_faulted",
        send_before_fault_canonical
            .request
            .metadata
            .interface_name
            .clone(),
        send_before_fault_canonical
            .request
            .metadata
            .operation_name
            .clone(),
        false,
        None,
    )
}

fn simulator_resumed_send_negative_fixture() -> ReducedSemanticEffectFixture {
    let (send_recv_global, send_recv_locals) = simple_send_recv_protocol();
    let send_recv_image = telltale_machine::runtime::loader::CodeImage::from_local_types(
        &send_recv_locals,
        &send_recv_global,
    );
    let resumed_canonical_scenario =
        scenario_for_low_level_backend("resumed_send_canonical", "canonical", 8);
    let resumed_threaded_scenario =
        scenario_for_low_level_backend("resumed_send_threaded", "threaded", 8);
    let resumed_canonical_machine = run_low_level_simulator(
        "canonical",
        &send_recv_image,
        &resumed_canonical_scenario,
        &ResumedSendHandler,
    );
    let resumed_threaded_machine = run_low_level_simulator(
        "threaded",
        &send_recv_image,
        &resumed_threaded_scenario,
        &ResumedSendHandler,
    );
    let resumed_send_canonical = resumed_canonical_machine
        .effect_exchanges()
        .iter()
        .find(|exchange| {
            matches!(
                exchange.request.body,
                EffectRequestBody::SendDecision { .. }
            ) && exchange.succeeded()
        })
        .expect("canonical resumed send");
    let resumed_send_threaded = resumed_threaded_machine
        .effect_exchanges()
        .iter()
        .find(|exchange| {
            matches!(
                exchange.request.body,
                EffectRequestBody::SendDecision { .. }
            ) && exchange.succeeded()
        })
        .expect("threaded resumed send");
    assert_same_exchange_metadata(resumed_send_canonical, resumed_send_threaded);
    reduced_fixture(
        "resumed_send",
        "send_decision",
        "resumed",
        resumed_send_canonical
            .request
            .metadata
            .interface_name
            .clone(),
        resumed_send_canonical
            .request
            .metadata
            .operation_name
            .clone(),
        false,
        None,
    )
}

fn simulator_negative_fixture_bundle() -> Vec<ReducedSemanticEffectFixture> {
    let mut fixtures = vec![
        simulator_failed_invoke_negative_fixture(),
        simulator_send_before_fault_negative_fixture(),
        simulator_resumed_send_negative_fixture(),
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

    assert_eq!(simulator_fixture_bundle(), expected);
}

#[test]
fn simulator_reduced_semantic_effects_match_machine_reduced_fixture_bundle() {
    assert_eq!(simulator_fixture_bundle(), machine_fixture_bundle());
}

#[test]
fn semantic_effect_projection_survives_scenario_result_json_roundtrip() {
    let canonical_result = canonical_semantic_effect_result();
    let expected = internal_fixtures_from_result(&canonical_result);
    let encoded = serde_json::to_vec(&canonical_result).expect("encode scenario result");
    let decoded: ScenarioResult = serde_json::from_slice(&encoded).expect("decode scenario result");

    assert_eq!(
        decoded.replay.effect_exchanges,
        canonical_result.replay.effect_exchanges
    );
    assert_eq!(
        decoded.replay.semantic_objects,
        canonical_result.replay.semantic_objects
    );
    assert_eq!(internal_fixtures_from_result(&decoded), expected);
}

#[test]
fn semantic_effect_projection_survives_persisted_replay_roundtrip() {
    let canonical_result = canonical_semantic_effect_result();
    let expected = internal_fixtures_from_result(&canonical_result);
    let persisted = PersistedReplayArtifact::scenario_replay(canonical_result.replay.clone());
    let encoded = persisted.to_cbor().expect("encode persisted replay");
    let decoded = PersistedReplayArtifact::from_slice(&encoded).expect("decode persisted replay");
    let replay = match decoded.payload {
        PersistedReplayPayload::ScenarioReplay(replay) => replay,
        PersistedReplayPayload::Checkpoint(_) => panic!("expected scenario replay payload"),
    };

    assert_eq!(
        replay.effect_exchanges,
        canonical_result.replay.effect_exchanges
    );
    assert_eq!(
        replay.semantic_objects,
        canonical_result.replay.semantic_objects
    );
    assert_eq!(internal_fixtures_from_replay(&replay), expected);
}

#[test]
fn blocked_semantic_effect_projection_survives_persisted_replay_roundtrip() {
    let blocked_result = blocked_semantic_effect_result();
    let expected = blocked_send_fixture_from_result(&blocked_result);
    let persisted = PersistedReplayArtifact::scenario_replay(blocked_result.replay.clone());
    let encoded = persisted
        .to_cbor()
        .expect("encode blocked persisted replay");
    let decoded =
        PersistedReplayArtifact::from_slice(&encoded).expect("decode blocked persisted replay");
    let replay = match decoded.payload {
        PersistedReplayPayload::ScenarioReplay(replay) => replay,
        PersistedReplayPayload::Checkpoint(_) => panic!("expected scenario replay payload"),
    };

    assert_eq!(blocked_send_fixture_from_replay(&replay), expected);
}
