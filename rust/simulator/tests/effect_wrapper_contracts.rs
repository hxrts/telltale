#![cfg(not(target_arch = "wasm32"))]
#![allow(clippy::expect_used)]
//! Contract tests for simulator-side effect-handler wrappers and middleware stacks.

use std::collections::BTreeMap;
use std::time::Duration;

use telltale_machine::durable::WalSyncRequest;
use telltale_machine::model::effects::{
    EffectHandler, EffectRequest, EffectResponse, EffectResult, SendDecision, SendDecisionInput,
    TopologyPerturbation,
};
use telltale_machine::model::output_condition::OutputConditionHint;
use telltale_machine::Value;
use telltale_simulator::runner::run_with_scenario;
use telltale_simulator::scenario::Scenario;
use telltale_simulator::{
    AdversaryInjector, AdversaryProgram, NetworkConfig, NetworkModel, SimRng,
};
use telltale_types::{FixedQ32, GlobalType, Label, LocalTypeR};

#[derive(Debug, Clone, PartialEq)]
struct SurfaceSnapshot {
    handler_identity: String,
    topology_events: Vec<TopologyPerturbation>,
    output_hint: Option<OutputConditionHint>,
    acquire_evidence: Value,
    wal_supported: bool,
}

#[derive(Debug, Clone, Copy)]
struct SurfaceHandler;

impl EffectHandler for SurfaceHandler {
    fn handler_identity(&self) -> String {
        "surface_handler".to_string()
    }

    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &[Value],
    ) -> EffectResult<Value> {
        EffectResult::success(Value::Unit)
    }

    fn send_decision(&self, input: SendDecisionInput<'_>) -> EffectResult<SendDecision> {
        EffectResult::success(SendDecision::Deliver(input.payload.unwrap_or(Value::Unit)))
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
        labels.last().cloned().map_or_else(
            || EffectResult::success("none".to_string()),
            EffectResult::success,
        )
    }

    fn step(&self, _role: &str, _state: &mut Vec<Value>) -> EffectResult<()> {
        EffectResult::success(())
    }

    fn handle_acquire(
        &self,
        sid: usize,
        role: &str,
        layer: &str,
        state: &[Value],
    ) -> EffectResult<Value> {
        EffectResult::success(Value::Prod(
            Box::new(Value::Nat(u64::try_from(sid).unwrap_or(u64::MAX))),
            Box::new(Value::Prod(
                Box::new(Value::Str(role.to_string())),
                Box::new(Value::Prod(
                    Box::new(Value::Str(layer.to_string())),
                    Box::new(Value::Nat(u64::try_from(state.len()).unwrap_or(u64::MAX))),
                )),
            )),
        ))
    }

    fn handle_release(
        &self,
        _sid: usize,
        _role: &str,
        _layer: &str,
        _evidence: &Value,
        _state: &[Value],
    ) -> EffectResult<()> {
        EffectResult::success(())
    }

    fn supports_wal_sync(&self) -> bool {
        true
    }

    fn wal_sync(&self, _sync: &WalSyncRequest) -> EffectResult<()> {
        EffectResult::success(())
    }

    fn topology_events(&self, tick: u64) -> EffectResult<Vec<TopologyPerturbation>> {
        EffectResult::success(vec![
            TopologyPerturbation::Partition {
                from: format!("A{tick}"),
                to: format!("B{tick}"),
            },
            TopologyPerturbation::Heal {
                from: format!("C{tick}"),
                to: format!("D{tick}"),
            },
        ])
    }

    fn output_condition_hint(
        &self,
        sid: usize,
        role: &str,
        state: &[Value],
    ) -> Option<OutputConditionHint> {
        Some(OutputConditionHint {
            predicate_ref: format!("surface.{sid}.{role}.{}", state.len()),
            witness_ref: Some("surface-witness".to_string()),
        })
    }
}

fn surface_state() -> Vec<Value> {
    vec![Value::Nat(1), Value::Str("state".to_string())]
}

fn surface_sync() -> WalSyncRequest {
    WalSyncRequest {
        tick: 11,
        operation_id: "wal#surface".to_string(),
        downstream_coroutine_id: "coro#surface".to_string(),
        gate_level: telltale_machine::AgreementLevel::Finalized,
        agreement_state: None,
        agreement_evidence: vec![],
    }
}

fn expect_success<T>(result: EffectResult<T>, what: &str) -> T {
    match result {
        EffectResult::Success(value) => value,
        EffectResult::Blocked => panic!("{what} blocked unexpectedly"),
        EffectResult::Failure(failure) => panic!("{what} failed unexpectedly: {failure:?}"),
    }
}

fn exercise_surface(handler: &dyn EffectHandler) -> SurfaceSnapshot {
    let state = surface_state();
    let topology_events = expect_success(handler.topology_events(3), "topology events");
    let topology_outcome = handler.handle_effect(EffectRequest::topology_events(3));
    assert_eq!(
        topology_outcome.response,
        Some(EffectResponse::TopologyEvents {
            events: topology_events.clone(),
        })
    );

    let output_hint = handler.output_condition_hint(7, "role_a", &state);
    let output_outcome = handler.handle_effect(EffectRequest::output_condition_hint(
        5, 7, None, "role_a", &state,
    ));
    assert_eq!(
        output_outcome.response,
        Some(EffectResponse::OutputConditionHint {
            hint: output_hint.clone(),
        })
    );

    let acquire_evidence = expect_success(
        handler.handle_acquire(7, "role_a", "layer_alpha", &state),
        "acquire evidence",
    );
    let acquire_outcome = handler.handle_effect(EffectRequest::acquire(
        5,
        7,
        None,
        "role_a",
        "layer_alpha",
        &state,
    ));
    assert_eq!(
        acquire_outcome.response,
        Some(EffectResponse::Acquire {
            evidence: acquire_evidence.clone(),
        })
    );

    expect_success(
        handler.handle_release(7, "role_a", "layer_alpha", &acquire_evidence, &state),
        "release evidence",
    );
    let release_outcome = handler.handle_effect(EffectRequest::release(
        5,
        7,
        None,
        "role_a",
        "layer_alpha",
        &acquire_evidence,
        &state,
    ));
    assert_eq!(release_outcome.response, Some(EffectResponse::Release));

    let wal_supported = handler.supports_wal_sync();
    let sync = surface_sync();
    expect_success(handler.wal_sync(&sync), "wal sync");
    let wal_outcome = handler.handle_effect(EffectRequest::wal_sync(
        sync.tick,
        sync.operation_id.clone(),
        sync.clone(),
    ));
    assert_eq!(wal_outcome.response, Some(EffectResponse::WalSync));

    SurfaceSnapshot {
        handler_identity: handler.handler_identity(),
        topology_events,
        output_hint,
        acquire_evidence,
        wal_supported,
    }
}

fn assert_surface_metadata(exchanges: &[telltale_machine::EffectExchangeRecord]) {
    let surface_ops = [
        ("Runtime", "topologyEvents"),
        ("Runtime", "outputConditionHint"),
        ("Guard", "acquire"),
        ("Guard", "release"),
        ("Wal", "sync"),
    ];
    for (interface_name, operation_name) in surface_ops {
        assert!(
            exchanges.iter().any(|exchange| {
                exchange.request.metadata.interface_name == interface_name
                    && exchange.request.metadata.operation_name == operation_name
            }),
            "missing metadata pair {interface_name}/{operation_name} in recorded exchanges"
        );
    }
}

fn simple_protocol() -> (GlobalType, BTreeMap<String, LocalTypeR>) {
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

fn scenario_with_network(name: &str) -> Scenario {
    Scenario::parse(&format!(
        r#"
name = "{name}"
roles = ["A", "B"]
steps = 4
seed = 7

[execution]
backend = "canonical"
scheduler_concurrency = 1
worker_threads = 1

[network]
links = []

[field]
layer = "mean_field"

[field.params]
beta = "1.0"
species = ["up", "down"]
initial_state = ["0.5", "0.5"]
step_size = "0.01"
"#
    ))
    .expect("parse scenario")
}

#[test]
fn adversary_injector_preserves_declared_surface_contracts() {
    let base = SurfaceHandler;
    let expected = exercise_surface(&base);
    let wrapper = AdversaryInjector::new(base, AdversaryProgram::default(), SimRng::new(7));
    let observed = exercise_surface(&wrapper);
    assert_eq!(observed, expected);
}

#[test]
fn network_model_preserves_declared_surface_contracts() {
    let base = SurfaceHandler;
    let expected = exercise_surface(&base);
    let wrapper = NetworkModel::new(
        base,
        NetworkConfig::default(),
        SimRng::new(7),
        Duration::from_millis(1),
    );
    let observed = exercise_surface(&wrapper);
    assert_eq!(observed, expected);
}

#[test]
fn simulator_middleware_stack_preserves_topology_output_and_wal_surfaces() {
    let (global, local_types) = simple_protocol();
    let initial_states = BTreeMap::from([
        ("A".to_string(), vec![FixedQ32::zero()]),
        ("B".to_string(), vec![FixedQ32::zero()]),
    ]);
    let scenario = scenario_with_network("effect_wrapper_stack");
    let result = run_with_scenario(
        &local_types,
        &global,
        &initial_states,
        &scenario,
        &SurfaceHandler,
    )
    .expect("run scenario");

    let effect_exchanges = &result.replay.effect_exchanges;
    assert!(effect_exchanges
        .iter()
        .any(|exchange| exchange.request.metadata.operation_name == "topologyEvents"));
    assert!(effect_exchanges
        .iter()
        .any(|exchange| exchange.request.metadata.operation_name == "outputConditionHint"));
    assert!(effect_exchanges
        .iter()
        .any(|exchange| exchange.request.metadata.operation_name == "sync"));
    assert!(effect_exchanges
        .iter()
        .filter(|exchange| {
            matches!(
                exchange.request.metadata.operation_name.as_str(),
                "topologyEvents" | "outputConditionHint" | "sync"
            )
        })
        .all(|exchange| exchange.handler_identity == "surface_handler"));
}

#[test]
fn generated_simulator_wrapper_compositions_preserve_surface_and_metadata() {
    let expected = exercise_surface(&SurfaceHandler);

    let raw_recording = telltale_machine::RecordingEffectHandler::new(&SurfaceHandler);
    let raw_snapshot = exercise_surface(&raw_recording);
    assert_eq!(raw_snapshot, expected);
    assert_surface_metadata(&raw_recording.effect_exchanges());

    let adversary =
        AdversaryInjector::new(SurfaceHandler, AdversaryProgram::default(), SimRng::new(7));
    let adversary_recording = telltale_machine::RecordingEffectHandler::new(&adversary);
    let adversary_snapshot = exercise_surface(&adversary_recording);
    assert_eq!(adversary_snapshot, expected);
    assert_surface_metadata(&adversary_recording.effect_exchanges());

    let network = NetworkModel::new(
        SurfaceHandler,
        NetworkConfig::default(),
        SimRng::new(7),
        Duration::from_millis(1),
    );
    let network_recording = telltale_machine::RecordingEffectHandler::new(&network);
    let network_snapshot = exercise_surface(&network_recording);
    assert_eq!(network_snapshot, expected);
    assert_surface_metadata(&network_recording.effect_exchanges());

    let stacked = NetworkModel::new(
        AdversaryInjector::new(SurfaceHandler, AdversaryProgram::default(), SimRng::new(9)),
        NetworkConfig::default(),
        SimRng::new(11),
        Duration::from_millis(1),
    );
    let stacked_recording = telltale_machine::RecordingEffectHandler::new(&stacked);
    let stacked_snapshot = exercise_surface(&stacked_recording);
    assert_eq!(stacked_snapshot, expected);
    assert_surface_metadata(&stacked_recording.effect_exchanges());
}
