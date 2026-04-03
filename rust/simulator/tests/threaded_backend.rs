//! Threaded simulator backend integration tests.
#![cfg(feature = "multi-thread")]

use std::collections::BTreeMap;

use telltale_machine::coroutine::Value;
use telltale_machine::model::effects::{
    EffectFailure, EffectHandler, EffectResult, SendDecision, SendDecisionInput,
};
use telltale_simulator::runner::run_with_scenario;
use telltale_simulator::scenario::{ExecutionRegime, ResolvedExecutionBackend, Scenario};
use telltale_types::{GlobalType, Label, LocalTypeR};

#[derive(Debug, Clone, Copy)]
struct PassthroughHandler;

impl EffectHandler for PassthroughHandler {
    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        label: &str,
        _state: &[Value],
    ) -> EffectResult<Value> {
        EffectResult::success(Value::Str(label.to_string()))
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
        match labels.first().cloned() {
            Some(label) => EffectResult::success(label),
            None => EffectResult::failure(EffectFailure::invalid_input("no labels available")),
        }
    }

    fn step(&self, _role: &str, _state: &mut Vec<Value>) -> EffectResult<()> {
        EffectResult::success(())
    }
}

fn simple_protocol() -> (GlobalType, BTreeMap<String, LocalTypeR>) {
    let global = GlobalType::mu(
        "loop",
        GlobalType::send("A", "B", Label::new("msg"), GlobalType::var("loop")),
    );

    let mut local_types = BTreeMap::new();
    local_types.insert(
        "A".to_string(),
        LocalTypeR::mu(
            "loop",
            LocalTypeR::Send {
                partner: "B".into(),
                branches: vec![(Label::new("msg"), None, LocalTypeR::var("loop"))],
            },
        ),
    );
    local_types.insert(
        "B".to_string(),
        LocalTypeR::mu(
            "loop",
            LocalTypeR::Recv {
                partner: "A".into(),
                branches: vec![(Label::new("msg"), None, LocalTypeR::var("loop"))],
            },
        ),
    );

    (global, local_types)
}

fn scenario(backend: &str, scheduler_concurrency: u64, worker_threads: u64) -> Scenario {
    let toml = format!(
        r#"
name = "threaded_backend"
roles = ["A", "B"]
steps = 8
seed = 11

[execution]
backend = "{backend}"
scheduler_concurrency = {scheduler_concurrency}
worker_threads = {worker_threads}

[material]
layer = "mean_field"

[material.params]
beta = "1.0"
species = ["up", "down"]
initial_state = ["0.5", "0.5"]
step_size = "0.01"
"#
    );
    Scenario::parse(&toml).expect("parse scenario")
}

#[test]
fn threaded_backend_matches_canonical_at_scheduler_concurrency_one() {
    let (global, local_types) = simple_protocol();
    let canonical = scenario("canonical", 1, 1);
    let threaded = scenario("threaded", 1, 2);

    let canonical_result =
        run_with_scenario(&local_types, &global, &BTreeMap::new(), &canonical, &PassthroughHandler)
            .expect("canonical run");
    let threaded_result =
        run_with_scenario(&local_types, &global, &BTreeMap::new(), &threaded, &PassthroughHandler)
            .expect("threaded run");

    assert_eq!(
        canonical_result.replay.obs_trace,
        threaded_result.replay.obs_trace,
        "threaded backend must preserve canonical observable traces at scheduler_concurrency = 1"
    );
    assert_eq!(canonical_result.replay.effect_trace, threaded_result.replay.effect_trace);
    assert_eq!(
        canonical_result.replay.output_condition_trace,
        threaded_result.replay.output_condition_trace
    );
    assert_eq!(
        canonical_result.replay.semantic_objects,
        threaded_result.replay.semantic_objects
    );
}

#[test]
fn threaded_backend_reports_resolved_execution_settings() {
    let (global, local_types) = simple_protocol();
    let threaded = scenario("threaded", 2, 2);

    let result =
        run_with_scenario(&local_types, &global, &BTreeMap::new(), &threaded, &PassthroughHandler)
            .expect("threaded run");

    assert_eq!(result.stats.backend, ResolvedExecutionBackend::Threaded);
    assert_eq!(
        result.stats.execution_regime,
        ExecutionRegime::ThreadedEnvelopeBounded
    );
    assert_eq!(result.stats.scheduler_concurrency, 2);
    assert_eq!(result.stats.worker_threads, 2);
}

#[test]
fn threaded_backend_is_worker_count_invariant_for_fixed_scheduler_concurrency() {
    let (global, local_types) = simple_protocol();
    let workers2 = scenario("threaded", 2, 2);
    let workers4 = scenario("threaded", 2, 4);

    let result2 =
        run_with_scenario(&local_types, &global, &BTreeMap::new(), &workers2, &PassthroughHandler)
            .expect("threaded run with two workers");
    let result4 =
        run_with_scenario(&local_types, &global, &BTreeMap::new(), &workers4, &PassthroughHandler)
            .expect("threaded run with four workers");

    assert_eq!(result2.replay.obs_trace, result4.replay.obs_trace);
    assert_eq!(result2.replay.effect_trace, result4.replay.effect_trace);
    assert_eq!(
        result2.replay.output_condition_trace,
        result4.replay.output_condition_trace
    );
    assert_eq!(result2.replay.semantic_objects, result4.replay.semantic_objects);
}
