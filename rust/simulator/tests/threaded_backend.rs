//! Threaded simulator backend integration tests.
#![cfg(feature = "multi-thread")]

use std::collections::BTreeMap;

use telltale_machine::coroutine::Value;
use telltale_machine::model::effects::{
    EffectFailure, EffectHandler, EffectResult, SendDecision, SendDecisionInput,
};
use telltale_simulator::contracts::{evaluate_contracts, ContractCheckConfig};
use telltale_simulator::decision::theorem_eligibility_from_result;
use telltale_simulator::run_canonical_replay;
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

fn middleware_active_scenario(
    name: &str,
    backend: &str,
    scheduler_concurrency: u64,
    worker_threads: u64,
) -> Scenario {
    let toml = format!(
        r#"
name = "{name}"
roles = ["A", "B"]
steps = 8
seed = 17

[execution]
backend = "{backend}"
scheduler_concurrency = {scheduler_concurrency}
worker_threads = {worker_threads}

[network]
base_latency_ms = 1
latency_variance = "0.0"
loss_probability = "0.0"

[[adversaries]]
id = "timing_once"
trigger = {{ at_tick = 2 }}
action = {{ type = "timing_disturbance", ticks = 1 }}
budget = {{ total = 1, mode = "activation", assumption_failure = "fairness_failure" }}

[[reconfigurations]]
trigger = {{ at_tick = 1 }}
action = {{ type = "handoff", handoff_id = "handoff#1", from_role = "A", to_role = "B" }}

[properties]
invariants = ["no_faults", "simplex"]

[field]
layer = "mean_field"

[field.params]
beta = "1.0"
species = ["up", "down"]
initial_state = ["0.5", "0.5"]
step_size = "0.01"
"#
    );
    Scenario::parse(&toml).expect("parse middleware-active scenario")
}

fn assert_authoritative_equivalence(
    left: &telltale_simulator::runner::ScenarioResult,
    right: &telltale_simulator::runner::ScenarioResult,
) {
    assert_eq!(left.replay.obs_trace, right.replay.obs_trace);
    assert_eq!(left.replay.effect_trace, right.replay.effect_trace);
    assert_eq!(
        left.replay.output_condition_trace,
        right.replay.output_condition_trace
    );
    assert_eq!(left.replay.semantic_objects, right.replay.semantic_objects);
    assert_eq!(
        left.replay.adversary_budget_history,
        right.replay.adversary_budget_history
    );
    assert_eq!(
        left.replay.reconfiguration_trace,
        right.replay.reconfiguration_trace
    );
    assert_eq!(left.analysis, right.analysis);
    assert_eq!(left.violations, right.violations);
}

#[test]
fn threaded_backend_matches_canonical_for_middleware_active_exact_runs() {
    let (global, local_types) = simple_protocol();
    let canonical = middleware_active_scenario("threaded_phase19_canonical", "canonical", 1, 1);
    let threaded = middleware_active_scenario("threaded_phase19_exact", "threaded", 1, 2);

    let canonical_result = run_with_scenario(
        &local_types,
        &global,
        &BTreeMap::new(),
        &canonical,
        &PassthroughHandler,
    )
    .expect("canonical run");
    let threaded_result = run_with_scenario(
        &local_types,
        &global,
        &BTreeMap::new(),
        &threaded,
        &PassthroughHandler,
    )
    .expect("threaded run");

    assert_authoritative_equivalence(&canonical_result, &threaded_result);
}

#[test]
fn threaded_backend_reports_resolved_execution_settings() {
    let (global, local_types) = simple_protocol();
    let threaded = scenario("threaded", 2, 2);

    let result = run_with_scenario(
        &local_types,
        &global,
        &BTreeMap::new(),
        &threaded,
        &PassthroughHandler,
    )
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
fn threaded_backend_is_worker_count_invariant_for_middleware_active_exact_runs() {
    let (global, local_types) = simple_protocol();
    let workers2 = middleware_active_scenario("threaded_phase19_workers2", "threaded", 1, 2);
    let workers4 = middleware_active_scenario("threaded_phase19_workers4", "threaded", 1, 4);

    let result2 = run_with_scenario(
        &local_types,
        &global,
        &BTreeMap::new(),
        &workers2,
        &PassthroughHandler,
    )
    .expect("threaded run with two workers");
    let result4 = run_with_scenario(
        &local_types,
        &global,
        &BTreeMap::new(),
        &workers4,
        &PassthroughHandler,
    )
    .expect("threaded run with four workers");

    assert_authoritative_equivalence(&result2, &result4);
}

#[test]
fn threaded_exact_runs_replay_through_the_canonical_lane() {
    let (global, local_types) = simple_protocol();
    let threaded = middleware_active_scenario("threaded_phase19_replay", "threaded", 1, 3);

    let exact = run_with_scenario(
        &local_types,
        &global,
        &BTreeMap::new(),
        &threaded,
        &PassthroughHandler,
    )
    .expect("threaded exact run");
    let replayed = run_canonical_replay(
        &local_types,
        &global,
        &BTreeMap::new(),
        &threaded,
        &PassthroughHandler,
    )
    .expect("canonical replay run");

    assert_authoritative_equivalence(&exact, &replayed);
    assert_eq!(
        evaluate_contracts(&exact, &ContractCheckConfig::default()),
        evaluate_contracts(&replayed, &ContractCheckConfig::default())
    );
    assert_eq!(
        theorem_eligibility_from_result(&exact),
        theorem_eligibility_from_result(&replayed),
        "threaded exact replay should preserve theorem eligibility under the canonical lane"
    );
}
