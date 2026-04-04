//! Correctness regression tests for simulator equivalence lanes.

use std::collections::BTreeMap;

use telltale_machine::coroutine::Value;
use telltale_machine::model::effects::{
    EffectFailure, EffectHandler, EffectResult, SendDecision, SendDecisionInput,
};
use telltale_simulator::contracts::{evaluate_contracts, ContractCheckConfig};
use telltale_simulator::decision::{decide_theorem_eligibility, theorem_eligibility_from_result};
use telltale_simulator::harness::{DirectAdapter, HarnessSpec, SimulationHarness};
use telltale_simulator::resume_with_checkpoint_artifact;
use telltale_simulator::runner::{run_with_scenario, ScenarioResult};
use telltale_simulator::scenario::{Scenario, TheoremSchedulerProfile};
use telltale_simulator::sweep::{compare_sweep_results, run_sweep, SweepAxis, SweepConfig};
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
        GlobalType::send(
            "A",
            "B",
            Label::new("msg"),
            GlobalType::send("B", "A", Label::new("ack"), GlobalType::var("loop")),
        ),
    );

    let mut local_types = BTreeMap::new();
    local_types.insert(
        "A".to_string(),
        LocalTypeR::mu(
            "loop",
            LocalTypeR::Send {
                partner: "B".into(),
                branches: vec![(
                    Label::new("msg"),
                    None,
                    LocalTypeR::Recv {
                        partner: "B".into(),
                        branches: vec![(Label::new("ack"), None, LocalTypeR::var("loop"))],
                    },
                )],
            },
        ),
    );
    local_types.insert(
        "B".to_string(),
        LocalTypeR::mu(
            "loop",
            LocalTypeR::Recv {
                partner: "A".into(),
                branches: vec![(
                    Label::new("msg"),
                    None,
                    LocalTypeR::Send {
                        partner: "A".into(),
                        branches: vec![(Label::new("ack"), None, LocalTypeR::var("loop"))],
                    },
                )],
            },
        ),
    );

    (global, local_types)
}

fn scenario_name(prefix: &str) -> String {
    format!("{prefix}_{}", std::process::id())
}

fn middleware_heavy_canonical_scenario(name: &str) -> Scenario {
    let toml = format!(
        r#"
name = "{name}"
roles = ["A", "B"]
steps = 8
seed = 41
checkpoint_interval = 2

[execution]
backend = "canonical"
scheduler_concurrency = 1
worker_threads = 1

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
    Scenario::parse(&toml).expect("parse middleware-heavy canonical scenario")
}

fn sweep_base_scenario() -> Scenario {
    Scenario::parse(
        r#"
name = "phase19_sweep"
roles = ["A", "B"]
steps = 6
seed = 3

[execution]
backend = "canonical"
scheduler_concurrency = 1
worker_threads = 1

[field]
layer = "mean_field"

[field.params]
beta = "1.0"
species = ["up", "down"]
initial_state = ["0.5", "0.5"]
step_size = "0.01"
"#,
    )
    .expect("parse sweep scenario")
}

fn assert_authoritative_equivalence(left: &ScenarioResult, right: &ScenarioResult) {
    assert_eq!(left.replay.theorem_profile, right.replay.theorem_profile);
    assert_eq!(
        left.replay.adversary_schedule,
        right.replay.adversary_schedule
    );
    assert_eq!(
        left.replay.adversary_budget_history,
        right.replay.adversary_budget_history
    );
    assert_eq!(
        left.replay.assumption_diagnostics,
        right.replay.assumption_diagnostics
    );
    assert_eq!(left.replay.obs_trace, right.replay.obs_trace);
    assert_eq!(left.replay.effect_trace, right.replay.effect_trace);
    assert_eq!(left.replay.effect_exchanges, right.replay.effect_exchanges);
    assert_eq!(
        left.replay.output_condition_trace,
        right.replay.output_condition_trace
    );
    assert_eq!(
        left.replay.semantic_audit_log,
        right.replay.semantic_audit_log
    );
    assert_eq!(left.replay.semantic_objects, right.replay.semantic_objects);
    assert_eq!(
        left.replay.reconfiguration_trace,
        right.replay.reconfiguration_trace
    );
    assert_eq!(
        left.replay.environment_trace,
        right.replay.environment_trace
    );
    assert_eq!(left.analysis, right.analysis);
    assert_eq!(left.violations, right.violations);
}

#[test]
fn checkpoint_resume_matches_uninterrupted_canonical_artifacts() {
    let (global, local_types) = simple_protocol();
    let scenario = middleware_heavy_canonical_scenario(&scenario_name("phase19_checkpoint"));

    let full = run_with_scenario(
        &local_types,
        &global,
        &BTreeMap::new(),
        &scenario,
        &PassthroughHandler,
    )
    .expect("full canonical run");

    let checkpoint = full
        .replay
        .checkpoints
        .iter()
        .find(|checkpoint| checkpoint.tick == 4)
        .unwrap_or_else(|| {
            panic!(
                "captured checkpoint at tick 4; available ticks: {:?}; checkpoint_writes={}; checkpoint_error={:?}",
                full.replay
                    .checkpoints
                    .iter()
                    .map(|checkpoint| checkpoint.tick)
                    .collect::<Vec<_>>(),
                full.stats.checkpoint_writes,
                full.stats.checkpoint_error
            )
        });
    let resumed =
        resume_with_checkpoint_artifact(&scenario, checkpoint, &PassthroughHandler, None, None)
            .expect("resume canonical checkpoint");

    assert_authoritative_equivalence(&full, &resumed);
    assert_eq!(
        full.replay.obs_trace, resumed.replay.obs_trace,
        "checkpoint resume must preserve the full observable trace"
    );
    assert_eq!(
        full.replay.effect_trace, resumed.replay.effect_trace,
        "checkpoint resume must preserve the full effect trace"
    );
    assert_eq!(
        full.replay.semantic_objects, resumed.replay.semantic_objects,
        "checkpoint resume must preserve final semantic objects"
    );
    assert_eq!(
        full.replay.adversary_budget_history, resumed.replay.adversary_budget_history,
        "checkpoint resume must preserve adversary budget accounting"
    );
    assert_eq!(
        full.replay.reconfiguration_trace, resumed.replay.reconfiguration_trace,
        "checkpoint resume must preserve reconfiguration trace fidelity"
    );
}

#[test]
fn direct_and_checkpoint_resume_lanes_keep_contracts_and_decisions_aligned() {
    let (global, local_types) = simple_protocol();
    let scenario = middleware_heavy_canonical_scenario(&scenario_name("phase19_cross_lane"));

    let direct = run_with_scenario(
        &local_types,
        &global,
        &BTreeMap::new(),
        &scenario,
        &PassthroughHandler,
    )
    .expect("direct run");

    let checkpoint = direct
        .replay
        .checkpoints
        .iter()
        .find(|checkpoint| checkpoint.tick == 4)
        .unwrap_or_else(|| {
            panic!(
                "captured checkpoint at tick 4; available ticks: {:?}; checkpoint_writes={}; checkpoint_error={:?}",
                direct
                    .replay
                    .checkpoints
                    .iter()
                    .map(|checkpoint| checkpoint.tick)
                    .collect::<Vec<_>>(),
                direct.stats.checkpoint_writes,
                direct.stats.checkpoint_error
            )
        });
    let replayed =
        resume_with_checkpoint_artifact(&scenario, checkpoint, &PassthroughHandler, None, None)
            .expect("resume from checkpoint");

    assert_authoritative_equivalence(&direct, &replayed);
    assert_eq!(
        evaluate_contracts(&direct, &ContractCheckConfig::default()),
        evaluate_contracts(&replayed, &ContractCheckConfig::default())
    );

    let offline = decide_theorem_eligibility(&scenario);
    let direct_runtime = theorem_eligibility_from_result(&direct);
    let replay_runtime = theorem_eligibility_from_result(&replayed);
    assert_eq!(offline, direct_runtime);
    assert_eq!(direct_runtime, replay_runtime);
}

#[test]
fn sweep_results_are_reproducible_across_parallelism() {
    let (global, local_types) = simple_protocol();
    let spec = HarnessSpec::new(local_types, global, sweep_base_scenario());
    let adapter = DirectAdapter::new(&PassthroughHandler);
    let harness = SimulationHarness::new(&adapter);
    let config_serial = SweepConfig {
        batch: telltale_simulator::harness::BatchConfig {
            parallelism: Some(1),
        },
        axes: vec![
            SweepAxis::Seed { values: vec![3, 9] },
            SweepAxis::SchedulerProfile {
                values: vec![
                    TheoremSchedulerProfile::CanonicalExact,
                    TheoremSchedulerProfile::ThreadedExact,
                ],
            },
        ],
    };
    let config_parallel = SweepConfig {
        batch: telltale_simulator::harness::BatchConfig {
            parallelism: Some(4),
        },
        axes: config_serial.axes.clone(),
    };

    let serial = run_sweep(&harness, &spec, &config_serial).expect("serial sweep");
    let parallel = run_sweep(&harness, &spec, &config_parallel).expect("parallel sweep");

    assert_eq!(serial.manifest.runs, parallel.manifest.runs);
    assert_eq!(serial.results, parallel.results);
    assert!(
        compare_sweep_results(&serial, &parallel)
            .differing_runs
            .is_empty(),
        "parallelism changes must not alter authoritative sweep results"
    );
    for (serial_run, parallel_run) in serial
        .results
        .iter()
        .zip(parallel.results.iter())
        .filter_map(|(left, right)| Some((left.as_ref().ok()?, right.as_ref().ok()?)))
    {
        assert_eq!(serial_run.analysis, parallel_run.analysis);
        assert_eq!(
            serial_run.stats.theorem_profile,
            parallel_run.stats.theorem_profile
        );
        assert_eq!(
            serial_run.stats.theorem_progress,
            parallel_run.stats.theorem_progress
        );
    }
}
