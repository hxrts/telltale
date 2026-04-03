//! Integration tests for scenario runner replay and stats surfaces.

use std::collections::BTreeMap;

use serde_json::json;
use telltale_machine::coroutine::Value;
use telltale_machine::model::effects::{
    EffectFailure, EffectHandler, EffectResult, SendDecision, SendDecisionInput,
};
use telltale_machine::runtime::loader::CodeImage;
use telltale_machine::{ProtocolMachine, ProtocolMachineConfig, SemanticAuditRecord};
use telltale_simulator::backend::SimulationMachine;
use telltale_simulator::execution::{execute_scenario_rounds, ScenarioMiddleware};
use telltale_simulator::generated::{GeneratedEffectScenario, ScenarioEffectDisposition};
use telltale_simulator::harness::derive_initial_states;
use telltale_simulator::property::{PropertyContext, PropertyMonitor};
use telltale_simulator::reconfiguration::{ReconfigurationAction, ReconfigurationEffectKind};
use telltale_simulator::runner::{
    run, run_with_scenario, CriticalCapacityPhase, SchedulerLiftMode,
};
use telltale_simulator::scenario::{
    ExecutionRegime, ResolvedExecutionBackend, Scenario, TheoremAssumptionBundle,
    TheoremEligibility, TheoremEnvelopeProfile, TheoremSchedulerProfile,
};
use telltale_types::{FixedQ32, GlobalType, Label, LocalTypeR};

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

fn finite_protocol() -> (GlobalType, BTreeMap<String, LocalTypeR>) {
    let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);

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

    (global, local_types)
}

fn write_initial_states(
    machine: &mut SimulationMachine,
    sid: usize,
    initial_states: &BTreeMap<String, Vec<FixedQ32>>,
) {
    let coro_info = machine
        .session_coroutines(sid)
        .iter()
        .map(|coro| (coro.id, coro.role.clone()))
        .collect::<Vec<_>>();
    for (coro_id, role) in coro_info {
        let Some(values) = initial_states.get(&role) else {
            continue;
        };
        let encoded = values
            .iter()
            .map(|value| Value::Str(format!("q32:{}", value.to_bits())))
            .collect::<Vec<_>>();
        if !encoded.is_empty() {
            machine
                .overwrite_coroutine_registers(coro_id, 2, &encoded)
                .expect("write coroutine registers");
        }
    }
}

#[test]
fn scenario_result_includes_replay_and_stats() {
    let (global, local_types) = simple_protocol();
    let scenario_toml = r#"
name = "scenario_replay"
roles = ["A", "B"]
steps = 8
seed = 123
checkpoint_interval = 2

[execution]
backend = "canonical"
scheduler_concurrency = 1
worker_threads = 1

[material]
layer = "mean_field"

[material.params]
beta = "1.0"
species = ["up", "down"]
initial_state = ["0.5", "0.5"]
step_size = "0.01"
"#;

    let scenario = Scenario::parse(scenario_toml).expect("parse scenario");
    let result = run_with_scenario(
        &local_types,
        &global,
        &BTreeMap::new(),
        &scenario,
        &PassthroughHandler,
    )
    .expect("scenario run");

    assert_eq!(result.stats.seed, 123);
    assert_eq!(
        result.stats.execution_regime,
        ExecutionRegime::CanonicalExact
    );
    assert_eq!(
        result.stats.theorem_profile.scheduler_profile,
        TheoremSchedulerProfile::CanonicalExact
    );
    assert_eq!(
        result.stats.theorem_profile.envelope_profile,
        TheoremEnvelopeProfile::Exact
    );
    assert_eq!(
        result.stats.theorem_profile.assumption_bundle,
        TheoremAssumptionBundle::FaultFreeTransport
    );
    assert_eq!(
        result.stats.theorem_profile.eligibility,
        TheoremEligibility::Exact
    );
    assert_eq!(result.replay.theorem_profile, result.stats.theorem_profile);
    assert!(result.replay.reconfiguration_trace.is_empty());
    assert_eq!(result.stats.reconfiguration_summary.applied_operations, 0);
    assert_eq!(
        result.stats.theorem_progress.critical_capacity.phase,
        CriticalCapacityPhase::Unsupported
    );
    assert_eq!(
        result.stats.theorem_progress.scheduler_lift.mode,
        SchedulerLiftMode::ProductiveExactOnly
    );
    assert_eq!(result.stats.backend, ResolvedExecutionBackend::Canonical);
    assert_eq!(result.stats.scheduler_concurrency, 1);
    assert_eq!(result.stats.worker_threads, 1);
    assert!(result.stats.rounds_executed > 0);
    assert_eq!(result.stats.total_obs_events, result.replay.obs_trace.len());
    assert_eq!(
        result.stats.total_invoked_events,
        result
            .replay
            .obs_trace
            .iter()
            .filter(|event| matches!(event, telltale_machine::ObsEvent::Invoked { .. }))
            .count()
    );
    assert!(result.replay.effect_trace.len() <= result.replay.obs_trace.len());
    assert!(
        result
            .replay
            .semantic_audit_log
            .iter()
            .any(|record| matches!(
                record,
                SemanticAuditRecord::EffectObservation {
                    effect_interface: Some(_),
                    effect_operation: Some(_),
                    ..
                }
            )),
        "scenario replay should include structured semantic effect observations"
    );
}

#[test]
fn theorem_progress_summary_reports_descent_and_phase_boundary_for_supported_runs() {
    let (global, local_types) = finite_protocol();
    let scenario_toml = r#"
name = "finite_progress_summary"
roles = ["A", "B"]
steps = 4
seed = 5

[execution]
backend = "canonical"
scheduler_concurrency = 1
worker_threads = 1

[theorem]
scheduler_profile = "canonical_exact"
envelope_profile = "exact"
assumption_bundle = "fault_free_transport"
"#;
    let scenario = Scenario::parse(scenario_toml).expect("parse scenario");
    let initial_states =
        BTreeMap::from([("A".to_string(), Vec::new()), ("B".to_string(), Vec::new())]);

    let result = run_with_scenario(
        &local_types,
        &global,
        &initial_states,
        &scenario,
        &PassthroughHandler,
    )
    .expect("finite scenario run");

    assert_eq!(result.stats.theorem_progress.initial_depth_budget, 2);
    assert_eq!(result.stats.theorem_progress.initial_weighted_measure, 4);
    assert_eq!(result.stats.theorem_progress.productive_step_count, 2);
    assert_eq!(result.stats.theorem_progress.remaining_weighted_measure, 0);
    assert_eq!(result.stats.theorem_progress.weighted_measure_consumed, 4);
    assert_eq!(
        result.stats.theorem_progress.scheduler_lift.mode,
        SchedulerLiftMode::ProductiveExactOnly
    );
    assert_eq!(
        result.stats.theorem_progress.critical_capacity.threshold,
        Some(2)
    );
    assert_eq!(
        result.stats.theorem_progress.critical_capacity.phase,
        CriticalCapacityPhase::AtThreshold
    );
}

#[test]
fn theorem_progress_summary_reports_scheduler_lift_for_envelope_runs() {
    let (global, local_types) = finite_protocol();
    let scenario_toml = r#"
name = "finite_threaded_envelope"
roles = ["A", "B"]
steps = 4
seed = 5

[execution]
backend = "threaded"
scheduler_concurrency = 2
worker_threads = 2

[theorem]
scheduler_profile = "threaded_envelope"
envelope_profile = "protocol_machine_envelope_adherence"
assumption_bundle = "fault_free_transport"
"#;
    let scenario = Scenario::parse(scenario_toml).expect("parse scenario");
    let initial_states =
        BTreeMap::from([("A".to_string(), Vec::new()), ("B".to_string(), Vec::new())]);

    let result = run_with_scenario(
        &local_types,
        &global,
        &initial_states,
        &scenario,
        &PassthroughHandler,
    )
    .expect("threaded envelope run");

    assert_eq!(
        result.stats.theorem_progress.scheduler_lift.mode,
        SchedulerLiftMode::ConservativeTotalStepBound
    );
    assert_eq!(
        result
            .stats
            .theorem_progress
            .scheduler_lift
            .total_step_upper_bound,
        Some(8)
    );
}

#[test]
fn theorem_profiles_can_reclassify_one_execution_without_changing_runtime_behavior() {
    let (global, local_types) = simple_protocol();
    let exact_toml = r#"
name = "theorem_exact"
roles = ["A", "B"]
steps = 8
seed = 77

[execution]
backend = "canonical"
scheduler_concurrency = 1
worker_threads = 1

[theorem]
scheduler_profile = "canonical_exact"
envelope_profile = "exact"
assumption_bundle = "fault_free_transport"

[material]
layer = "mean_field"

[material.params]
beta = "1.0"
species = ["up", "down"]
initial_state = ["0.5", "0.5"]
step_size = "0.01"
"#;
    let envelope_toml = r#"
name = "theorem_envelope"
roles = ["A", "B"]
steps = 8
seed = 77

[execution]
backend = "canonical"
scheduler_concurrency = 1
worker_threads = 1

[theorem]
scheduler_profile = "canonical_exact"
envelope_profile = "protocol_machine_envelope_adherence"
assumption_bundle = "fault_free_transport"

[material]
layer = "mean_field"

[material.params]
beta = "1.0"
species = ["up", "down"]
initial_state = ["0.5", "0.5"]
step_size = "0.01"
"#;

    let exact = Scenario::parse(exact_toml).expect("parse exact theorem scenario");
    let envelope = Scenario::parse(envelope_toml).expect("parse envelope theorem scenario");

    let exact_result = run_with_scenario(
        &local_types,
        &global,
        &BTreeMap::new(),
        &exact,
        &PassthroughHandler,
    )
    .expect("exact theorem run");
    let envelope_result = run_with_scenario(
        &local_types,
        &global,
        &BTreeMap::new(),
        &envelope,
        &PassthroughHandler,
    )
    .expect("envelope theorem run");

    assert_eq!(exact_result.trace.records, envelope_result.trace.records);
    assert_eq!(
        exact_result.replay.obs_trace,
        envelope_result.replay.obs_trace
    );
    assert_eq!(
        exact_result.replay.effect_trace,
        envelope_result.replay.effect_trace
    );
    assert_eq!(exact_result.stats.backend, envelope_result.stats.backend);
    assert_eq!(
        exact_result.stats.execution_regime,
        envelope_result.stats.execution_regime
    );
    assert_eq!(
        exact_result.stats.theorem_profile.eligibility,
        TheoremEligibility::Exact
    );
    assert_eq!(
        envelope_result.stats.theorem_profile.eligibility,
        TheoremEligibility::EnvelopeBounded
    );
}

#[test]
fn pure_handoff_reconfiguration_preserves_runtime_behavior_and_enters_replay() {
    let (global, local_types) = finite_protocol();
    let base_toml = r#"
name = "handoff_base"
roles = ["A", "B"]
steps = 4
seed = 21

[execution]
backend = "canonical"
scheduler_concurrency = 1
worker_threads = 1

[theorem]
scheduler_profile = "canonical_exact"
envelope_profile = "exact"
assumption_bundle = "fault_free_transport"
"#;
    let handoff_toml = r#"
name = "handoff_reconfig"
roles = ["A", "B"]
steps = 4
seed = 21

[execution]
backend = "canonical"
scheduler_concurrency = 1
worker_threads = 1

[theorem]
scheduler_profile = "canonical_exact"
envelope_profile = "exact"
assumption_bundle = "observed_transport"

[[reconfigurations]]
trigger = { at_tick = 1 }
action = { type = "handoff", handoff_id = "ownership#1", from_role = "A", to_role = "B" }
"#;
    let initial_states =
        BTreeMap::from([("A".to_string(), Vec::new()), ("B".to_string(), Vec::new())]);
    let base = Scenario::parse(base_toml).expect("parse base scenario");
    let handoff = Scenario::parse(handoff_toml).expect("parse handoff scenario");

    let base_result = run_with_scenario(
        &local_types,
        &global,
        &initial_states,
        &base,
        &PassthroughHandler,
    )
    .expect("base run");
    let handoff_result = run_with_scenario(
        &local_types,
        &global,
        &initial_states,
        &handoff,
        &PassthroughHandler,
    )
    .expect("handoff run");

    assert_eq!(base_result.trace.records, handoff_result.trace.records);
    assert_eq!(
        base_result.replay.obs_trace,
        handoff_result.replay.obs_trace
    );
    assert_eq!(
        base_result.stats.theorem_progress,
        handoff_result.stats.theorem_progress
    );
    assert_eq!(handoff_result.replay.reconfiguration_trace.len(), 1);
    let record = &handoff_result.replay.reconfiguration_trace[0];
    assert_eq!(record.operation_id, "reconfiguration:0");
    assert_eq!(record.tick, 1);
    assert_eq!(record.logical_step, 1);
    assert_eq!(
        record.action,
        ReconfigurationAction::Handoff {
            handoff_id: "ownership#1".to_string(),
            from_role: "A".to_string(),
            to_role: "B".to_string(),
        }
    );
    assert_eq!(
        record.footprint.roles,
        vec!["A".to_string(), "B".to_string()]
    );
    assert_eq!(record.effect.kind, ReconfigurationEffectKind::Pure);
    assert_eq!(
        handoff_result
            .stats
            .reconfiguration_summary
            .applied_operations,
        1
    );
    assert_eq!(
        handoff_result.stats.reconfiguration_summary.pure_operations,
        1
    );
    assert_eq!(
        handoff_result
            .stats
            .reconfiguration_summary
            .transition_budget_consumed,
        0
    );
}

#[test]
fn transition_reconfiguration_budget_is_reported_separately_from_descent() {
    let (global, local_types) = finite_protocol();
    let scenario_toml = r#"
name = "transition_reconfig"
roles = ["A", "B"]
steps = 4
seed = 13

[execution]
backend = "canonical"
scheduler_concurrency = 1
worker_threads = 1

[theorem]
scheduler_profile = "canonical_exact"
envelope_profile = "exact"
assumption_bundle = "observed_transport"

[[reconfigurations]]
trigger = { at_tick = 1 }
effect = { kind = "transition_choreography", budget_cost = 3 }
action = { type = "mode_transition", roles = ["A"], from_mode = "mesh", to_mode = "relay" }
"#;
    let scenario = Scenario::parse(scenario_toml).expect("parse scenario");
    let initial_states =
        BTreeMap::from([("A".to_string(), Vec::new()), ("B".to_string(), Vec::new())]);

    let result = run_with_scenario(
        &local_types,
        &global,
        &initial_states,
        &scenario,
        &PassthroughHandler,
    )
    .expect("run scenario");

    assert_eq!(result.stats.theorem_progress.initial_depth_budget, 2);
    assert_eq!(result.stats.theorem_progress.weighted_measure_consumed, 4);
    assert_eq!(result.stats.reconfiguration_summary.applied_operations, 1);
    assert_eq!(result.stats.reconfiguration_summary.pure_operations, 0);
    assert_eq!(
        result.stats.reconfiguration_summary.transition_operations,
        1
    );
    assert_eq!(
        result
            .stats
            .reconfiguration_summary
            .transition_budget_consumed,
        3
    );
}

#[test]
fn generated_effect_scenario_builder_records_effect_outcomes() {
    let scenario = GeneratedEffectScenario::builder()
        .record_return("Runtime", "acceptInvite", json!({"channel": "abc"}))
        .with_delay_ms(15)
        .record_timeout("Runtime", "acceptInvite")
        .record_stale_late_result("Runtime", "acceptInvite")
        .build();

    assert_eq!(scenario.steps.len(), 3);
    assert_eq!(scenario.steps[0].delay_ms, Some(15));
    assert_eq!(
        scenario.steps[1].disposition,
        ScenarioEffectDisposition::Timeout
    );
    assert_eq!(
        scenario.steps[2].disposition,
        ScenarioEffectDisposition::StaleLateResult
    );
}

#[test]
fn run_samples_initial_state_plus_one_record_per_round() {
    let (global, local_types) = simple_protocol();
    let mut initial_states = BTreeMap::new();
    initial_states.insert("A".to_string(), vec![FixedQ32::half(), FixedQ32::half()]);
    initial_states.insert("B".to_string(), vec![FixedQ32::half(), FixedQ32::half()]);

    let trace = run(
        &local_types,
        &global,
        &initial_states,
        4,
        &PassthroughHandler,
    )
    .expect("round-based run");

    let a_steps = trace
        .records_for_role("A")
        .into_iter()
        .map(|record| record.step)
        .collect::<Vec<_>>();
    let b_steps = trace
        .records_for_role("B")
        .into_iter()
        .map(|record| record.step)
        .collect::<Vec<_>>();

    assert_eq!(a_steps, vec![0, 1, 2, 3]);
    assert_eq!(b_steps, vec![0, 1, 2, 3]);
}

#[test]
fn shared_execution_engine_matches_scenario_runner_semantics() {
    let (global, local_types) = simple_protocol();
    let scenario_toml = r#"
name = "shared_engine_equivalence"
roles = ["A", "B"]
steps = 8
seed = 9

[execution]
backend = "canonical"
scheduler_concurrency = 1
worker_threads = 1

[material]
layer = "mean_field"

[material.params]
beta = "1.0"
species = ["up", "down"]
initial_state = ["0.5", "0.5"]
step_size = "0.01"

[[events]]
[events.trigger]
at_tick = 2

[events.action]
type = "message_delay"
ticks = 2

[network]
base_latency_ms = 1
latency_variance = "0.0"
loss_probability = "0.0"
"#;

    let scenario = Scenario::parse(scenario_toml).expect("parse scenario");
    let result = run_with_scenario(
        &local_types,
        &global,
        &BTreeMap::new(),
        &scenario,
        &PassthroughHandler,
    )
    .expect("scenario run");

    let image = CodeImage::from_local_types(&local_types, &global);
    let mut machine =
        SimulationMachine::Canonical(ProtocolMachine::new(ProtocolMachineConfig::default()));
    let owned = machine
        .load_choreography_owned(&image, "sim/shared-engine-test")
        .expect("load choreography");
    let sid = owned.session_id();

    let initial_states = derive_initial_states(&scenario).expect("derive initial states");
    write_initial_states(&mut machine, sid, &initial_states);

    let middleware = ScenarioMiddleware::from_scenario(
        &scenario,
        &PassthroughHandler,
        machine.clock().tick_duration,
    )
    .expect("build middleware");
    let concurrency = usize::try_from(
        scenario
            .resolved_execution()
            .expect("resolve execution")
            .scheduler_concurrency,
    )
    .expect("concurrency fits usize");
    let max_rounds = scenario.steps.saturating_sub(1);
    let mut monitor = scenario
        .property_monitor()
        .expect("build property monitor")
        .unwrap_or_else(|| PropertyMonitor::new(Vec::new()));

    let execution = execute_scenario_rounds(
        &mut machine,
        &scenario,
        &middleware,
        concurrency,
        max_rounds,
        |machine, _completed_rounds| {
            let session_snapshots = machine.session_snapshots();
            let coroutine_snapshots = machine.coroutines();
            let ctx = PropertyContext {
                tick: machine.clock().tick,
                trace: machine.trace(),
                sessions: &session_snapshots,
                coroutines: &coroutine_snapshots,
            };
            monitor.check(&ctx);
            Ok(())
        },
    )
    .expect("shared engine run");

    assert_eq!(execution.rounds_executed, result.stats.rounds_executed);
    assert_eq!(machine.clock().tick, result.stats.final_tick);
    assert_eq!(machine.trace(), result.replay.obs_trace.as_slice());
    assert_eq!(
        machine.effect_trace(),
        result.replay.effect_trace.as_slice()
    );
    assert_eq!(monitor.violations().len(), result.violations.len());
}
