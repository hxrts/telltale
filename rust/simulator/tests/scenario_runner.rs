//! Integration tests for scenario runner replay and stats surfaces.

use std::collections::BTreeMap;

use serde_json::json;
use telltale_machine::runtime::loader::CodeImage;
use telltale_machine::coroutine::Value;
use telltale_machine::model::effects::{
    EffectFailure, EffectHandler, EffectResult, SendDecision, SendDecisionInput,
};
use telltale_machine::{ProtocolMachine, ProtocolMachineConfig, SemanticAuditRecord};
use telltale_simulator::backend::SimulationMachine;
use telltale_simulator::execution::{execute_scenario_rounds, ScenarioMiddleware};
use telltale_simulator::generated::{GeneratedEffectScenario, ScenarioEffectDisposition};
use telltale_simulator::harness::derive_initial_states;
use telltale_simulator::property::{PropertyContext, PropertyMonitor};
use telltale_simulator::runner::{run, run_with_scenario};
use telltale_simulator::scenario::{ResolvedExecutionBackend, Scenario};
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

fn write_initial_states(machine: &mut SimulationMachine, sid: usize, initial_states: &BTreeMap<String, Vec<FixedQ32>>) {
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
    initial_states.insert(
        "A".to_string(),
        vec![FixedQ32::half(), FixedQ32::half()],
    );
    initial_states.insert(
        "B".to_string(),
        vec![FixedQ32::half(), FixedQ32::half()],
    );

    let trace = run(&local_types, &global, &initial_states, 4, &PassthroughHandler)
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
    let mut machine = SimulationMachine::Canonical(ProtocolMachine::new(ProtocolMachineConfig::default()));
    let owned = machine
        .load_choreography_owned(&image, "sim/shared-engine-test")
        .expect("load choreography");
    let sid = owned.session_id();

    let initial_states = derive_initial_states(&scenario).expect("derive initial states");
    write_initial_states(&mut machine, sid, &initial_states);

    let middleware =
        ScenarioMiddleware::from_scenario(&scenario, &PassthroughHandler, machine.clock().tick_duration)
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
    assert_eq!(machine.effect_trace(), result.replay.effect_trace.as_slice());
    assert_eq!(monitor.violations().len(), result.violations.len());
}
