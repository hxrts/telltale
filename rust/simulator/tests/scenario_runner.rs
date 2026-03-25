//! Integration tests for scenario runner replay and stats surfaces.

use std::collections::BTreeMap;

use serde_json::json;
use telltale_machine::coroutine::Value;
use telltale_machine::model::effects::{
    EffectFailure, EffectHandler, EffectResult, SendDecision, SendDecisionInput,
};
use telltale_machine::SemanticAuditRecord;
use telltale_simulator::generated::{GeneratedEffectScenario, ScenarioEffectDisposition};
use telltale_simulator::runner::run_with_scenario;
use telltale_simulator::scenario::Scenario;
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

#[test]
fn scenario_result_includes_replay_and_stats() {
    let (global, local_types) = simple_protocol();
    let scenario_toml = r#"
name = "scenario_replay"
roles = ["A", "B"]
steps = 8
concurrency = 2
seed = 123
checkpoint_interval = 2

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
    assert_eq!(result.stats.concurrency, 2);
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
