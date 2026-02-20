//! Integration tests for scenario runner replay and stats surfaces.

use std::collections::BTreeMap;

use telltale_simulator::runner::run_with_scenario;
use telltale_simulator::scenario::Scenario;
use telltale_types::{GlobalType, Label, LocalTypeR};
use telltale_vm::coroutine::Value;
use telltale_vm::effect::{EffectHandler, SendDecision, SendDecisionInput};

#[derive(Debug, Clone, Copy)]
struct PassthroughHandler;

impl EffectHandler for PassthroughHandler {
    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        label: &str,
        _state: &[Value],
    ) -> Result<Value, String> {
        Ok(Value::Str(label.to_string()))
    }

    fn send_decision(&self, input: SendDecisionInput<'_>) -> Result<SendDecision, String> {
        Ok(SendDecision::Deliver(input.payload.unwrap_or(Value::Unit)))
    }

    fn handle_recv(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &mut Vec<Value>,
        _payload: &Value,
    ) -> Result<(), String> {
        Ok(())
    }

    fn handle_choose(
        &self,
        _role: &str,
        _partner: &str,
        labels: &[String],
        _state: &[Value],
    ) -> Result<String, String> {
        labels
            .first()
            .cloned()
            .ok_or_else(|| "no labels available".to_string())
    }

    fn step(&self, _role: &str, _state: &mut Vec<Value>) -> Result<(), String> {
        Ok(())
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
            .filter(|event| matches!(event, telltale_vm::vm::ObsEvent::Invoked { .. }))
            .count()
    );
    assert!(result.replay.effect_trace.len() <= result.replay.obs_trace.len());
}
