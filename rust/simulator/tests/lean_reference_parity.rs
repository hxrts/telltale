//! Parity tests between Rust simulator runs and Lean reference simulation APIs.
#![allow(clippy::expect_used)]

use std::collections::BTreeMap;

use telltale_lean_bridge::{
    compute_trace_diff, default_schema_version, global_to_json, local_to_json, normalize_vm_trace,
    SimRunInput, SimRunOutput, SimTraceValidation, TickedObsEvent, VmRunner, VmRunnerError,
    VmTraceEvent,
};
use telltale_simulator::runner::{run_with_scenario, ScenarioResult};
use telltale_simulator::scenario::Scenario;
use telltale_types::{GlobalType, Label, LocalTypeR};
use telltale_vm::coroutine::Value;
use telltale_vm::effect::{EffectHandler, SendDecision};
use telltale_vm::vm::ObsEvent;

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

    fn send_decision(
        &self,
        _sid: usize,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &[Value],
        payload: Option<Value>,
    ) -> Result<SendDecision, String> {
        Ok(SendDecision::Deliver(payload.unwrap_or(Value::Unit)))
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

struct SimFixture {
    name: &'static str,
    global: GlobalType,
    local_types: BTreeMap<String, LocalTypeR>,
    scenario: Scenario,
}

fn base_scenario(name: &str, roles: &[&str], steps: u64) -> Scenario {
    let role_list = roles
        .iter()
        .map(|r| format!("\"{r}\""))
        .collect::<Vec<_>>()
        .join(", ");
    let toml = format!(
        r#"
name = "{name}"
roles = [{role_list}]
steps = {steps}
concurrency = 1
seed = 7

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

fn ping_pong_loop_fixture() -> SimFixture {
    let global = GlobalType::mu(
        "loop",
        GlobalType::send(
            "A",
            "B",
            Label::new("ping"),
            GlobalType::send("B", "A", Label::new("pong"), GlobalType::var("loop")),
        ),
    );

    let mut local_types = BTreeMap::new();
    local_types.insert(
        "A".to_string(),
        LocalTypeR::mu(
            "loop",
            LocalTypeR::send(
                "B",
                Label::new("ping"),
                LocalTypeR::recv("B", Label::new("pong"), LocalTypeR::var("loop")),
            ),
        ),
    );
    local_types.insert(
        "B".to_string(),
        LocalTypeR::mu(
            "loop",
            LocalTypeR::recv(
                "A",
                Label::new("ping"),
                LocalTypeR::send("A", Label::new("pong"), LocalTypeR::var("loop")),
            ),
        ),
    );

    SimFixture {
        name: "sim_parity_ping_pong",
        global,
        local_types,
        scenario: base_scenario("sim_parity_ping_pong", &["A", "B"], 16),
    }
}

fn three_role_ring_fixture() -> SimFixture {
    let global = GlobalType::mu(
        "loop",
        GlobalType::send(
            "A",
            "B",
            Label::new("ab"),
            GlobalType::send(
                "B",
                "C",
                Label::new("bc"),
                GlobalType::send("C", "A", Label::new("ca"), GlobalType::var("loop")),
            ),
        ),
    );

    let mut local_types = BTreeMap::new();
    local_types.insert(
        "A".to_string(),
        LocalTypeR::mu(
            "loop",
            LocalTypeR::send(
                "B",
                Label::new("ab"),
                LocalTypeR::recv("C", Label::new("ca"), LocalTypeR::var("loop")),
            ),
        ),
    );
    local_types.insert(
        "B".to_string(),
        LocalTypeR::mu(
            "loop",
            LocalTypeR::recv(
                "A",
                Label::new("ab"),
                LocalTypeR::send("C", Label::new("bc"), LocalTypeR::var("loop")),
            ),
        ),
    );
    local_types.insert(
        "C".to_string(),
        LocalTypeR::mu(
            "loop",
            LocalTypeR::recv(
                "B",
                Label::new("bc"),
                LocalTypeR::send("A", Label::new("ca"), LocalTypeR::var("loop")),
            ),
        ),
    );

    SimFixture {
        name: "sim_parity_ring",
        global,
        local_types,
        scenario: base_scenario("sim_parity_ring", &["A", "B", "C"], 18),
    }
}

fn unsupported_operation(stderr: &str) -> bool {
    stderr.contains("unknown operation")
        || stderr.contains("unsupported operation")
        || stderr.contains("runSimulation")
        || stderr.contains("validateSimulationTrace")
        || stderr.contains("missing choreographies")
}

fn run_reference_or_skip(
    runner: &VmRunner,
    input: &SimRunInput,
    fixture_name: &str,
) -> Option<SimRunOutput> {
    match runner.run_reference_simulation(input) {
        Ok(out) => Some(out),
        Err(VmRunnerError::ProcessFailed { stderr, .. }) if unsupported_operation(&stderr) => {
            eprintln!(
                "SKIPPED: Lean vm_runner does not support runSimulation yet ({fixture_name})"
            );
            None
        }
        Err(err) => panic!("run_reference_simulation failed for {fixture_name}: {err}"),
    }
}

fn validate_sim_trace_or_skip(
    runner: &VmRunner,
    trace: &[VmTraceEvent],
    fixture_name: &str,
) -> Option<SimTraceValidation> {
    match runner.validate_simulation_trace(trace) {
        Ok(out) => Some(out),
        Err(VmRunnerError::ProcessFailed { stderr, .. }) if unsupported_operation(&stderr) => {
            eprintln!(
                "SKIPPED: Lean vm_runner does not support validateSimulationTrace yet ({fixture_name})"
            );
            None
        }
        Err(err) => panic!("validate_simulation_trace failed for {fixture_name}: {err}"),
    }
}

fn obs_to_vm_trace(event: &ObsEvent) -> Option<VmTraceEvent> {
    let mut out = VmTraceEvent {
        schema_version: default_schema_version(),
        kind: String::new(),
        tick: 0,
        session: None,
        sender: None,
        receiver: None,
        label: None,
        role: None,
        target: None,
        permitted: None,
        epoch: None,
        ghost: None,
        from: None,
        to: None,
        predicate_ref: None,
        witness_ref: None,
        output_digest: None,
        passed: None,
    };

    match event {
        ObsEvent::Sent {
            tick,
            session,
            from,
            to,
            label,
            ..
        } => {
            out.kind = "sent".to_string();
            out.tick = *tick;
            out.session = Some(*session as u64);
            out.sender = Some(from.clone());
            out.receiver = Some(to.clone());
            out.label = Some(label.clone());
            Some(out)
        }
        ObsEvent::Received {
            tick,
            session,
            from,
            to,
            label,
            ..
        } => {
            out.kind = "received".to_string();
            out.tick = *tick;
            out.session = Some(*session as u64);
            out.sender = Some(from.clone());
            out.receiver = Some(to.clone());
            out.label = Some(label.clone());
            Some(out)
        }
        ObsEvent::Opened {
            tick,
            session,
            roles,
        } => {
            out.kind = "opened".to_string();
            out.tick = *tick;
            out.session = Some(*session as u64);
            out.role = Some(roles.join(","));
            Some(out)
        }
        ObsEvent::Closed { tick, session } => {
            out.kind = "closed".to_string();
            out.tick = *tick;
            out.session = Some(*session as u64);
            Some(out)
        }
        ObsEvent::Halted { tick, coro_id } => {
            out.kind = "halted".to_string();
            out.tick = *tick;
            out.target = Some(coro_id.to_string());
            Some(out)
        }
        ObsEvent::Faulted { tick, coro_id, .. } => {
            out.kind = "faulted".to_string();
            out.tick = *tick;
            out.target = Some(coro_id.to_string());
            Some(out)
        }
        ObsEvent::OutputConditionChecked {
            tick,
            predicate_ref,
            witness_ref,
            output_digest,
            passed,
        } => {
            out.kind = "output_condition_checked".to_string();
            out.tick = *tick;
            out.predicate_ref = Some(predicate_ref.clone());
            out.witness_ref = witness_ref.clone();
            out.output_digest = Some(output_digest.clone());
            out.passed = Some(*passed);
            Some(out)
        }
        _ => None,
    }
}

fn parity_signal_kind(kind: &str) -> bool {
    matches!(kind, "opened" | "sent" | "received" | "closed")
}

fn to_ticked(trace: &[VmTraceEvent]) -> Vec<TickedObsEvent<VmTraceEvent>> {
    trace
        .iter()
        .cloned()
        .map(|event| TickedObsEvent {
            tick: event.tick,
            event,
        })
        .collect()
}

fn run_rust_scenario(fixture: &SimFixture) -> ScenarioResult {
    run_with_scenario(
        &fixture.local_types,
        &fixture.global,
        &BTreeMap::new(),
        &fixture.scenario,
        &PassthroughHandler,
    )
    .unwrap_or_else(|e| panic!("rust scenario run failed for {}: {e}", fixture.name))
}

fn to_sim_run_input(fixture: &SimFixture) -> SimRunInput {
    let local_types = fixture
        .local_types
        .iter()
        .map(|(role, lt)| (role.clone(), local_to_json(lt)))
        .collect();

    SimRunInput {
        schema_version: default_schema_version(),
        scenario: serde_json::to_value(&fixture.scenario).expect("serialize scenario"),
        global_type: global_to_json(&fixture.global),
        local_types,
        initial_states: BTreeMap::new(),
    }
}

fn assert_reference_parity(fixture: SimFixture) {
    let rust_result = run_rust_scenario(&fixture);

    let Some(runner) = VmRunner::try_new() else {
        eprintln!("SKIPPED: Lean vm_runner not available");
        return;
    };

    let input = to_sim_run_input(&fixture);
    let Some(lean_out) = run_reference_or_skip(&runner, &input, fixture.name) else {
        return;
    };

    let rust_events: Vec<VmTraceEvent> = rust_result
        .replay
        .obs_trace
        .iter()
        .filter_map(obs_to_vm_trace)
        .filter(|event| parity_signal_kind(&event.kind))
        .collect();
    let lean_events: Vec<VmTraceEvent> = lean_out
        .trace
        .iter()
        .filter(|event| parity_signal_kind(&event.kind))
        .cloned()
        .collect();

    if !lean_events.is_empty() && lean_events.iter().all(|event| event.kind == "opened") {
        eprintln!(
            "SKIPPED: Lean runSimulation returned load-only trace for {}",
            fixture.name
        );
        return;
    }

    assert!(
        !rust_events.is_empty(),
        "Rust simulator produced no parity-signal events for {}",
        fixture.name
    );
    assert!(
        !lean_events.is_empty(),
        "Lean reference simulator produced no parity-signal events for {}",
        fixture.name
    );

    let rust_ticked = to_ticked(&rust_events);
    let lean_ticked = to_ticked(&lean_events);
    let rust_norm = normalize_vm_trace(&rust_ticked);
    let lean_norm = normalize_vm_trace(&lean_ticked);

    let diff = compute_trace_diff(&rust_norm, &lean_norm);
    assert_eq!(
        rust_norm, lean_norm,
        "reference parity mismatch for {}: {:?}",
        fixture.name, diff
    );

    assert!(
        rust_result.violations.is_empty(),
        "rust scenario had unexpected violations for {}",
        fixture.name
    );
    assert!(
        lean_out.violations.is_empty(),
        "lean reference simulation had unexpected violations for {}",
        fixture.name
    );
}

#[test]
fn test_reference_simulator_parity_ping_pong_loop() {
    assert_reference_parity(ping_pong_loop_fixture());
}

#[test]
fn test_reference_simulator_parity_three_role_ring_loop() {
    assert_reference_parity(three_role_ring_fixture());
}

#[test]
fn test_rust_simulator_trace_validates_under_lean_reference_rules() {
    let fixtures = [ping_pong_loop_fixture(), three_role_ring_fixture()];
    let Some(runner) = VmRunner::try_new() else {
        eprintln!("SKIPPED: Lean vm_runner not available");
        return;
    };

    for fixture in fixtures {
        let rust_result = run_rust_scenario(&fixture);
        let rust_events: Vec<VmTraceEvent> = rust_result
            .replay
            .obs_trace
            .iter()
            .filter_map(obs_to_vm_trace)
            .collect();
        let Some(validation) = validate_sim_trace_or_skip(&runner, &rust_events, fixture.name)
        else {
            return;
        };

        assert!(
            validation.valid,
            "Lean reference validation failed for {}: {:?}",
            fixture.name, validation.errors
        );
    }
}
