//! Parity tests between Rust simulator runs and Lean reference simulation APIs.
#![allow(clippy::expect_used)]

use std::collections::BTreeMap;

use serde_json::json;
use telltale_bridge::{
    canonical_schema_version, global_to_json, local_to_json, normalize_semantic_audit,
    ProtocolMachineRunner, ProtocolMachineTraceEvent, SimRunInput, SimRunOutput,
    SimTraceValidation, TickedObsEvent,
};
use telltale_machine::coroutine::Value;
use telltale_machine::model::effects::{
    EffectHandler, EffectResult, SendDecision, SendDecisionInput,
};
use telltale_machine::ObsEvent;
use telltale_simulator::runner::{run_with_scenario, ScenarioResult};
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
        EffectResult::success(
            labels
                .first()
                .cloned()
                .expect("labels should contain at least one branch"),
        )
    }

    fn step(&self, _role: &str, _state: &mut Vec<Value>) -> EffectResult<()> {
        EffectResult::success(())
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

fn strict_simulation_trace_validation_required() -> bool {
    std::env::var("TELLTALE_REQUIRE_SIMULATION_TRACE_VALIDATION")
        .map(|value| value != "0")
        .unwrap_or(false)
}

fn strict_protocol_machine_runner_required() -> bool {
    std::env::var("TELLTALE_REQUIRE_PROTOCOL_MACHINE_RUNNER")
        .map(|value| value != "0")
        .unwrap_or(false)
}

fn run_reference_or_skip(
    runner: &ProtocolMachineRunner,
    input: &SimRunInput,
) -> Option<SimRunOutput> {
    match runner.run_reference_simulation(input) {
        Ok(out) => Some(out),
        Err(err) => panic!("run_reference_simulation failed: {err}"),
    }
}

fn validate_sim_trace_or_skip(
    runner: &ProtocolMachineRunner,
    input: &SimRunInput,
    trace: &[ProtocolMachineTraceEvent],
) -> Option<SimTraceValidation> {
    match runner.validate_simulation_trace(input, trace) {
        Ok(out) => Some(out),
        Err(err) => panic!("validate_simulation_trace failed: {err}"),
    }
}

#[allow(clippy::as_conversions)]
fn obs_to_semantic_audit_event(event: &ObsEvent) -> Option<ProtocolMachineTraceEvent> {
    let mut out = ProtocolMachineTraceEvent {
        schema_version: canonical_schema_version(),
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
        reason: None,
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

fn collect_actions(global: &GlobalType) -> Vec<(String, String, String)> {
    match global {
        GlobalType::End | GlobalType::Var(_) => Vec::new(),
        GlobalType::Mu { body, .. } => collect_actions(body),
        GlobalType::Comm {
            sender,
            receiver,
            branches,
        } => {
            let mut out = Vec::new();
            for (label, cont) in branches {
                out.push((sender.clone(), receiver.clone(), label.name.clone()));
                out.extend(collect_actions(cont));
            }
            out
        }
    }
}

type ExpectedPrefixShape = (
    String,
    Option<String>,
    Option<String>,
    Option<String>,
    Option<String>,
);

fn expected_prefix_shapes(fixture: &SimFixture) -> Vec<ExpectedPrefixShape> {
    let mut expected = vec![(
        "opened".to_string(),
        None,
        None,
        None,
        Some(fixture.global.roles().join(",")),
    )];
    for (sender, receiver, label) in collect_actions(&fixture.global) {
        expected.push((
            "sent".to_string(),
            Some(sender.clone()),
            Some(receiver.clone()),
            Some(label.clone()),
            None,
        ));
        expected.push((
            "received".to_string(),
            Some(sender),
            Some(receiver),
            Some(label),
            None,
        ));
    }
    expected
}

fn active_per_role(local: &LocalTypeR) -> usize {
    match local {
        LocalTypeR::Send { branches, .. } | LocalTypeR::Recv { branches, .. } => {
            1 + branches
                .iter()
                .map(|(_, _, cont)| active_per_role(cont))
                .max()
                .unwrap_or(0)
        }
        LocalTypeR::Mu { body, .. } => active_per_role(body),
        LocalTypeR::Var(_) | LocalTypeR::End => 0,
    }
}

fn active_steps_per_round(fixture: &SimFixture) -> usize {
    fixture
        .local_types
        .values()
        .map(active_per_role)
        .max()
        .unwrap_or(0)
}

fn expected_observable_count(fixture: &SimFixture) -> u64 {
    let steps = usize::try_from(fixture.scenario.steps).expect("scenario steps fit in usize");
    let num_roles = fixture.local_types.len();
    let active_per_round = active_steps_per_round(fixture);
    if steps == 0 || num_roles == 0 {
        return 0;
    }

    let mut invoke_count = 0usize;
    let mut active_count = 0usize;
    let mut step_idx = 1usize;
    let mut emitted = 0usize;
    let max_budget = steps.saturating_mul(num_roles.max(1)).saturating_mul(10);

    for _ in 0..max_budget {
        if step_idx >= steps {
            break;
        }
        emitted += 1;
        invoke_count += 1;
        if invoke_count >= num_roles {
            invoke_count -= num_roles;
            active_count += 1;
            step_idx += 1;
            if active_per_round > 0 && active_count >= active_per_round && step_idx < steps {
                active_count = 0;
                step_idx += 1;
            }
        }
    }

    u64::try_from(emitted).expect("emitted observable count fits in u64")
}

fn canonical_reference_event(
    event: &TickedObsEvent<ProtocolMachineTraceEvent>,
) -> serde_json::Value {
    json!({
        "kind": event.event.kind,
        "tick": event.tick,
        "session": event.event.session,
        "sender": event.event.sender,
        "receiver": event.event.receiver,
        "label": event.event.label,
        "role": event.event.role,
    })
}

fn normalized_reference_trace(
    events: &[ProtocolMachineTraceEvent],
) -> Vec<TickedObsEvent<ProtocolMachineTraceEvent>> {
    let ticked: Vec<_> = events
        .iter()
        .cloned()
        .map(|event| TickedObsEvent {
            tick: event.tick,
            event,
        })
        .collect();
    normalize_semantic_audit(&ticked)
}

fn expected_simulation_artifacts(fixture: &SimFixture) -> serde_json::Value {
    let observable_count = expected_observable_count(fixture);
    json!({
        "mode": "deterministic_reference",
        "steps": fixture.scenario.steps,
        "action_count": collect_actions(&fixture.global).len(),
        "trace_length": observable_count + 1,
        "observable_count": observable_count,
        "num_roles": fixture.local_types.len(),
        "active_steps_per_round": active_steps_per_round(fixture),
        "roles": fixture.global.roles(),
        "actions": collect_actions(&fixture.global)
            .into_iter()
            .map(|(sender, receiver, label)| json!({
                "sender": sender,
                "receiver": receiver,
                "label": label,
            }))
            .collect::<Vec<_>>(),
    })
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
        schema_version: canonical_schema_version(),
        scenario: serde_json::to_value(&fixture.scenario).expect("serialize scenario"),
        global_type: global_to_json(&fixture.global),
        local_types,
        initial_states: BTreeMap::new(),
    }
}

#[allow(clippy::needless_pass_by_value)]
fn assert_reference_execution(fixture: SimFixture) {
    let rust_result = run_rust_scenario(&fixture);

    let Some(runner) = ProtocolMachineRunner::try_new() else {
        eprintln!("SKIPPED: Lean protocol-machine runner not available");
        return;
    };

    let input = to_sim_run_input(&fixture);
    let Some(lean_out) = run_reference_or_skip(&runner, &input) else {
        return;
    };

    let rust_events: Vec<ProtocolMachineTraceEvent> = rust_result
        .replay
        .obs_trace
        .iter()
        .filter_map(obs_to_semantic_audit_event)
        .filter(|event| parity_signal_kind(&event.kind))
        .collect();

    let lean_events: Vec<ProtocolMachineTraceEvent> = lean_out
        .trace
        .iter()
        .filter(|event| parity_signal_kind(&event.kind))
        .cloned()
        .collect();

    assert!(
        !rust_events.is_empty(),
        "Rust simulator produced no observable trace for {}",
        fixture.name
    );
    assert!(
        !lean_events.is_empty(),
        "Lean reference simulator produced no parity-signal events for {}",
        fixture.name
    );

    let expected_prefix = expected_prefix_shapes(&fixture);
    let observed_prefix: Vec<_> = lean_events
        .iter()
        .take(expected_prefix.len())
        .map(|event| {
            (
                event.kind.clone(),
                event.sender.clone(),
                event.receiver.clone(),
                event.label.clone(),
                event.role.clone(),
            )
        })
        .collect();
    assert_eq!(
        observed_prefix, expected_prefix,
        "reference simulation emitted an unexpected action prefix for {}",
        fixture.name
    );
    assert_eq!(
        normalized_reference_trace(&rust_events)
            .iter()
            .map(canonical_reference_event)
            .collect::<Vec<_>>(),
        normalized_reference_trace(&lean_events)
            .iter()
            .map(canonical_reference_event)
            .collect::<Vec<_>>(),
        "reference simulation trace diverged from Rust simulator for {}",
        fixture.name
    );
    assert_eq!(
        lean_out.artifacts,
        expected_simulation_artifacts(&fixture),
        "reference simulation artifacts changed unexpectedly for {}",
        fixture.name
    );

    let validation = runner
        .validate_simulation_trace(&input, &lean_events)
        .expect("lean reference trace should validate under Lean rules");
    assert!(
        validation.valid,
        "Lean reference trace failed self-validation for {}: {:?}",
        fixture.name, validation.errors
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
    assert_reference_execution(ping_pong_loop_fixture());
}

#[test]
fn test_reference_simulator_parity_three_role_ring_loop() {
    assert_reference_execution(three_role_ring_fixture());
}

#[test]
fn test_rust_simulator_trace_validates_under_lean_reference_rules() {
    let fixtures = [ping_pong_loop_fixture(), three_role_ring_fixture()];
    let Some(runner) = ProtocolMachineRunner::try_new() else {
        assert!(
            !strict_simulation_trace_validation_required() && !strict_protocol_machine_runner_required(),
            "strict simulation trace validation is enabled but the protocol-machine runner is unavailable"
        );
        eprintln!("SKIPPED: Lean protocol-machine runner not available");
        return;
    };

    for fixture in fixtures {
        let rust_result = run_rust_scenario(&fixture);
        let input = to_sim_run_input(&fixture);
        let rust_events: Vec<ProtocolMachineTraceEvent> = rust_result
            .replay
            .obs_trace
            .iter()
            .filter_map(obs_to_semantic_audit_event)
            .collect();
        let Some(validation) = validate_sim_trace_or_skip(&runner, &input, &rust_events) else {
            return;
        };

        assert!(
            validation.valid,
            "Lean reference validation failed for {}: {:?}",
            fixture.name, validation.errors
        );
    }
}

#[test]
fn test_lean_reference_validation_rejects_tampered_simulator_trace() {
    let fixture = ping_pong_loop_fixture();
    let Some(runner) = ProtocolMachineRunner::try_new() else {
        assert!(
            !strict_simulation_trace_validation_required() && !strict_protocol_machine_runner_required(),
            "strict simulation trace validation is enabled but the protocol-machine runner is unavailable"
        );
        eprintln!("SKIPPED: Lean protocol-machine runner not available");
        return;
    };

    let rust_result = run_rust_scenario(&fixture);
    let input = to_sim_run_input(&fixture);
    let mut rust_events: Vec<ProtocolMachineTraceEvent> = rust_result
        .replay
        .obs_trace
        .iter()
        .filter_map(obs_to_semantic_audit_event)
        .collect();

    let first_message = rust_events
        .iter_mut()
        .find(|event| event.label.is_some())
        .expect("simulator trace must contain a message event");
    first_message.label = Some("tampered_sim_label".to_string());

    let Some(validation) = validate_sim_trace_or_skip(&runner, &input, &rust_events) else {
        return;
    };

    assert!(
        !validation.valid,
        "tampered simulator trace should fail Lean reference validation"
    );
    assert!(
        !validation.errors.is_empty(),
        "tampered simulator trace should produce structured errors"
    );
    assert!(
        validation
            .errors
            .iter()
            .all(|error| !error.code.trim().is_empty() && !error.message.trim().is_empty()),
        "structured errors should include stable code/message fields: {:?}",
        validation.errors
    );
}
