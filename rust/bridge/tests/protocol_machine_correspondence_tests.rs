#![allow(clippy::as_conversions, clippy::expect_used)]
//! Rust/Lean protocol machine correspondence tests.

#[path = "test_choreographies/mod.rs"]
mod test_choreographies;

use telltale_bridge::{
    canonical_schema_version, global_to_json, semantic_objects_from_json, ChoreographyJson,
    EffectTraceEvent, OutputConditionTraceEvent, ProtocolMachineRunOutput, ProtocolMachineRunner,
    ProtocolMachineSessionStatus, ProtocolMachineTraceEvent,
};
use telltale_machine::coroutine::Value;
use telltale_machine::model::effects::{
    EffectHandler, EffectResult, SendDecision, SendDecisionInput,
};
use telltale_machine::model::output_condition::OutputConditionPolicy;
use telltale_machine::runtime::loader::CodeImage;
use telltale_machine::ObsEvent;
use telltale_machine::{ProtocolMachine, ProtocolMachineConfig};

fn strict_protocol_machine_runner_required() -> bool {
    std::env::var("TELLTALE_REQUIRE_PROTOCOL_MACHINE_RUNNER")
        .map(|value| value != "0")
        .unwrap_or(false)
}

fn protocol_machine_runner() -> ProtocolMachineRunner {
    if strict_protocol_machine_runner_required() {
        ProtocolMachineRunner::require_available();
    }
    ProtocolMachineRunner::try_new()
        .expect("Lean protocol-machine runner must be available for correspondence tests")
}

#[derive(Debug, thiserror::Error)]
enum ProtocolMachineCorrespondenceError {
    #[error("machine load failed: {0}")]
    Load(String),
    #[error("machine run failed: {0}")]
    Run(String),
}

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

fn obs_to_semantic_audit_event(ev: &ObsEvent) -> Option<ProtocolMachineTraceEvent> {
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

    match ev {
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
        // Lean protocol-machine runner trace export currently models protocol-machine observables, not
        // output-condition bookkeeping. Exclude these from correspondence.
        ObsEvent::OutputConditionChecked { .. } => None,
        _ => None,
    }
}

fn run_rust_vm(
    fixture: &test_choreographies::ProtocolFixture,
    max_steps: usize,
) -> Result<ProtocolMachineRunOutput, ProtocolMachineCorrespondenceError> {
    let image = CodeImage::from_local_types(&fixture.local_types, &fixture.global);
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig {
        output_condition_policy: OutputConditionPolicy::AllowAll,
        ..ProtocolMachineConfig::default()
    });
    machine
        .load_choreography(&image)
        .map_err(|e| ProtocolMachineCorrespondenceError::Load(e.to_string()))?;
    machine
        .run(&PassthroughHandler, max_steps)
        .map_err(|e| ProtocolMachineCorrespondenceError::Run(e.to_string()))?;

    let trace = machine
        .trace()
        .iter()
        .filter_map(obs_to_semantic_audit_event)
        .collect();
    let mut sessions: Vec<_> = machine
        .sessions()
        .session_ids()
        .into_iter()
        .map(|sid| ProtocolMachineSessionStatus {
            schema_version: canonical_schema_version(),
            sid: sid as u64,
            terminal: machine
                .sessions()
                .get(sid)
                .map(|s| {
                    !matches!(
                        s.status,
                        telltale_machine::model::state::SessionStatus::Active
                    )
                })
                .unwrap_or(false),
        })
        .collect();
    sessions.sort_by_key(|session| session.sid);

    let effect_trace = machine
        .effect_trace()
        .iter()
        .map(|e| EffectTraceEvent {
            effect_id: e.effect_id,
            effect_kind: e.effect_kind.clone(),
            inputs: e.inputs.clone(),
            outputs: e.outputs.clone(),
            handler_identity: e.handler_identity.clone(),
            ordering_key: e.ordering_key,
            topology: None,
        })
        .collect();
    let effect_exchanges = machine.effect_exchanges().to_vec();

    let output_condition_trace = machine
        .output_condition_checks()
        .iter()
        .map(|c| OutputConditionTraceEvent {
            predicate_ref: c.meta.predicate_ref.clone(),
            witness_ref: c.meta.witness_ref.clone(),
            output_digest: c.meta.output_digest.clone(),
            passed: c.passed,
        })
        .collect();

    let semantic_objects = semantic_objects_from_json(
        serde_json::to_value(machine.semantic_objects()).expect("encode semantic objects"),
    )
    .expect("decode semantic objects into bridge schema");

    Ok(ProtocolMachineRunOutput {
        schema_version: canonical_schema_version(),
        trace,
        sessions,
        steps_executed: max_steps as u64,
        concurrency: 1,
        status: "ok".to_string(),
        effect_trace,
        effect_exchanges,
        output_condition_trace,
        step_states: Vec::new(),
        semantic_objects,
    })
}

fn fixture_to_choreography_json(
    fixture: &test_choreographies::ProtocolFixture,
) -> telltale_bridge::ChoreographyJson {
    let mut roles: Vec<String> = fixture.local_types.keys().cloned().collect();
    roles.sort();
    ChoreographyJson {
        schema_version: canonical_schema_version(),
        global_type: global_to_json(&fixture.global),
        roles,
    }
}

fn assert_stepwise_prefix_equivalent(
    fixture_name: &str,
    result: &telltale_bridge::ComparisonResult,
) {
    let min_len = result
        .rust_semantic_audit
        .len()
        .min(result.lean_semantic_audit.len());
    for idx in 0..min_len {
        assert_eq!(
            result.rust_semantic_audit[idx], result.lean_semantic_audit[idx],
            "step mismatch for {fixture_name} at index {idx}"
        );
    }
}

#[test]
fn test_protocol_machine_semantic_audit_correspondence_ping_pong() {
    let fixture = test_choreographies::ping_pong();
    let rust_output = run_rust_vm(&fixture, 200).expect("run rust ProtocolMachine");

    let runner = protocol_machine_runner();
    let choreography = fixture_to_choreography_json(&fixture);
    let result = runner
        .compare_execution(&choreography, &rust_output)
        .expect("compare execution");
    assert!(
        result.equivalent,
        "trace mismatch for ping_pong: {:?}",
        result.diff
    );
    assert!(
        result.session_statuses_equivalent,
        "session status mismatch for ping_pong"
    );
    assert_eq!(result.rust_semantic_audit, result.lean_semantic_audit);
}

#[test]
fn test_protocol_machine_semantic_audit_correspondence_all_tier1() {
    let fixtures = [
        test_choreographies::ping_pong(),
        test_choreographies::singleton(),
        test_choreographies::chain(),
    ];

    let runner = protocol_machine_runner();

    for fixture in fixtures {
        let rust_output = run_rust_vm(&fixture, 250)
            .unwrap_or_else(|err| panic!("run rust ProtocolMachine for {}: {err}", fixture.name));
        let choreography = fixture_to_choreography_json(&fixture);
        let result = runner
            .compare_execution(&choreography, &rust_output)
            .unwrap_or_else(|err| panic!("compare execution for {}: {err}", fixture.name));

        assert!(
            result.equivalent,
            "trace mismatch for {}: {:?}",
            fixture.name, result.diff
        );
        assert!(
            result.session_statuses_equivalent,
            "session status mismatch for {}",
            fixture.name
        );
        assert_eq!(result.rust_semantic_audit, result.lean_semantic_audit);

        assert_stepwise_prefix_equivalent(fixture.name, &result);
    }
}

#[test]
fn test_protocol_machine_semantic_audit_correspondence_tier2_to_tier4() {
    let fixtures = [
        test_choreographies::tier2_control_flow::binary_choice(),
        test_choreographies::tier3_distributed::three_party_ack(),
        test_choreographies::tier4_classical::queue_observer(),
    ];

    let runner = protocol_machine_runner();

    for fixture in fixtures {
        let rust_output = run_rust_vm(&fixture, 300)
            .unwrap_or_else(|err| panic!("run rust ProtocolMachine for {}: {err}", fixture.name));
        let choreography = fixture_to_choreography_json(&fixture);
        let result = runner
            .compare_execution(&choreography, &rust_output)
            .unwrap_or_else(|err| panic!("compare execution for {}: {err}", fixture.name));

        assert!(
            result.equivalent,
            "trace mismatch for {}: {:?}",
            fixture.name, result.diff
        );
        assert!(
            result.session_statuses_equivalent,
            "session status mismatch for {}",
            fixture.name
        );
        assert_eq!(result.rust_semantic_audit, result.lean_semantic_audit);
        if fixture.name == "binary_choice" {
            assert_stepwise_prefix_equivalent(fixture.name, &result);
        }
    }
}
