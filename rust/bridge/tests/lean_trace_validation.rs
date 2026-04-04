#![allow(clippy::expect_used)]
//! Trace validation comparing Rust protocol machine to Lean runner.

#[path = "test_choreographies/mod.rs"]
mod test_choreographies;

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use telltale_bridge::{
    canonical_schema_version, global_to_json, ChoreographyJson, ProtocolMachineRunner,
    ProtocolMachineRunnerError, ProtocolMachineTraceEvent,
};
use telltale_language::ast::convert::{choreography_to_global, local_to_local_r};
use telltale_language::compiler::parser::parse_choreography_file;
use telltale_machine::coroutine::Value;
use telltale_machine::model::effects::{
    EffectHandler, EffectResult, SendDecision, SendDecisionInput,
};
use telltale_machine::model::output_condition::OutputConditionPolicy;
use telltale_machine::runtime::loader::CodeImage;
use telltale_machine::{ObsEvent, ProtocolMachine, ProtocolMachineConfig};

#[derive(Debug)]
enum TraceValidationOutcome {
    Valid,
    Invalid {
        errors: Vec<telltale_bridge::LeanStructuredError>,
    },
}

fn strict_protocol_machine_trace_validation_required() -> bool {
    std::env::var("TELLTALE_REQUIRE_PROTOCOL_MACHINE_TRACE_VALIDATION")
        .map(|value| value != "0")
        .unwrap_or(false)
}

fn strict_protocol_machine_runner_required() -> bool {
    std::env::var("TELLTALE_REQUIRE_PROTOCOL_MACHINE_RUNNER")
        .map(|value| value != "0")
        .unwrap_or(false)
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
        ObsEvent::OutputConditionChecked { .. } => None,
        _ => None,
    }
}

fn run_rust_semantic_audit(
    fixture: &test_choreographies::ProtocolFixture,
    max_steps: usize,
) -> Vec<ProtocolMachineTraceEvent> {
    let image = CodeImage::from_local_types(&fixture.local_types, &fixture.global);
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig {
        output_condition_policy: OutputConditionPolicy::AllowAll,
        ..ProtocolMachineConfig::default()
    });
    machine
        .load_choreography(&image)
        .unwrap_or_else(|err| panic!("load choreography for {}: {err}", fixture.name));
    machine
        .run(&PassthroughHandler, max_steps)
        .unwrap_or_else(|err| panic!("run choreography for {}: {err}", fixture.name));
    machine
        .trace()
        .iter()
        .filter_map(obs_to_semantic_audit_event)
        .collect()
}

fn authority_pass_fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../runtime/tests/ui/authority_pass")
        .join(format!("{name}.tell"))
}

fn code_image_from_choreography(choreography: &telltale_language::ast::Choreography) -> CodeImage {
    let global = choreography_to_global(choreography).expect("convert choreography to global");
    let mut locals = BTreeMap::new();
    for role in &choreography.roles {
        let local = telltale_language::project(choreography, role).expect("project local type");
        let local_r = local_to_local_r(&local).expect("convert local type");
        locals.insert(role.name().to_string(), local_r);
    }
    CodeImage::from_local_types(&locals, &global)
}

fn run_rust_semantic_audit_for_choreography(
    choreography: &telltale_language::ast::Choreography,
    max_steps: usize,
) -> Vec<ProtocolMachineTraceEvent> {
    let image = code_image_from_choreography(choreography);
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig {
        output_condition_policy: OutputConditionPolicy::AllowAll,
        ..ProtocolMachineConfig::default()
    });
    machine
        .load_choreography(&image)
        .expect("load choreography");
    machine
        .run(&PassthroughHandler, max_steps)
        .expect("run choreography");
    machine
        .trace()
        .iter()
        .filter_map(obs_to_semantic_audit_event)
        .collect()
}

fn validate_trace(
    fixture: &test_choreographies::ProtocolFixture,
    trace: &[ProtocolMachineTraceEvent],
) -> Result<TraceValidationOutcome, ProtocolMachineRunnerError> {
    if strict_protocol_machine_trace_validation_required()
        || strict_protocol_machine_runner_required()
    {
        ProtocolMachineRunner::require_available();
    }
    let runner = ProtocolMachineRunner::try_new()
        .expect("Lean protocol-machine runner must be available for trace validation tests");

    let choreography = ChoreographyJson {
        schema_version: canonical_schema_version(),
        global_type: global_to_json(&fixture.global),
        roles: fixture.local_types.keys().cloned().collect(),
    };

    match runner.validate_trace(&[choreography], trace) {
        Ok(validation) if validation.valid => Ok(TraceValidationOutcome::Valid),
        Ok(validation) => Ok(TraceValidationOutcome::Invalid {
            errors: validation.errors,
        }),
        Err(err) => Err(err),
    }
}

fn stable_trace_corpus() -> Vec<test_choreographies::ProtocolFixture> {
    vec![
        test_choreographies::ping_pong(),
        test_choreographies::chain(),
    ]
}

fn tamper_first_label(trace: &mut [ProtocolMachineTraceEvent]) {
    let first_message = trace
        .iter_mut()
        .find(|event| event.label.is_some())
        .expect("trace must contain a message event");
    first_message.label = Some("tampered_label".to_string());
}

#[test]
fn lean_validate_trace_support_matrix_is_explicit() {
    let fixture = test_choreographies::ping_pong();
    let trace = run_rust_semantic_audit(&fixture, 64);
    match validate_trace(&fixture, &trace)
        .expect("validate_trace support probe should not hard-fail")
    {
        TraceValidationOutcome::Valid | TraceValidationOutcome::Invalid { .. } => {}
    }
}

#[test]
fn lean_accepts_rust_protocol_machine_trace_corpus() {
    for fixture in stable_trace_corpus() {
        let trace = run_rust_semantic_audit(&fixture, 128);
        match validate_trace(&fixture, &trace).expect("validate_trace should not hard-fail") {
            TraceValidationOutcome::Valid => {}
            TraceValidationOutcome::Invalid { errors } => panic!(
                "Lean validateTrace rejected accepted Rust trace for {}: {:?}",
                fixture.name, errors
            ),
        }
    }
}

#[test]
fn lean_rejects_tampered_protocol_machine_trace_with_structured_errors() {
    let fixture = test_choreographies::ping_pong();
    let mut trace = run_rust_semantic_audit(&fixture, 64);
    tamper_first_label(&mut trace);

    match validate_trace(&fixture, &trace).expect("validate_trace should not hard-fail") {
        TraceValidationOutcome::Invalid { errors } => {
            assert!(
                !errors.is_empty(),
                "tampered trace should produce structured errors"
            );
            assert!(
                errors
                    .iter()
                    .all(|error| !error.code.trim().is_empty() && !error.message.trim().is_empty()),
                "structured errors should include stable code/message fields: {:?}",
                errors
            );
        }
        TraceValidationOutcome::Valid => {
            panic!("tampered protocol-machine trace unexpectedly validated");
        }
    }
}

#[test]
fn lean_accepts_projectable_authority_control_flow_trace_corpus() {
    if strict_protocol_machine_runner_required() {
        ProtocolMachineRunner::require_available();
    }
    let runner = ProtocolMachineRunner::try_new().expect(
        "Lean protocol-machine runner must be available for authority control-flow trace validation",
    );

    for fixture in [
        "call_plain_communication",
        "choice_observational_binding",
        "loop_authoritative_binding",
        "recursion_authoritative_binding",
    ] {
        let choreography = parse_choreography_file(&authority_pass_fixture(fixture))
            .unwrap_or_else(|err| panic!("parse {fixture}: {err}"));
        choreography
            .validate()
            .unwrap_or_else(|err| panic!("validate {fixture}: {err}"));
        assert!(
            choreography.language_tier_status().session_projectable,
            "{fixture} should remain session-projectable"
        );

        let trace = run_rust_semantic_audit_for_choreography(&choreography, 128);
        let validation = runner
            .validate_trace(
                &[ChoreographyJson {
                    schema_version: canonical_schema_version(),
                    global_type: global_to_json(
                        &choreography_to_global(&choreography)
                            .expect("convert authority control-flow choreography to global"),
                    ),
                    roles: choreography
                        .roles
                        .iter()
                        .map(|role| role.name().to_string())
                        .collect(),
                }],
                &trace,
            )
            .unwrap_or_else(|err| panic!("validate_trace {fixture}: {err}"));
        assert!(
            validation.valid,
            "Lean validateTrace rejected accepted authority control-flow trace for {fixture}: {:?}",
            validation.errors
        );
    }
}
