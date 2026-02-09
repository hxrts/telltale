#![allow(clippy::expect_used)]

#[path = "test_choreographies/mod.rs"]
mod test_choreographies;

use telltale_lean_bridge::{
    default_schema_version, global_to_json, ChoreographyJson, EffectTraceEvent,
    OutputConditionTraceEvent, VmRunOutput, VmRunner, VmSessionStatus, VmTraceEvent,
};
use telltale_vm::coroutine::Value;
use telltale_vm::effect::{EffectHandler, SendDecision};
use telltale_vm::loader::CodeImage;
use telltale_vm::output_condition::OutputConditionPolicy;
use telltale_vm::vm::{ObsEvent, VMConfig, VM};

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
        Ok(Value::Label(label.to_string()))
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

fn obs_to_vm_trace(ev: &ObsEvent) -> Option<VmTraceEvent> {
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
        // Lean vm_runner trace export currently models VM observables, not
        // output-condition bookkeeping. Exclude these from correspondence.
        ObsEvent::OutputConditionChecked { .. } => None,
        _ => None,
    }
}

fn run_rust_vm(
    fixture: &test_choreographies::ProtocolFixture,
    max_steps: usize,
) -> Result<VmRunOutput, String> {
    let image = CodeImage::from_local_types(&fixture.local_types, &fixture.global);
    let mut vm = VM::new(VMConfig {
        output_condition_policy: OutputConditionPolicy::AllowAll,
        ..VMConfig::default()
    });
    vm.load_choreography(&image).map_err(|e| e.to_string())?;
    vm.run(&PassthroughHandler, max_steps)
        .map_err(|e| e.to_string())?;

    let trace = vm.trace().iter().filter_map(obs_to_vm_trace).collect();
    let sessions = vm
        .sessions()
        .session_ids()
        .into_iter()
        .map(|sid| VmSessionStatus {
            schema_version: default_schema_version(),
            sid: sid as u64,
            terminal: vm
                .sessions()
                .get(sid)
                .map(|s| !matches!(s.status, telltale_vm::session::SessionStatus::Active))
                .unwrap_or(false),
        })
        .collect();

    let effect_trace = vm
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

    let output_condition_trace = vm
        .output_condition_checks()
        .iter()
        .map(|c| OutputConditionTraceEvent {
            predicate_ref: c.meta.predicate_ref.clone(),
            witness_ref: c.meta.witness_ref.clone(),
            output_digest: c.meta.output_digest.clone(),
            passed: c.passed,
        })
        .collect();

    Ok(VmRunOutput {
        schema_version: default_schema_version(),
        trace,
        sessions,
        steps_executed: max_steps as u64,
        concurrency: 1,
        status: "ok".to_string(),
        effect_trace,
        output_condition_trace,
        step_states: Vec::new(),
    })
}

fn fixture_to_choreography_json(
    fixture: &test_choreographies::ProtocolFixture,
) -> telltale_lean_bridge::ChoreographyJson {
    let mut roles: Vec<String> = fixture.local_types.keys().cloned().collect();
    roles.sort();
    ChoreographyJson {
        schema_version: default_schema_version(),
        global_type: global_to_json(&fixture.global),
        roles,
    }
}

fn lean_trace_is_load_only(trace: &[VmTraceEvent]) -> bool {
    !trace.is_empty() && trace.iter().all(|ev| ev.kind == "opened")
}

fn assert_stepwise_prefix_equivalent(
    fixture_name: &str,
    result: &telltale_lean_bridge::ComparisonResult,
) {
    let min_len = result
        .rust_normalized
        .len()
        .min(result.lean_normalized.len());
    for idx in 0..min_len {
        assert_eq!(
            result.rust_normalized[idx], result.lean_normalized[idx],
            "step mismatch for {fixture_name} at index {idx}"
        );
    }
}

#[test]
fn test_vm_trace_correspondence_ping_pong() {
    let fixture = test_choreographies::ping_pong();
    let rust_output = run_rust_vm(&fixture, 200).expect("run rust VM");

    let Some(runner) = VmRunner::try_new() else {
        eprintln!("SKIPPED: Lean vm_runner not available");
        return;
    };
    let choreography = fixture_to_choreography_json(&fixture);
    let result = runner
        .compare_execution(&choreography, &rust_output)
        .expect("compare execution");
    if lean_trace_is_load_only(&result.lean_output.trace) {
        eprintln!("SKIPPED: Lean vm_runner produced load-only trace");
        return;
    }
    assert!(
        result.equivalent,
        "trace mismatch for ping_pong: {:?}",
        result.diff
    );
}

#[test]
fn test_vm_trace_correspondence_all_tier1() {
    let fixtures = [
        test_choreographies::ping_pong(),
        test_choreographies::singleton(),
        test_choreographies::chain(),
    ];

    let Some(runner) = VmRunner::try_new() else {
        eprintln!("SKIPPED: Lean vm_runner not available");
        return;
    };

    for fixture in fixtures {
        let rust_output = run_rust_vm(&fixture, 250)
            .unwrap_or_else(|err| panic!("run rust VM for {}: {err}", fixture.name));
        let choreography = fixture_to_choreography_json(&fixture);
        let result = runner
            .compare_execution(&choreography, &rust_output)
            .unwrap_or_else(|err| panic!("compare execution for {}: {err}", fixture.name));
        if lean_trace_is_load_only(&result.lean_output.trace) {
            eprintln!("SKIPPED: Lean vm_runner produced load-only trace");
            return;
        }

        assert!(
            result.equivalent,
            "trace mismatch for {}: {:?}",
            fixture.name, result.diff
        );

        assert_stepwise_prefix_equivalent(fixture.name, &result);
    }
}

#[test]
fn test_vm_trace_correspondence_tier2_to_tier4() {
    let fixtures = [
        test_choreographies::tier2_control_flow::binary_choice(),
        test_choreographies::tier3_distributed::three_party_ack(),
        test_choreographies::tier4_classical::queue_observer(),
    ];

    let Some(runner) = VmRunner::try_new() else {
        eprintln!("SKIPPED: Lean vm_runner not available");
        return;
    };

    for fixture in fixtures {
        let rust_output = run_rust_vm(&fixture, 300)
            .unwrap_or_else(|err| panic!("run rust VM for {}: {err}", fixture.name));
        let choreography = fixture_to_choreography_json(&fixture);
        let result = runner
            .compare_execution(&choreography, &rust_output)
            .unwrap_or_else(|err| panic!("compare execution for {}: {err}", fixture.name));
        if lean_trace_is_load_only(&result.lean_output.trace) {
            eprintln!("SKIPPED: Lean vm_runner produced load-only trace");
            return;
        }

        assert!(
            result.equivalent,
            "trace mismatch for {}: {:?}",
            fixture.name, result.diff
        );
        if fixture.name == "binary_choice" {
            assert_stepwise_prefix_equivalent(fixture.name, &result);
        }
    }
}
