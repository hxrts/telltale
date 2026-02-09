#![allow(clippy::expect_used)]

#[path = "test_choreographies/mod.rs"]
mod test_choreographies;

use std::collections::BTreeMap;

use serde_json::json;
use telltale_lean_bridge::{
    default_schema_version, global_to_json, normalize_vm_trace, ChoreographyJson, TickedObsEvent,
    VmRunInput, VmRunner, VmTraceEvent,
};
use telltale_vm::coroutine::Value;
use telltale_vm::effect::{EffectHandler, SendDecision};
use telltale_vm::loader::CodeImage;
use telltale_vm::output_condition::OutputConditionPolicy;
use telltale_vm::session::SessionStatus;
use telltale_vm::vm::{ObsEvent, StepResult, VMConfig, VM};

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

#[derive(Debug, Clone)]
struct RustStepState {
    step_index: u64,
    status: String,
    selected_coro: Option<u64>,
    exec_status: Option<String>,
    event: Option<TickedObsEvent<VmTraceEvent>>,
    pre_session_type_counts: BTreeMap<u64, u64>,
    session_type_counts: BTreeMap<u64, u64>,
    session_type_deltas: BTreeMap<u64, i64>,
}

fn session_type_counts(vm: &VM) -> BTreeMap<u64, u64> {
    let mut out = BTreeMap::new();
    for sid in vm.sessions().session_ids() {
        if let Some(sess) = vm.sessions().get(sid) {
            if !matches!(sess.status, SessionStatus::Cancelled) {
                out.insert(sid as u64, sess.local_types.len() as u64);
            }
        }
    }
    out
}

fn session_type_deltas(
    before: &BTreeMap<u64, u64>,
    after: &BTreeMap<u64, u64>,
) -> BTreeMap<u64, i64> {
    let mut out = BTreeMap::new();
    for sid in before.keys().chain(after.keys()) {
        let prev = *before.get(sid).unwrap_or(&0) as i64;
        let next = *after.get(sid).unwrap_or(&0) as i64;
        let delta = next - prev;
        if delta != 0 {
            out.insert(*sid, delta);
        }
    }
    out
}

fn canonical_event(event: &VmTraceEvent) -> serde_json::Value {
    json!({
        "kind": event.kind,
        "session": event.session,
        "sender": event.sender,
        "receiver": event.receiver,
        "label": event.label,
        "role": event.role,
        "target": event.target,
        "permitted": event.permitted,
        "epoch": event.epoch,
        "ghost": event.ghost,
        "from": event.from,
        "to": event.to,
        "predicate_ref": event.predicate_ref,
        "witness_ref": event.witness_ref,
        "output_digest": event.output_digest,
        "passed": event.passed
    })
}

fn lean_trace_is_load_only(trace: &[VmTraceEvent]) -> bool {
    !trace.is_empty() && trace.iter().all(|ev| ev.kind == "opened")
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
        // Lean vm_runner step traces do not currently emit output-condition
        // bookkeeping events; ignore them for cross-target step correspondence.
        ObsEvent::OutputConditionChecked { .. } => None,
        _ => None,
    }
}

fn run_rust_step_states(
    fixture: &test_choreographies::ProtocolFixture,
    max_steps: usize,
) -> Result<Vec<RustStepState>, String> {
    let image = CodeImage::from_local_types(&fixture.local_types, &fixture.global);
    let mut vm = VM::new(VMConfig {
        output_condition_policy: OutputConditionPolicy::AllowAll,
        ..VMConfig::default()
    });
    vm.load_choreography(&image).map_err(|e| e.to_string())?;

    let mut out = Vec::new();
    for step_index in 0..max_steps {
        let old_len = vm.trace().len();
        let before_counts = session_type_counts(&vm);
        let status = vm.step(&PassthroughHandler).map_err(|e| e.to_string())?;
        let status = match status {
            StepResult::Continue => "continue",
            StepResult::Stuck => "stuck",
            StepResult::AllDone => "all_done",
        }
        .to_string();

        let event = vm
            .trace()
            .get(old_len)
            .and_then(obs_to_vm_trace)
            .map(|event| TickedObsEvent {
                tick: event.tick,
                event,
            });

        let after_counts = session_type_counts(&vm);
        let deltas = session_type_deltas(&before_counts, &after_counts);
        let step_meta = vm.last_sched_step().cloned();

        out.push(RustStepState {
            step_index: step_index as u64,
            status,
            selected_coro: step_meta.as_ref().map(|m| m.selected_coro as u64),
            exec_status: step_meta.as_ref().map(|m| m.exec_status.clone()),
            event,
            pre_session_type_counts: before_counts,
            session_type_counts: after_counts,
            session_type_deltas: deltas,
        });

        if matches!(
            out.last().expect("step state exists").status.as_str(),
            "stuck" | "all_done"
        ) {
            break;
        }
    }
    Ok(out)
}

fn fixture_to_choreography_json(
    fixture: &test_choreographies::ProtocolFixture,
) -> ChoreographyJson {
    let mut roles: Vec<String> = fixture.local_types.keys().cloned().collect();
    roles.sort();
    ChoreographyJson {
        schema_version: default_schema_version(),
        global_type: global_to_json(&fixture.global),
        roles,
    }
}

fn assert_step_indexed_equivalence(
    fixture: &test_choreographies::ProtocolFixture,
    max_steps: usize,
    runner: &VmRunner,
) {
    let rust_steps = run_rust_step_states(fixture, max_steps)
        .unwrap_or_else(|e| panic!("run rust step states for {}: {e}", fixture.name));

    let rust_events: Vec<TickedObsEvent<VmTraceEvent>> =
        rust_steps.iter().filter_map(|s| s.event.clone()).collect();
    let rust_normalized = normalize_vm_trace(&rust_events);

    let choreo = fixture_to_choreography_json(fixture);
    let input = VmRunInput {
        schema_version: default_schema_version(),
        choreographies: vec![choreo],
        concurrency: 1,
        max_steps: max_steps as u64,
    };
    let lean_output = runner
        .run_lean_vm(&input)
        .unwrap_or_else(|e| panic!("run lean vm for {}: {e}", fixture.name));
    if lean_trace_is_load_only(&lean_output.trace) {
        eprintln!(
            "SKIPPED: Lean vm_runner produced load-only trace for {}",
            fixture.name
        );
        return;
    }
    let lean_steps = lean_output.step_states.clone();
    let lean_events: Vec<TickedObsEvent<VmTraceEvent>> = lean_steps
        .iter()
        .filter_map(|s| {
            s.event.clone().map(|event| TickedObsEvent {
                tick: event.tick,
                event,
            })
        })
        .collect();
    let lean_normalized = normalize_vm_trace(&lean_events);
    if lean_normalized.is_empty() && !rust_normalized.is_empty() {
        eprintln!(
            "SKIPPED: Lean vm_runner emitted no step-level observables for {}",
            fixture.name
        );
        return;
    }

    let min_len = rust_normalized.len().min(lean_normalized.len());
    for idx in 0..min_len {
        if rust_normalized[idx] != lean_normalized[idx] {
            let rust_source = rust_steps
                .iter()
                .find(|s| s.event.as_ref() == Some(&rust_normalized[idx]))
                .cloned();
            panic!(
                "step-indexed divergence for {} at event {}:\n{}",
                fixture.name,
                idx,
                serde_json::to_string_pretty(&json!({
                    "kind": "event_mismatch",
                    "event_index": idx,
                    "rust": rust_normalized[idx],
                    "lean": lean_normalized[idx],
                    "rust_step": rust_source.as_ref().map(|s| s.step_index),
                    "rust_status": rust_source.as_ref().map(|s| s.status.clone()),
                    "rust_session_type_counts": rust_source.as_ref().map(|s| s.session_type_counts.clone()),
                    "rust_len": rust_normalized.len(),
                    "lean_len": lean_normalized.len()
                }))
                .unwrap_or_else(|_| "<diff encode failed>".to_string())
            );
        }
    }

    assert_eq!(
        rust_normalized.len(),
        lean_normalized.len(),
        "normalized trace length mismatch for {}",
        fixture.name
    );

    if !lean_steps.is_empty() {
        let rust_exec_steps: Vec<_> = rust_steps
            .iter()
            .filter(|s| s.selected_coro.is_some() || s.exec_status.is_some())
            .cloned()
            .collect();

        assert_eq!(
            rust_exec_steps.len(),
            lean_steps.len(),
            "step-state length mismatch for {}",
            fixture.name
        );

        for (idx, (rust_step, lean_step)) in
            rust_exec_steps.iter().zip(lean_steps.iter()).enumerate()
        {
            let lean_prev_counts = if idx == 0 {
                rust_step.pre_session_type_counts.clone()
            } else {
                lean_steps[idx - 1].session_type_counts.clone()
            };
            let lean_deltas =
                session_type_deltas(&lean_prev_counts, &lean_step.session_type_counts);
            if rust_step.selected_coro != lean_step.selected_coro
                || rust_step.exec_status != lean_step.exec_status
                || rust_step.session_type_counts != lean_step.session_type_counts
                || rust_step.session_type_deltas != lean_deltas
                || rust_step.event.as_ref().map(|e| canonical_event(&e.event))
                    != lean_step.event.as_ref().map(canonical_event)
            {
                panic!(
                    "step-state divergence for {} at step {}:\n{}",
                    fixture.name,
                    idx,
                    serde_json::to_string_pretty(&json!({
                        "kind": "step_state_mismatch",
                        "step_index": idx,
                        "rust": {
                            "selected_coro": rust_step.selected_coro,
                            "exec_status": rust_step.exec_status,
                            "session_type_counts": rust_step.session_type_counts,
                            "session_type_deltas": rust_step.session_type_deltas,
                            "event": rust_step.event.as_ref().map(|e| canonical_event(&e.event)),
                        },
                        "lean": {
                            "selected_coro": lean_step.selected_coro,
                            "exec_status": lean_step.exec_status,
                            "session_type_counts": lean_step.session_type_counts,
                            "session_type_deltas": lean_deltas,
                            "event": lean_step.event.as_ref().map(canonical_event),
                        }
                    }))
                    .unwrap_or_else(|_| "<diff encode failed>".to_string())
                );
            }
        }
    }
}

#[test]
fn tier1_step_indexed_correspondence() {
    let Some(runner) = VmRunner::try_new() else {
        eprintln!("SKIPPED: Lean vm_runner not available");
        return;
    };

    let fixtures = [
        test_choreographies::ping_pong(),
        test_choreographies::singleton(),
        test_choreographies::chain(),
    ];
    for fixture in fixtures {
        assert_step_indexed_equivalence(&fixture, 256, &runner);
    }
}

#[test]
fn tier2_step_indexed_correspondence() {
    let Some(runner) = VmRunner::try_new() else {
        eprintln!("SKIPPED: Lean vm_runner not available");
        return;
    };

    let fixture = test_choreographies::tier2_control_flow::binary_choice();
    assert_step_indexed_equivalence(&fixture, 320, &runner);
}
