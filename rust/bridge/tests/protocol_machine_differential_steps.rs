#![allow(clippy::as_conversions, clippy::expect_used)]

#[path = "test_choreographies/mod.rs"]
mod test_choreographies;

use std::collections::BTreeMap;

use serde_json::json;
use telltale_bridge::{
    canonical_schema_version, global_to_json, normalize_semantic_audit, ChoreographyJson,
    ProtocolMachineRunInput, ProtocolMachineRunner, ProtocolMachineTraceEvent, TickedObsEvent,
};
use telltale_machine::coroutine::Value;
use telltale_machine::model::effects::{
    EffectHandler, EffectResult, SendDecision, SendDecisionInput,
};
use telltale_machine::model::output_condition::OutputConditionPolicy;
use telltale_machine::model::state::SessionStatus;
use telltale_machine::runtime::loader::CodeImage;
use telltale_machine::{ObsEvent, StepResult};
use telltale_machine::{ProtocolMachine, ProtocolMachineConfig, ProtocolMachineRefinementSlice};
use telltale_theory::projection::project_all;

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
        .expect("Lean protocol-machine runner must be available for differential step tests")
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

#[derive(Debug, Clone)]
struct RustStepState {
    step_index: u64,
    status: String,
    pre_state: ProtocolMachineRefinementSlice,
    post_state: ProtocolMachineRefinementSlice,
    selected_coro: Option<u64>,
    selected_pc: Option<u64>,
    selected_type: Option<serde_json::Value>,
    exec_status: Option<String>,
    event: Option<TickedObsEvent<ProtocolMachineTraceEvent>>,
    pre_session_type_counts: BTreeMap<u64, u64>,
    session_type_counts: BTreeMap<u64, u64>,
    buffered_message_counts: BTreeMap<u64, u64>,
    ready_queue: Vec<u64>,
    blocked: BTreeMap<u64, String>,
    session_type_deltas: BTreeMap<u64, i64>,
}

fn canonicalize_state_for_cross_target(
    slice: &ProtocolMachineRefinementSlice,
) -> ProtocolMachineRefinementSlice {
    let mut canonical = slice.clone();
    let ready: std::collections::BTreeSet<u64> =
        canonical.scheduler.ready_queue.iter().copied().collect();
    for coroutine in &mut canonical.coroutines {
        coroutine.pc = 0;
        match coroutine.status.as_str() {
            "done" | "faulted" | "speculating" => {}
            _ if canonical.scheduler.blocked.contains_key(&coroutine.coro_id) => {
                coroutine.status = "blocked".to_string();
            }
            _ if ready.contains(&coroutine.coro_id) => {
                coroutine.status = "ready".to_string();
            }
            _ => {}
        }
    }
    canonical
}

fn session_type_counts(machine: &ProtocolMachine) -> BTreeMap<u64, u64> {
    let mut out = BTreeMap::new();
    for sid in machine.sessions().session_ids() {
        if let Some(sess) = machine.sessions().get(sid) {
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

fn canonical_event(event: &ProtocolMachineTraceEvent) -> serde_json::Value {
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
        // Lean protocol-machine runner step traces do not currently emit output-condition
        // bookkeeping events; ignore them for cross-target step correspondence.
        ObsEvent::OutputConditionChecked { .. } => None,
        _ => None,
    }
}

fn run_rust_step_states(
    fixture: &test_choreographies::ProtocolFixture,
    max_steps: usize,
) -> Result<Vec<RustStepState>, String> {
    let projected: BTreeMap<String, _> = project_all(&fixture.global)
        .map_err(|e| format!("project fixture global for {}: {e}", fixture.name))?
        .into_iter()
        .collect();
    let local_types = if projected.is_empty() {
        &fixture.local_types
    } else {
        &projected
    };
    let image = CodeImage::from_local_types(local_types, &fixture.global);
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig {
        output_condition_policy: OutputConditionPolicy::AllowAll,
        ..ProtocolMachineConfig::default()
    });
    machine
        .load_choreography(&image)
        .map_err(|e| e.to_string())?;

    let mut out = Vec::new();
    for step_index in 0..max_steps {
        let old_len = machine.trace().len();
        let before_counts = session_type_counts(&machine);
        let status = machine
            .step(&PassthroughHandler)
            .map_err(|e| e.to_string())?;
        let pre_state = machine
            .last_pre_dispatch_refinement_slice()
            .ok_or_else(|| {
                "export pre-dispatch refinement slice: missing step snapshot".to_string()
            })?;
        let status = match status {
            StepResult::Continue => "continue",
            StepResult::Stuck => "stuck",
            StepResult::AllDone => "all_done",
        }
        .to_string();

        let event = machine.trace()[old_len..]
            .iter()
            .find_map(obs_to_semantic_audit_event)
            .map(|event| TickedObsEvent {
                tick: event.tick,
                event,
            });

        let after_counts = session_type_counts(&machine);
        let deltas = session_type_deltas(&before_counts, &after_counts);
        let post_state = machine
            .refinement_slice()
            .map_err(|e| format!("export post-step refinement slice: {e}"))?;
        let transition = machine
            .transition_refinement_summary()
            .map_err(|e| format!("export transition refinement summary: {e}"))?;

        out.push(RustStepState {
            step_index: step_index as u64,
            status,
            pre_state,
            post_state,
            selected_coro: transition.selected_coro,
            selected_pc: transition.selected_pc,
            selected_type: transition.selected_type,
            exec_status: transition.exec_status,
            event,
            pre_session_type_counts: before_counts,
            session_type_counts: after_counts,
            buffered_message_counts: transition.buffered_message_counts,
            ready_queue: transition.ready_queue,
            blocked: transition.blocked,
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
        schema_version: canonical_schema_version(),
        global_type: global_to_json(&fixture.global),
        roles,
    }
}

#[allow(clippy::too_many_lines)]
fn assert_step_indexed_equivalence(
    fixture: &test_choreographies::ProtocolFixture,
    max_steps: usize,
    runner: &ProtocolMachineRunner,
) {
    let rust_steps = run_rust_step_states(fixture, max_steps)
        .unwrap_or_else(|e| panic!("run rust step states for {}: {e}", fixture.name));

    let rust_events: Vec<TickedObsEvent<ProtocolMachineTraceEvent>> =
        rust_steps.iter().filter_map(|s| s.event.clone()).collect();
    let rust_normalized = normalize_semantic_audit(&rust_events);

    let choreo = fixture_to_choreography_json(fixture);
    let input = ProtocolMachineRunInput {
        schema_version: canonical_schema_version(),
        choreographies: vec![choreo],
        concurrency: 1,
        max_steps: max_steps as u64,
    };
    let lean_output = runner
        .run_protocol_machine(&input)
        .unwrap_or_else(|e| panic!("run lean protocol machine for {}: {e}", fixture.name));
    let lean_steps = lean_output.step_states.clone();
    let lean_events: Vec<TickedObsEvent<ProtocolMachineTraceEvent>> = lean_steps
        .iter()
        .filter_map(|s| {
            s.event.clone().map(|event| TickedObsEvent {
                tick: event.tick,
                event,
            })
        })
        .collect();
    let lean_normalized = normalize_semantic_audit(&lean_events);
    assert!(
        !lean_normalized.is_empty() || rust_normalized.is_empty(),
        "Lean protocol-machine runner emitted no step-level observables for {}",
        fixture.name
    );

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
            if lean_step
                .pre_state
                .as_ref()
                .map(canonicalize_state_for_cross_target)
                != Some(canonicalize_state_for_cross_target(&rust_step.pre_state))
                || lean_step
                    .post_state
                    .as_ref()
                    .map(canonicalize_state_for_cross_target)
                    != Some(canonicalize_state_for_cross_target(&rust_step.post_state))
                || rust_step.selected_coro != lean_step.selected_coro
                || rust_step.selected_type != lean_step.selected_type
                || rust_step.exec_status != lean_step.exec_status
                || rust_step.session_type_counts != lean_step.session_type_counts
                || rust_step.buffered_message_counts != lean_step.buffered_message_counts
                || rust_step.ready_queue != lean_step.ready_queue
                || rust_step.blocked != lean_step.blocked
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
                            "pre_state": canonicalize_state_for_cross_target(&rust_step.pre_state),
                            "post_state": canonicalize_state_for_cross_target(&rust_step.post_state),
                            "pre_state_raw": rust_step.pre_state,
                            "post_state_raw": rust_step.post_state,
                            "selected_coro": rust_step.selected_coro,
                            "selected_pc": rust_step.selected_pc,
                            "selected_type": rust_step.selected_type,
                            "exec_status": rust_step.exec_status,
                            "session_type_counts": rust_step.session_type_counts,
                            "buffered_message_counts": rust_step.buffered_message_counts,
                            "ready_queue": rust_step.ready_queue,
                            "blocked": rust_step.blocked,
                            "session_type_deltas": rust_step.session_type_deltas,
                            "event": rust_step.event.as_ref().map(|e| canonical_event(&e.event)),
                        },
                        "lean": {
                            "pre_state": lean_step.pre_state.as_ref().map(canonicalize_state_for_cross_target),
                            "post_state": lean_step.post_state.as_ref().map(canonicalize_state_for_cross_target),
                            "pre_state_raw": lean_step.pre_state,
                            "post_state_raw": lean_step.post_state,
                            "selected_coro": lean_step.selected_coro,
                            "selected_pc": lean_step.selected_pc,
                            "selected_type": lean_step.selected_type,
                            "exec_status": lean_step.exec_status,
                            "session_type_counts": lean_step.session_type_counts,
                            "buffered_message_counts": lean_step.buffered_message_counts,
                            "ready_queue": lean_step.ready_queue,
                            "blocked": lean_step.blocked,
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
    let runner = protocol_machine_runner();

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
    let runner = protocol_machine_runner();

    let fixture = test_choreographies::tier2_control_flow::binary_choice();
    assert_step_indexed_equivalence(&fixture, 320, &runner);
}
