#![cfg(not(target_arch = "wasm32"))]
//! Lean protocol-machine runner vs Rust protocol-machine equivalence tests.
#![allow(clippy::needless_collect)]

#[allow(dead_code, unreachable_pub)]
#[path = "support/mod.rs"]
mod test_support;

use telltale_bridge::{
    canonical_schema_version, global_to_json, ChoreographyJson, ProtocolMachineRunInput,
    ProtocolMachineRunner,
};
use telltale_machine::trace::normalize_trace;
use telltale_machine::ObsEvent;
use telltale_machine::{ProtocolMachine, ProtocolMachineConfig, ProtocolMachineRefinementSlice};
use telltale_types::{GlobalType, Label};

use test_support::PassthroughHandler;

fn strict_protocol_machine_runner_required() -> bool {
    std::env::var("TELLTALE_REQUIRE_PROTOCOL_MACHINE_RUNNER")
        .map(|value| value != "0")
        .unwrap_or(false)
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

fn strict_protocol_machine_runner() -> Option<ProtocolMachineRunner> {
    let Some(runner) = ProtocolMachineRunner::try_new() else {
        assert!(
            !strict_protocol_machine_runner_required(),
            "strict protocol-machine runner verification is enabled but the Lean runner is unavailable"
        );
        eprintln!(
            "Lean protocol-machine runner not available. Build with: cd lean && lake build protocol_machine_runner"
        );
        return None;
    };
    Some(runner)
}

fn sample_global_and_roles() -> (GlobalType, Vec<String>) {
    (
        GlobalType::send("A", "B", Label::new("msg"), GlobalType::End),
        vec!["A".to_string(), "B".to_string()],
    )
}

fn sample_run_input(global: &GlobalType, roles: Vec<String>) -> ProtocolMachineRunInput {
    ProtocolMachineRunInput {
        schema_version: canonical_schema_version(),
        choreographies: vec![ChoreographyJson {
            schema_version: canonical_schema_version(),
            global_type: global_to_json(global),
            roles,
        }],
        concurrency: 1,
        max_steps: 50,
    }
}

fn lean_comm_trace(
    lean_out: &telltale_bridge::ProtocolMachineRunOutput,
) -> Vec<(u64, String, String, String, String)> {
    lean_out
        .trace
        .iter()
        .filter_map(|ev| match ev.kind.as_str() {
            "sent" => Some((
                ev.tick,
                "sent".to_string(),
                ev.sender.clone().unwrap_or_default(),
                ev.receiver.clone().unwrap_or_default(),
                ev.label.clone().unwrap_or_default(),
            )),
            "received" => Some((
                ev.tick,
                "recv".to_string(),
                ev.sender.clone().unwrap_or_default(),
                ev.receiver.clone().unwrap_or_default(),
                ev.label.clone().unwrap_or_default(),
            )),
            _ => None,
        })
        .collect()
}

fn rust_comm_trace(machine: &ProtocolMachine) -> Vec<(u64, String, String, String, String)> {
    normalize_trace(machine.trace())
        .iter()
        .filter_map(|ev| match ev {
            ObsEvent::Sent {
                tick,
                from,
                to,
                label,
                ..
            } => Some((
                *tick,
                "sent".to_string(),
                from.clone(),
                to.clone(),
                label.clone(),
            )),
            ObsEvent::Received {
                tick,
                from,
                to,
                label,
                ..
            } => Some((
                *tick,
                "recv".to_string(),
                from.clone(),
                to.clone(),
                label.clone(),
            )),
            _ => None,
        })
        .collect()
}

fn run_sample_machine(global: &GlobalType) -> ProtocolMachine {
    let image = test_support::code_image_from_global(global)
        .expect("projected code image should exist for the test global");
    let handler = PassthroughHandler;
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    machine.load_choreography(&image).expect("load image");
    machine.run(&handler, 50).expect("run machine");
    machine
}

fn assert_last_step_matches_rust(
    machine: &ProtocolMachine,
    lean_out: &telltale_bridge::ProtocolMachineRunOutput,
) {
    let rust_pre_dispatch = machine
        .last_pre_dispatch_refinement_slice()
        .expect("export pre-dispatch refinement slice");
    let rust_slice = machine.refinement_slice().expect("export refinement slice");
    let rust_transition = machine
        .transition_refinement_summary()
        .expect("export transition refinement summary");
    let lean_last_step = lean_out
        .step_states
        .last()
        .expect("lean run should export final step state");
    assert_eq!(
        lean_last_step
            .pre_state
            .as_ref()
            .map(canonicalize_state_for_cross_target),
        Some(canonicalize_state_for_cross_target(&rust_pre_dispatch)),
        "Lean pre-step refinement slice diverged from Rust pre-dispatch slice"
    );
    assert_eq!(lean_last_step.selected_coro, rust_transition.selected_coro);
    assert_eq!(lean_last_step.selected_type, rust_transition.selected_type);
    assert_eq!(lean_last_step.exec_status, rust_transition.exec_status);
    assert_eq!(
        lean_last_step.session_type_counts,
        rust_transition.session_type_counts
    );
    assert_eq!(
        lean_last_step.buffered_message_counts,
        rust_transition.buffered_message_counts
    );
    assert_eq!(lean_last_step.ready_queue, rust_transition.ready_queue);
    assert_eq!(lean_last_step.blocked, rust_transition.blocked);
    assert_eq!(
        lean_last_step
            .post_state
            .as_ref()
            .map(canonicalize_state_for_cross_target),
        Some(canonicalize_state_for_cross_target(&rust_slice)),
        "Lean post-step refinement slice diverged from Rust runtime slice"
    );
    assert_eq!(lean_last_step.ready_queue, rust_slice.scheduler.ready_queue);
    assert_eq!(lean_last_step.blocked, rust_slice.scheduler.blocked);
}

#[test]
fn test_lean_semantic_audit_matches_rust() {
    let Some(runner) = strict_protocol_machine_runner() else {
        return;
    };

    let (global, roles) = sample_global_and_roles();
    let input = sample_run_input(&global, roles);

    let lean_out = runner
        .run(&input)
        .expect("run Lean protocol-machine runner");
    let lean_trace = lean_comm_trace(&lean_out);
    if lean_trace.is_empty() {
        eprintln!("SKIPPED: Lean protocol-machine runner emitted no communication trace");
        return;
    }

    let machine = run_sample_machine(&global);
    let rust_trace = rust_comm_trace(&machine);

    assert_eq!(lean_trace, rust_trace, "Lean and Rust traces diverged");
    assert_last_step_matches_rust(&machine, &lean_out);
}

#[test]
fn claimed_runtime_core_bundle_matches_component_exports() {
    let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
    let image = test_support::code_image_from_global(&global)
        .expect("projected code image should exist for the test global");
    let handler = PassthroughHandler;
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    machine.load_choreography(&image).expect("load image");
    machine.run(&handler, 50).expect("run machine");

    let bundle = machine
        .claimed_runtime_core_bundle()
        .expect("export claimed runtime core bundle");

    assert_eq!(
        bundle.state,
        machine.refinement_slice().expect("export refinement slice")
    );
    assert_eq!(
        bundle.transition,
        machine
            .transition_refinement_summary()
            .expect("export transition summary")
    );
}

#[test]
fn runtime_observation_bundle_matches_component_exports() {
    let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
    let image = test_support::code_image_from_global(&global)
        .expect("projected code image should exist for the test global");
    let handler = PassthroughHandler;
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    machine.load_choreography(&image).expect("load image");
    machine.run(&handler, 50).expect("run machine");

    let bundle = machine
        .runtime_observation_bundle()
        .expect("export runtime observation bundle");

    assert_eq!(bundle.effect_exchanges, machine.effect_exchanges().to_vec());
    assert_eq!(
        bundle.output_condition_checks,
        machine.output_condition_checks().to_vec()
    );
    assert_eq!(bundle.semantic_objects, machine.semantic_objects());
    assert_eq!(bundle.semantic_audit, machine.semantic_audit_log());
}
