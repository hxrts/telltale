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
use telltale_machine::{ProtocolMachine, ProtocolMachineConfig};
use telltale_types::{GlobalType, Label};

use test_support::PassthroughHandler;

fn strict_protocol_machine_runner_required() -> bool {
    std::env::var("TELLTALE_REQUIRE_PROTOCOL_MACHINE_RUNNER")
        .map(|value| value != "0")
        .unwrap_or(false)
}

#[test]
fn test_lean_semantic_audit_matches_rust() {
    let Some(runner) = ProtocolMachineRunner::try_new() else {
        assert!(
            !strict_protocol_machine_runner_required(),
            "strict protocol-machine runner verification is enabled but the Lean runner is unavailable"
        );
        eprintln!(
            "Lean protocol-machine runner not available. Build with: cd lean && lake build protocol_machine_runner"
        );
        return;
    };

    let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
    let roles = vec!["A".to_string(), "B".to_string()];

    let input = ProtocolMachineRunInput {
        schema_version: canonical_schema_version(),
        choreographies: vec![ChoreographyJson {
            schema_version: canonical_schema_version(),
            global_type: global_to_json(&global),
            roles: roles.clone(),
        }],
        concurrency: 1,
        max_steps: 50,
    };

    let lean_out = runner
        .run(&input)
        .expect("run Lean protocol-machine runner");
    let lean_trace: Vec<(u64, String, String, String, String)> = lean_out
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
        .collect();
    if lean_trace.is_empty() {
        eprintln!("SKIPPED: Lean protocol-machine runner emitted no communication trace");
        return;
    }

    let image = test_support::simple_send_recv_image("A", "B", "msg");
    let handler = PassthroughHandler;
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    machine.load_choreography(&image).expect("load image");
    machine.run(&handler, 50).expect("run machine");

    let rust_trace: Vec<(u64, String, String, String, String)> = normalize_trace(machine.trace())
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
        .collect();

    assert_eq!(lean_trace, rust_trace, "Lean and Rust traces diverged");

    let rust_slice = machine.refinement_slice().expect("export refinement slice");
    let rust_session_type_counts = rust_slice
        .sessions
        .iter()
        .map(|session| (session.sid, session.local_type_entries))
        .collect::<std::collections::BTreeMap<_, _>>();
    let rust_buffered_message_counts = rust_slice
        .sessions
        .iter()
        .map(|session| (session.sid, session.buffered_messages))
        .collect::<std::collections::BTreeMap<_, _>>();
    let lean_last_step = lean_out
        .step_states
        .last()
        .expect("lean run should export final step state");
    assert_eq!(lean_last_step.session_type_counts, rust_session_type_counts);
    assert_eq!(
        lean_last_step.buffered_message_counts,
        rust_buffered_message_counts
    );
    assert_eq!(lean_last_step.ready_queue, rust_slice.scheduler.ready_queue);
    assert_eq!(lean_last_step.blocked, rust_slice.scheduler.blocked);
}
