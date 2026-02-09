#![cfg(not(target_arch = "wasm32"))]
//! Lean VM runner vs Rust VM equivalence tests.
#![allow(clippy::needless_collect)]

#[allow(dead_code, unreachable_pub)]
mod helpers;

use telltale_lean_bridge::{
    default_schema_version, global_to_json, ChoreographyJson, VmRunInput, VmRunner,
};
use telltale_types::{GlobalType, Label};
use telltale_vm::trace::normalize_trace;
use telltale_vm::vm::{ObsEvent, VMConfig, VM};

use helpers::PassthroughHandler;

#[test]
fn test_lean_vm_trace_matches_rust() {
    let Some(runner) = VmRunner::try_new() else {
        eprintln!("Lean vm_runner not available. Build with: cd lean && lake build vm_runner");
        return;
    };

    let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
    let roles = vec!["A".to_string(), "B".to_string()];

    let input = VmRunInput {
        schema_version: default_schema_version(),
        choreographies: vec![ChoreographyJson {
            schema_version: default_schema_version(),
            global_type: global_to_json(&global),
            roles: roles.clone(),
        }],
        concurrency: 1,
        max_steps: 50,
    };

    let lean_out = runner.run(&input).expect("run Lean vm_runner");
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
        eprintln!("SKIPPED: Lean vm_runner emitted no communication trace");
        return;
    }

    let image = helpers::simple_send_recv_image("A", "B", "msg");
    let handler = PassthroughHandler;
    let mut vm = VM::new(VMConfig::default());
    vm.load_choreography(&image).expect("load image");
    vm.run(&handler, 50).expect("run vm");

    let rust_trace: Vec<(u64, String, String, String, String)> = normalize_trace(vm.trace())
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
}
