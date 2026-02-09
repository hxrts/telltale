#![cfg(not(target_arch = "wasm32"))]
//! Canonical-engine ownership guardrails.

#[allow(dead_code, unreachable_pub)]
mod helpers;

use helpers::{simple_send_recv_image, PassthroughHandler};
use telltale_vm::architecture::{EngineRole, CANONICAL_ENGINE, ENGINE_OWNERSHIP};
#[cfg(feature = "multi-thread")]
use telltale_vm::threaded::ThreadedVM;
use telltale_vm::trace::{normalize_trace, with_tick};
use telltale_vm::vm::{VMConfig, VM};

#[test]
fn canonical_engine_declaration_is_unique_and_adapters_defer_semantics() {
    let canonical: Vec<_> = ENGINE_OWNERSHIP
        .iter()
        .filter(|entry| entry.role == EngineRole::Canonical)
        .collect();
    assert_eq!(canonical.len(), 1, "expected exactly one canonical engine");
    assert_eq!(canonical[0].engine, CANONICAL_ENGINE);

    let owner = canonical[0].instruction_semantics_owner;
    for entry in ENGINE_OWNERSHIP
        .iter()
        .filter(|entry| entry.role == EngineRole::AdapterOnly)
    {
        assert_eq!(
            entry.instruction_semantics_owner, owner,
            "adapter {} must defer instruction semantics to canonical owner",
            entry.engine
        );
    }
}

#[cfg(feature = "multi-thread")]
#[test]
fn threaded_adapter_observably_matches_canonical_engine_on_smoke_protocol() {
    let image = simple_send_recv_image("A", "B", "m");
    let handler = PassthroughHandler;

    let mut canonical = VM::new(VMConfig::default());
    canonical
        .load_choreography(&image)
        .expect("load canonical choreography");
    canonical.run(&handler, 64).expect("canonical run");

    let mut adapter = ThreadedVM::with_workers(VMConfig::default(), 2);
    adapter
        .load_choreography(&image)
        .expect("load adapter choreography");
    adapter.run(&handler, 64).expect("adapter run");

    let canonical_norm: Vec<_> = normalize_trace(canonical.trace())
        .iter()
        .map(canonicalize_event)
        .collect();
    let adapter_norm: Vec<_> = normalize_trace(adapter.trace())
        .iter()
        .map(canonicalize_event)
        .collect();
    assert_eq!(
        canonical_norm, adapter_norm,
        "adapter observable semantics must match canonical engine"
    );
}

fn canonicalize_event(event: &telltale_vm::vm::ObsEvent) -> telltale_vm::vm::ObsEvent {
    match event {
        telltale_vm::vm::ObsEvent::OutputConditionChecked {
            predicate_ref,
            witness_ref,
            passed,
            ..
        } => telltale_vm::vm::ObsEvent::OutputConditionChecked {
            tick: 0,
            predicate_ref: predicate_ref.clone(),
            witness_ref: witness_ref.clone(),
            output_digest: "normalized".to_string(),
            passed: *passed,
        },
        other => with_tick(other, 0),
    }
}
