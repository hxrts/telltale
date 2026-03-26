//! Wasm trace equivalence tests.
#![cfg(target_arch = "wasm32")]

use std::collections::BTreeMap;

use wasm_bindgen_test::wasm_bindgen_test;

use telltale_machine::coroutine::Value;
use telltale_machine::model::effects::{EffectFailure, EffectHandler, EffectResult};
use telltale_machine::runtime::loader::CodeImage;
use telltale_machine::runtime::runner::WasmProtocolMachine;
use telltale_machine::trace::normalize_trace;
use telltale_machine::ProtocolMachineSemanticObjects;
use telltale_machine::{ObsEvent, ProtocolMachine, ProtocolMachineConfig};
use telltale_types::{GlobalType, Label, LocalTypeR};

struct NoOpHandler;

impl EffectHandler for NoOpHandler {
    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &[Value],
    ) -> EffectResult<Value> {
        EffectResult::success(Value::Unit)
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
        match labels.first().cloned() {
            Some(label) => EffectResult::success(label),
            None => EffectResult::failure(EffectFailure::invalid_input("no labels available")),
        }
    }

    fn step(&self, _role: &str, _state: &mut Vec<Value>) -> EffectResult<()> {
        EffectResult::success(())
    }
}

fn normalize_owner_id(owner_id: &mut Option<String>) {
    if owner_id.as_deref() == Some("wasm/host") {
        *owner_id = None;
    }
}

fn normalize_semantic_objects(
    mut objects: ProtocolMachineSemanticObjects,
) -> ProtocolMachineSemanticObjects {
    for operation in &mut objects.operation_instances {
        if operation.handler_identity.is_some() {
            operation.handler_identity = Some("<normalized-handler>".to_string());
        }
        normalize_owner_id(&mut operation.owner_id);
    }
    for effect in &mut objects.outstanding_effects {
        effect.handler_identity = "<normalized-handler>".to_string();
        normalize_owner_id(&mut effect.owner_id);
    }
    for read in &mut objects.authoritative_reads {
        normalize_owner_id(&mut read.owner_id);
    }
    for handle in &mut objects.canonical_handles {
        normalize_owner_id(&mut handle.owner_id);
    }
    for publication in &mut objects.publication_events {
        normalize_owner_id(&mut publication.owner_id);
    }
    for binding in &mut objects.prestate_bindings {
        normalize_owner_id(&mut binding.participant_digest);
    }
    for contract in &mut objects.agreement_contracts {
        normalize_owner_id(&mut contract.owner_id);
    }
    for evidence in &mut objects.agreement_evidence {
        normalize_owner_id(&mut evidence.owner_id);
    }
    for state in &mut objects.agreement_states {
        normalize_owner_id(&mut state.owner_id);
    }
    for region in &mut objects.regions {
        normalize_owner_id(&mut region.owner_id);
    }

    objects
        .operation_instances
        .sort_by_key(|value| serde_json::to_string(value).expect("serialize operation"));
    objects.operation_instances.dedup();
    objects
        .outstanding_effects
        .sort_by_key(|value| serde_json::to_string(value).expect("serialize effect"));
    objects.outstanding_effects.dedup();
    objects
        .semantic_handoffs
        .sort_by_key(|value| serde_json::to_string(value).expect("serialize handoff"));
    objects.semantic_handoffs.dedup();
    objects
        .transformation_obligations
        .sort_by_key(|value| serde_json::to_string(value).expect("serialize obligation"));
    objects.transformation_obligations.dedup();
    objects
        .authoritative_reads
        .sort_by_key(|value| serde_json::to_string(value).expect("serialize authoritative read"));
    objects.authoritative_reads.dedup();
    objects
        .observed_reads
        .sort_by_key(|value| serde_json::to_string(value).expect("serialize observed read"));
    objects.observed_reads.dedup();
    objects
        .materialization_proofs
        .sort_by_key(|value| serde_json::to_string(value).expect("serialize proof"));
    objects.materialization_proofs.dedup();
    objects
        .canonical_handles
        .sort_by_key(|value| serde_json::to_string(value).expect("serialize handle"));
    objects.canonical_handles.dedup();
    objects
        .publication_events
        .sort_by_key(|value| serde_json::to_string(value).expect("serialize publication"));
    objects.publication_events.dedup();
    objects
        .prestate_bindings
        .sort_by_key(|value| serde_json::to_string(value).expect("serialize prestate binding"));
    objects.prestate_bindings.dedup();
    objects
        .agreement_profiles
        .sort_by_key(|value| serde_json::to_string(value).expect("serialize agreement profile"));
    objects.agreement_profiles.dedup();
    objects
        .agreement_contracts
        .sort_by_key(|value| serde_json::to_string(value).expect("serialize agreement contract"));
    objects.agreement_contracts.dedup();
    objects
        .agreement_evidence
        .sort_by_key(|value| serde_json::to_string(value).expect("serialize agreement evidence"));
    objects.agreement_evidence.dedup();
    objects
        .agreement_states
        .sort_by_key(|value| serde_json::to_string(value).expect("serialize agreement state"));
    objects.agreement_states.dedup();
    objects
        .regions
        .sort_by_key(|value| serde_json::to_string(value).expect("serialize region"));
    objects.regions.dedup();
    objects
        .progress_contracts
        .sort_by_key(|value| serde_json::to_string(value).expect("serialize progress contract"));
    objects.progress_contracts.dedup();
    objects
        .progress_transitions
        .sort_by_key(|value| serde_json::to_string(value).expect("serialize progress transition"));
    objects.progress_transitions.dedup();
    objects
}

fn assert_wasm_trace_matches_vm(
    global: GlobalType,
    locals: BTreeMap<String, LocalTypeR>,
    max_steps: usize,
) {
    let local_copy = locals.clone();

    let spec = serde_json::json!({
        "local_types": locals,
        "global_type": global.clone(),
    });
    let spec_json = serde_json::to_string(&spec).unwrap();

    let mut wasm_vm = WasmProtocolMachine::new();
    wasm_vm.load_choreography_json(&spec_json).unwrap();
    wasm_vm.run(max_steps, 1).unwrap();
    let wasm_trace_json = wasm_vm.trace_normalized_json().unwrap();
    let wasm_trace: Vec<ObsEvent> = serde_json::from_str(&wasm_trace_json).unwrap();
    let wasm_semantic_objects_json = wasm_vm.semantic_objects_json().unwrap();
    let wasm_semantic_objects: ProtocolMachineSemanticObjects =
        serde_json::from_str(&wasm_semantic_objects_json).unwrap();

    let image = CodeImage::from_local_types(&local_copy, &global);
    let handler = NoOpHandler;
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    machine.load_choreography(&image).unwrap();
    machine.run(&handler, max_steps).unwrap();
    let native_trace = normalize_trace(machine.trace());
    let native_semantic_objects = machine.semantic_objects();

    assert_eq!(wasm_trace, native_trace);
    let wasm_semantic_objects = normalize_semantic_objects(wasm_semantic_objects);
    let native_semantic_objects = normalize_semantic_objects(native_semantic_objects);

    assert_eq!(
        wasm_semantic_objects.operation_instances,
        native_semantic_objects.operation_instances,
        "operation instance parity mismatch",
    );
    assert_eq!(
        wasm_semantic_objects.outstanding_effects,
        native_semantic_objects.outstanding_effects,
        "outstanding effect parity mismatch",
    );
    assert_eq!(
        wasm_semantic_objects.semantic_handoffs,
        native_semantic_objects.semantic_handoffs,
        "semantic handoff parity mismatch",
    );
    assert_eq!(
        wasm_semantic_objects.transformation_obligations,
        native_semantic_objects.transformation_obligations,
        "transformation obligation parity mismatch",
    );
    assert_eq!(
        wasm_semantic_objects.authoritative_reads,
        native_semantic_objects.authoritative_reads,
        "authoritative read parity mismatch",
    );
    assert_eq!(
        wasm_semantic_objects.observed_reads,
        native_semantic_objects.observed_reads,
        "observed read parity mismatch",
    );
    assert_eq!(
        wasm_semantic_objects.materialization_proofs,
        native_semantic_objects.materialization_proofs,
        "materialization proof parity mismatch",
    );
    assert_eq!(
        wasm_semantic_objects.canonical_handles,
        native_semantic_objects.canonical_handles,
        "canonical handle parity mismatch",
    );
    assert_eq!(
        wasm_semantic_objects.publication_events,
        native_semantic_objects.publication_events,
        "publication parity mismatch",
    );
    assert_eq!(
        wasm_semantic_objects.prestate_bindings,
        native_semantic_objects.prestate_bindings,
        "prestate binding parity mismatch",
    );
    assert_eq!(
        wasm_semantic_objects.agreement_profiles,
        native_semantic_objects.agreement_profiles,
        "agreement profile parity mismatch",
    );
    assert_eq!(
        wasm_semantic_objects.agreement_contracts,
        native_semantic_objects.agreement_contracts,
        "agreement contract parity mismatch",
    );
    assert_eq!(
        wasm_semantic_objects.agreement_evidence,
        native_semantic_objects.agreement_evidence,
        "agreement evidence parity mismatch",
    );
    assert_eq!(
        wasm_semantic_objects.agreement_states,
        native_semantic_objects.agreement_states,
        "agreement state parity mismatch",
    );
    assert_eq!(
        wasm_semantic_objects.regions,
        native_semantic_objects.regions,
        "region parity mismatch",
    );
    assert_eq!(
        wasm_semantic_objects.progress_contracts,
        native_semantic_objects.progress_contracts,
        "progress contract parity mismatch",
    );
    assert_eq!(
        wasm_semantic_objects.progress_transitions,
        native_semantic_objects.progress_transitions,
        "progress transition parity mismatch",
    );
}

#[wasm_bindgen_test]
fn test_wasm_trace_matches_vm_tier1_ping_pong() {
    let global = GlobalType::send(
        "A",
        "B",
        Label::new("ping"),
        GlobalType::send("B", "A", Label::new("pong"), GlobalType::End),
    );
    let mut locals = BTreeMap::new();
    locals.insert(
        "A".to_string(),
        LocalTypeR::send(
            "B",
            Label::new("ping"),
            LocalTypeR::recv("B", Label::new("pong"), LocalTypeR::End),
        ),
    );
    locals.insert(
        "B".to_string(),
        LocalTypeR::recv(
            "A",
            Label::new("ping"),
            LocalTypeR::send("A", Label::new("pong"), LocalTypeR::End),
        ),
    );
    assert_wasm_trace_matches_vm(global, locals, 80);
}

#[wasm_bindgen_test]
fn test_wasm_trace_matches_vm_tier2_binary_choice() {
    let global = GlobalType::comm(
        "A",
        "B",
        vec![
            (Label::new("yes"), GlobalType::End),
            (Label::new("no"), GlobalType::End),
        ],
    );
    let mut locals = BTreeMap::new();
    locals.insert(
        "A".to_string(),
        LocalTypeR::send_choice(
            "B",
            vec![
                (Label::new("yes"), None, LocalTypeR::End),
                (Label::new("no"), None, LocalTypeR::End),
            ],
        ),
    );
    locals.insert(
        "B".to_string(),
        LocalTypeR::recv_choice(
            "A",
            vec![
                (Label::new("yes"), None, LocalTypeR::End),
                (Label::new("no"), None, LocalTypeR::End),
            ],
        ),
    );
    assert_wasm_trace_matches_vm(global, locals, 80);
}

#[wasm_bindgen_test]
fn test_wasm_trace_matches_vm_tier3_three_party_ack() {
    let global = GlobalType::send(
        "Leader",
        "Replica1",
        Label::new("proposal"),
        GlobalType::send(
            "Leader",
            "Replica2",
            Label::new("proposal"),
            GlobalType::send(
                "Replica1",
                "Leader",
                Label::new("ack"),
                GlobalType::send("Replica2", "Leader", Label::new("ack"), GlobalType::End),
            ),
        ),
    );
    let mut locals = BTreeMap::new();
    locals.insert(
        "Leader".to_string(),
        LocalTypeR::send(
            "Replica1",
            Label::new("proposal"),
            LocalTypeR::send(
                "Replica2",
                Label::new("proposal"),
                LocalTypeR::recv(
                    "Replica1",
                    Label::new("ack"),
                    LocalTypeR::recv("Replica2", Label::new("ack"), LocalTypeR::End),
                ),
            ),
        ),
    );
    locals.insert(
        "Replica1".to_string(),
        LocalTypeR::recv(
            "Leader",
            Label::new("proposal"),
            LocalTypeR::send("Leader", Label::new("ack"), LocalTypeR::End),
        ),
    );
    locals.insert(
        "Replica2".to_string(),
        LocalTypeR::recv(
            "Leader",
            Label::new("proposal"),
            LocalTypeR::send("Leader", Label::new("ack"), LocalTypeR::End),
        ),
    );
    assert_wasm_trace_matches_vm(global, locals, 120);
}

#[wasm_bindgen_test]
fn test_wasm_trace_matches_vm_tier4_queue_observer() {
    let global = GlobalType::send(
        "Ingress",
        "Queue",
        Label::new("enqueue"),
        GlobalType::send("Queue", "Ingress", Label::new("accepted"), GlobalType::End),
    );
    let mut locals = BTreeMap::new();
    locals.insert(
        "Ingress".to_string(),
        LocalTypeR::send(
            "Queue",
            Label::new("enqueue"),
            LocalTypeR::recv("Queue", Label::new("accepted"), LocalTypeR::End),
        ),
    );
    locals.insert(
        "Queue".to_string(),
        LocalTypeR::recv(
            "Ingress",
            Label::new("enqueue"),
            LocalTypeR::send("Ingress", Label::new("accepted"), LocalTypeR::End),
        ),
    );
    assert_wasm_trace_matches_vm(global, locals, 80);
}
