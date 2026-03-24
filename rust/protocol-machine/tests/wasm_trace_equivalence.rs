//! Wasm trace equivalence tests.
#![cfg(target_arch = "wasm32")]

use std::collections::BTreeMap;

use wasm_bindgen_test::wasm_bindgen_test;

use telltale_types::{GlobalType, Label, LocalTypeR};
use telltale_protocol_machine::coroutine::Value;
use telltale_protocol_machine::effect::{EffectFailure, EffectHandler, EffectResult};
use telltale_protocol_machine::loader::CodeImage;
use telltale_protocol_machine::trace::normalize_trace;
use telltale_protocol_machine::wasm::WasmVM;
use telltale_protocol_machine::ProtocolMachineSemanticObjects;
use telltale_protocol_machine::{ObsEvent, ProtocolMachine, ProtocolMachineConfig};

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

    let mut wasm_vm = WasmVM::new();
    wasm_vm.load_choreography_json(&spec_json).unwrap();
    wasm_vm.run(max_steps, 1).unwrap();
    let wasm_trace_json = wasm_vm.trace_normalized_json().unwrap();
    let wasm_trace: Vec<ObsEvent> = serde_json::from_str(&wasm_trace_json).unwrap();
    let wasm_semantic_objects_json = wasm_vm.semantic_objects_json().unwrap();
    let wasm_semantic_objects: ProtocolMachineSemanticObjects =
        serde_json::from_str(&wasm_semantic_objects_json).unwrap();

    let image = CodeImage::from_local_types(&local_copy, &global);
    let handler = NoOpHandler;
    let mut vm = ProtocolMachine::new(ProtocolMachineConfig::default());
    vm.load_choreography(&image).unwrap();
    vm.run(&handler, max_steps).unwrap();
    let native_trace = normalize_trace(vm.trace());
    let native_semantic_objects = vm.semantic_objects();

    assert_eq!(wasm_trace, native_trace);
    assert_eq!(
        wasm_semantic_objects.progress_contracts,
        native_semantic_objects.progress_contracts
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
