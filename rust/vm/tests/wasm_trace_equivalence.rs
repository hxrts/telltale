//! Wasm trace equivalence tests.
#![cfg(target_arch = "wasm32")]

use std::collections::BTreeMap;

use wasm_bindgen_test::wasm_bindgen_test;

use telltale_types::{GlobalType, Label, LocalTypeR};
use telltale_vm::effect::EffectHandler;
use telltale_vm::loader::CodeImage;
use telltale_vm::trace::normalize_trace;
use telltale_vm::vm::{ObsEvent, VMConfig, VM};
use telltale_vm::wasm::WasmVM;
use telltale_vm::coroutine::Value;

struct NoOpHandler;

impl EffectHandler for NoOpHandler {
    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &[Value],
    ) -> Result<Value, String> {
        Ok(Value::Unit)
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
            .ok_or_else(|| "no labels available".into())
    }

    fn step(&self, _role: &str, _state: &mut Vec<Value>) -> Result<(), String> {
        Ok(())
    }
}

#[wasm_bindgen_test]
fn test_wasm_trace_matches_vm() {
    let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
    let mut locals = BTreeMap::new();
    locals.insert(
        "A".to_string(),
        LocalTypeR::Send {
            partner: "B".into(),
            branches: vec![(Label::new("msg"), None, LocalTypeR::End)],
        },
    );
    locals.insert(
        "B".to_string(),
        LocalTypeR::Recv {
            partner: "A".into(),
            branches: vec![(Label::new("msg"), None, LocalTypeR::End)],
        },
    );

    let spec = serde_json::json!({
        "local_types": locals.clone(),
        "global_type": global.clone(),
    });
    let spec_json = serde_json::to_string(&spec).unwrap();

    let mut wasm_vm = WasmVM::new();
    wasm_vm.load_choreography_json(&spec_json).unwrap();
    wasm_vm.run(50, 1).unwrap();
    let wasm_trace_json = wasm_vm.trace_normalized_json().unwrap();
    let wasm_trace: Vec<ObsEvent> = serde_json::from_str(&wasm_trace_json).unwrap();

    let image = CodeImage::from_local_types(&locals, &global);
    let handler = NoOpHandler;
    let mut vm = VM::new(VMConfig::default());
    vm.load_choreography(&image).unwrap();
    vm.run(&handler, 50).unwrap();
    let native_trace = normalize_trace(vm.trace());

    assert_eq!(wasm_trace, native_trace);
}
