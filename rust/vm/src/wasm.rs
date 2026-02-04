//! WebAssembly bindings for the VM.

use std::collections::BTreeMap;

use serde::Deserialize;
use wasm_bindgen::prelude::*;

use telltale_types::{GlobalType, LocalTypeR};

use crate::coroutine::Value;
use crate::effect::EffectHandler;
use crate::loader::CodeImage;
use crate::trace::{normalize_trace, strict_trace};
use crate::vm::{ObsEvent, StepResult, VMConfig, VM};

#[derive(Debug, Deserialize)]
struct WasmChoreoSpec {
    local_types: BTreeMap<String, LocalTypeR>,
    global_type: GlobalType,
}

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

/// Wasm wrapper for the VM.
#[wasm_bindgen]
pub struct WasmVM {
    inner: VM,
}

#[wasm_bindgen]
impl WasmVM {
    /// Create a new VM with default configuration.
    #[wasm_bindgen(constructor)]
    pub fn new() -> WasmVM {
        WasmVM {
            inner: VM::new(VMConfig::default()),
        }
    }

    /// Load a choreography from JSON.
    ///
    /// The JSON format is `{ "local_types": { ... }, "global_type": { ... } }`.
    pub fn load_choreography_json(&mut self, json: &str) -> Result<usize, JsValue> {
        let spec: WasmChoreoSpec = serde_json::from_str(json)
            .map_err(|e| JsValue::from_str(&format!("invalid json: {e}")))?;
        let image = CodeImage::from_local_types(&spec.local_types, &spec.global_type);
        self.inner
            .load_choreography(&image)
            .map_err(|e| JsValue::from_str(&e.to_string()))
    }

    /// Execute one scheduler round with concurrency `n`.
    pub fn step_round(&mut self, n: usize) -> Result<String, JsValue> {
        let handler = NoOpHandler;
        let result = self
            .inner
            .step_round(&handler, n)
            .map_err(|e| JsValue::from_str(&e.to_string()))?;
        let label = match result {
            StepResult::Continue => "continue",
            StepResult::Stuck => "stuck",
            StepResult::AllDone => "all_done",
        };
        Ok(label.to_string())
    }

    /// Run the VM for at most `max_rounds` with concurrency `n`.
    pub fn run(&mut self, max_rounds: usize, n: usize) -> Result<(), JsValue> {
        let handler = NoOpHandler;
        self.inner
            .run_concurrent(&handler, max_rounds, n)
            .map_err(|e| JsValue::from_str(&e.to_string()))
    }

    /// Get the raw observable trace as JSON.
    pub fn trace_json(&self) -> Result<String, JsValue> {
        let trace: Vec<ObsEvent> = strict_trace(self.inner.trace());
        serde_json::to_string(&trace).map_err(|e| JsValue::from_str(&e.to_string()))
    }

    /// Get the session-local normalized trace as JSON.
    pub fn trace_normalized_json(&self) -> Result<String, JsValue> {
        let trace = normalize_trace(self.inner.trace());
        serde_json::to_string(&trace).map_err(|e| JsValue::from_str(&e.to_string()))
    }
}
