//! Deterministic LocalTypeR trace corpus tests.
//!
//! These tests run on both native and WASM targets using wasm_bindgen_test's
//! `unsupported = test` fallback.

use std::collections::BTreeMap;

use wasm_bindgen_test::wasm_bindgen_test;

use telltale_machine::coroutine::Value;
use telltale_machine::model::effects::{EffectFailure, EffectHandler, EffectResult};
use telltale_machine::runtime::loader::CodeImage;
use telltale_machine::trace::normalize_trace;
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

#[wasm_bindgen_test(unsupported = test)]
fn test_trace_corpus_send_recv() {
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

    let image = CodeImage::from_local_types(&locals, &global);
    let handler = NoOpHandler;
    let mut vm = ProtocolMachine::new(ProtocolMachineConfig::default());
    vm.load_choreography(&image).unwrap();
    vm.run(&handler, 50).unwrap();

    let trace: Vec<(u64, String, String, String, String)> = normalize_trace(vm.trace())
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
                "sent".into(),
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
                "recv".into(),
                from.clone(),
                to.clone(),
                label.clone(),
            )),
            _ => None,
        })
        .collect();

    let expected = vec![
        (1, "sent".into(), "A".into(), "B".into(), "msg".into()),
        (2, "recv".into(), "A".into(), "B".into(), "msg".into()),
    ];

    assert_eq!(trace, expected);
}
