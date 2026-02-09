#![cfg(not(target_arch = "wasm32"))]
//! Deterministic LocalTypeR trace corpus tests.

use std::collections::BTreeMap;

use telltale_types::{GlobalType, Label, LocalTypeR};
use telltale_vm::coroutine::Value;
use telltale_vm::effect::EffectHandler;
use telltale_vm::loader::CodeImage;
use telltale_vm::trace::normalize_trace;
use telltale_vm::vm::{ObsEvent, VMConfig, VM};

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

#[test]
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
    let mut vm = VM::new(VMConfig::default());
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
