#![allow(missing_docs)]

use telltale_lean_bridge::ProtocolMachineSemanticObjects;
use telltale_vm::coroutine::Value;
use telltale_vm::effect::{EffectHandler, EffectResult, SendDecision, SendDecisionInput};
use telltale_vm::loader::CodeImage;
use telltale_vm::{ProtocolMachine, ProtocolMachineConfig};

#[derive(Debug, Clone, Copy)]
struct PassthroughHandler;

impl EffectHandler for PassthroughHandler {
    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        label: &str,
        _state: &[Value],
    ) -> EffectResult<Value> {
        EffectResult::success(Value::Str(label.to_string()))
    }

    fn send_decision(&self, input: SendDecisionInput<'_>) -> EffectResult<SendDecision> {
        EffectResult::success(SendDecision::Deliver(input.payload.unwrap_or(Value::Unit)))
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
        EffectResult::success(labels.first().cloned().expect("at least one label"))
    }

    fn step(&self, _role: &str, _state: &mut Vec<Value>) -> EffectResult<()> {
        EffectResult::success(())
    }
}

fn simple_send_recv_image() -> CodeImage {
    let global = telltale_types::GlobalType::send(
        "A",
        "B",
        telltale_types::Label::new("msg"),
        telltale_types::GlobalType::End,
    );
    let mut locals = std::collections::BTreeMap::new();
    locals.insert(
        "A".to_string(),
        telltale_types::LocalTypeR::send(
            "B",
            telltale_types::Label::new("msg"),
            telltale_types::LocalTypeR::End,
        ),
    );
    locals.insert(
        "B".to_string(),
        telltale_types::LocalTypeR::recv(
            "A",
            telltale_types::Label::new("msg"),
            telltale_types::LocalTypeR::End,
        ),
    );
    CodeImage::from_local_types(&locals, &global)
}

#[test]
fn semantic_object_schema_roundtrips_from_protocol_machine_objects() {
    let image = simple_send_recv_image();
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    machine
        .load_choreography(&image)
        .expect("load choreography");
    machine
        .run(&PassthroughHandler, 64)
        .expect("run protocol machine");

    let encoded =
        serde_json::to_value(machine.semantic_objects()).expect("encode protocol-machine objects");
    let decoded: ProtocolMachineSemanticObjects =
        serde_json::from_value(encoded).expect("decode bridge semantic-object schema");

    assert_eq!(
        decoded.schema_version,
        telltale_lean_bridge::SEMANTIC_OBJECTS_SCHEMA_VERSION
    );
    assert!(
        decoded.operation_instances.len() >= decoded.outstanding_effects.len(),
        "semantic-object bridge schema should preserve operation/effect correspondence"
    );
}
