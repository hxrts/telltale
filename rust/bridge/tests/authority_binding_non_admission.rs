#![cfg(not(target_arch = "wasm32"))]
//! The communication-only frontend must refuse authority loss before admission.
use telltale_language::ast::ConversionError;
use telltale_language::{compile_choreography, CompileArtifactsError};
use telltale_machine::coroutine::Value;
use telltale_machine::model::effects::{EffectHandler, EffectResult};
use telltale_machine::runtime::loader::CodeImage;
use telltale_machine::{ProtocolMachine, ProtocolMachineConfig};

struct CommunicationHandler;
impl EffectHandler for CommunicationHandler {
    fn handle_send(&self, _: &str, _: &str, _: &str, _: &[Value]) -> EffectResult<Value> {
        EffectResult::success(Value::Unit)
    }
    fn handle_recv(
        &self,
        _: &str,
        _: &str,
        _: &str,
        _: &mut Vec<Value>,
        _: &Value,
    ) -> EffectResult<()> {
        EffectResult::success(())
    }
    fn handle_choose(&self, _: &str, _: &str, _: &[String], _: &[Value]) -> EffectResult<String> {
        unreachable!("plain single-message fixture has no choice")
    }
    fn step(&self, _: &str, _: &mut Vec<Value>) -> EffectResult<()> {
        EffectResult::success(())
    }
}

#[test]
fn unsupported_authority_never_admits_but_plain_communication_loads_real_machine() {
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    let source =
        include_str!("../../runtime/tests/ui/authority_pass/choice_observational_binding.tell");
    let compiled = compile_choreography(source).unwrap();
    // Both artifact requests retain the original AST, unlike a bare LocalTypeR.
    assert!(
        matches!(compiled.global_type_json(), Err(CompileArtifactsError::Conversion(ConversionError::UnsupportedFeature { feature, .. })) if feature == "AuthorityBinding")
    );
    assert!(
        matches!(compiled.local_type_r_json(), Err(CompileArtifactsError::Conversion(ConversionError::UnsupportedFeature { feature, .. })) if feature == "AuthorityBinding")
    );
    assert_eq!(machine.session_count(), 0);

    let plain =
        compile_choreography("protocol Plain =\n  roles A, B\n  let local = Nothing\n  let alias = local\n  A -> B : Commit\n").unwrap();
    let global = plain.try_global_type().unwrap();
    let locals = plain.try_local_type_r_map().unwrap();
    let image = CodeImage::from_local_types(&locals, &global);
    let owner = machine
        .load_choreography_owned(&image, "actual-original")
        .unwrap();
    assert_eq!(machine.session_count(), 1);
    machine.run(&CommunicationHandler, 32).unwrap();
    machine.close_and_reap_session(owner.session_id()).unwrap();
    assert_eq!(machine.live_session_count(), 0);
}

#[test]
fn explicit_execution_placement_cannot_admit_a_communication_only_image() {
    let machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    let compiled = compile_choreography(
        "protocol Placed =\n  roles A, B\n  let value at B = Nothing\n  A -> B : Commit\n",
    );
    assert!(compiled.is_err());
    assert_eq!(machine.session_count(), 0);
}
