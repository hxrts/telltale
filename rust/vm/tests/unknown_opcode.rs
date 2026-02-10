//! Unknown opcode rejection tests.

use wasm_bindgen_test::wasm_bindgen_test;

use telltale_vm::instr::Instr;

#[wasm_bindgen_test(unsupported = test)]
fn test_unknown_opcode_rejected() {
    let json = r#"{"UnknownOpcode":{"foo":1}}"#;
    let decoded: Result<Instr, _> = serde_json::from_str(json);
    assert!(decoded.is_err(), "unknown opcode should be rejected");
}
