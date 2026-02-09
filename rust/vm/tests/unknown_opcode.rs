#![cfg(not(target_arch = "wasm32"))]
//! Unknown opcode rejection tests.

use telltale_vm::instr::Instr;

#[test]
fn test_unknown_opcode_rejected() {
    let json = r#"{"UnknownOpcode":{"foo":1}}"#;
    let decoded: Result<Instr, _> = serde_json::from_str(json);
    assert!(decoded.is_err(), "unknown opcode should be rejected");
}
