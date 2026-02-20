#![cfg(not(target_arch = "wasm32"))]
//! Strict Lean-value conformance rejection tests.

use assert_matches::assert_matches;
use std::collections::BTreeMap;
use telltale_types::{GlobalType, Label, LocalTypeR};
use telltale_vm::coroutine::{Fault, Value};
use telltale_vm::instr::{ImmValue, Instr};
use telltale_vm::loader::CodeImage;
use telltale_vm::vm::{VMConfig, VMError, VM};

#[allow(dead_code, unreachable_pub)]
mod helpers;

use helpers::PassthroughHandler;

#[test]
fn legacy_value_variants_are_rejected_by_deserialization() {
    for json in [
        r#"{"Int":7}"#,
        r#"{"Real":"0.5"}"#,
        r#"{"Vec":[1,2,3]}"#,
        r#"{"Label":"msg"}"#,
        r#"{"Json":{"k":"v"}}"#,
        r#"{"Knowledge":{"endpoint":{"sid":0,"role":"A"},"fact":"x"}}"#,
    ] {
        let parsed = serde_json::from_str::<Value>(json);
        assert!(
            parsed.is_err(),
            "legacy value JSON unexpectedly accepted: {json}"
        );
    }
}

#[test]
fn legacy_immediate_variants_are_rejected_by_deserialization() {
    for json in [r#"{"Int":7}"#, r#"{"Real":"0.5"}"#] {
        let parsed = serde_json::from_str::<ImmValue>(json);
        assert!(
            parsed.is_err(),
            "legacy immediate JSON unexpectedly accepted: {json}"
        );
    }
}

#[test]
fn choose_rejects_non_string_label_payload() {
    let mut local_types = BTreeMap::new();
    local_types.insert(
        "A".to_string(),
        LocalTypeR::send_choice(
            "B",
            vec![
                (Label::new("yes"), None, LocalTypeR::End),
                (Label::new("no"), None, LocalTypeR::End),
            ],
        ),
    );
    local_types.insert(
        "B".to_string(),
        LocalTypeR::recv_choice(
            "A",
            vec![
                (Label::new("yes"), None, LocalTypeR::End),
                (Label::new("no"), None, LocalTypeR::End),
            ],
        ),
    );

    let image = CodeImage {
        programs: {
            let mut m = BTreeMap::new();
            m.insert("A".to_string(), vec![Instr::Halt]);
            m.insert(
                "B".to_string(),
                vec![
                    Instr::Choose {
                        chan: 0,
                        table: vec![("yes".into(), 1), ("no".into(), 1)],
                    },
                    Instr::Halt,
                ],
            );
            m
        },
        global_type: GlobalType::comm(
            "A",
            "B",
            vec![
                (Label::new("yes"), GlobalType::End),
                (Label::new("no"), GlobalType::End),
            ],
        ),
        local_types,
    };

    let mut vm = VM::new(VMConfig::default());
    let sid = vm.load_choreography(&image).expect("load choreography");
    vm.sessions_mut()
        .get_mut(sid)
        .expect("session")
        .send("A", "B", Value::Nat(1))
        .expect("inject malformed payload");
    vm.pause_role("A");

    let handler = PassthroughHandler;
    let result = vm.run(&handler, 16);
    assert_matches!(
        result,
        Err(VMError::Fault {
            fault: Fault::TypeViolation { .. },
            ..
        })
    );
}

#[test]
fn tag_rejects_non_fact_shape() {
    let image = CodeImage {
        programs: {
            let mut m = BTreeMap::new();
            m.insert(
                "A".to_string(),
                vec![
                    Instr::Set {
                        dst: 1,
                        val: ImmValue::Str("not-a-fact".to_string()),
                    },
                    Instr::Tag { fact: 1, dst: 2 },
                    Instr::Halt,
                ],
            );
            m
        },
        global_type: GlobalType::End,
        local_types: {
            let mut m = BTreeMap::new();
            m.insert("A".to_string(), LocalTypeR::End);
            m
        },
    };

    let mut vm = VM::new(VMConfig::default());
    vm.load_choreography(&image).expect("load choreography");

    let handler = PassthroughHandler;
    let result = vm.run(&handler, 8);
    assert_matches!(
        result,
        Err(VMError::Fault {
            fault: Fault::Transfer { .. },
            ..
        })
    );
}
