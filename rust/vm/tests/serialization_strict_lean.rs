//! Serialization/schema conformance for strict Lean value surface.

use std::collections::BTreeSet;

use wasm_bindgen_test::wasm_bindgen_test;

use telltale_vm::coroutine::Value;
use telltale_vm::instr::{Endpoint, ImmValue};

#[wasm_bindgen_test(unsupported = test)]
fn lean_value_variants_roundtrip() {
    let values = vec![
        Value::Unit,
        Value::Nat(7),
        Value::Bool(true),
        Value::Str("hello".to_string()),
        Value::Prod(Box::new(Value::Nat(1)), Box::new(Value::Str("x".to_string()))),
        Value::Endpoint(Endpoint {
            sid: 3,
            role: "A".to_string(),
        }),
    ];

    for value in values {
        let encoded = serde_json::to_string(&value).expect("serialize value");
        let decoded: Value = serde_json::from_str(&encoded).expect("deserialize value");
        assert_eq!(decoded, value, "roundtrip mismatch for {encoded}");
    }
}

#[wasm_bindgen_test(unsupported = test)]
fn lean_immediate_variants_roundtrip() {
    let values = vec![
        ImmValue::Unit,
        ImmValue::Nat(11),
        ImmValue::Bool(false),
        ImmValue::Str("payload".to_string()),
    ];

    for value in values {
        let encoded = serde_json::to_string(&value).expect("serialize immediate");
        let decoded: ImmValue = serde_json::from_str(&encoded).expect("deserialize immediate");
        assert_eq!(decoded, value, "roundtrip mismatch for {encoded}");
    }
}

#[wasm_bindgen_test(unsupported = test)]
fn value_schema_tag_set_is_strictly_lean() {
    let samples = vec![
        Value::Unit,
        Value::Nat(0),
        Value::Bool(false),
        Value::Str("s".to_string()),
        Value::Prod(Box::new(Value::Nat(1)), Box::new(Value::Bool(true))),
        Value::Endpoint(Endpoint {
            sid: 0,
            role: "R".to_string(),
        }),
    ];

    let mut tags = BTreeSet::new();
    for sample in samples {
        let encoded = serde_json::to_value(sample).expect("serialize");
        let tag = if let Some(s) = encoded.as_str() {
            s.to_string()
        } else {
            let obj = encoded.as_object().expect("externally-tagged enum object");
            assert_eq!(obj.len(), 1, "expected exactly one enum tag");
            obj.keys().next().expect("tag key").clone()
        };
        tags.insert(tag);
    }
    let expected: BTreeSet<String> = ["Unit", "Nat", "Bool", "Str", "Prod", "Endpoint"]
        .into_iter()
        .map(std::string::ToString::to_string)
        .collect();
    assert_eq!(tags, expected);
}

#[wasm_bindgen_test(unsupported = test)]
fn legacy_value_schema_tags_are_rejected() {
    for json in [
        r#"{"Int":1}"#,
        r#"{"Real":"0.1"}"#,
        r#"{"Vec":[1,2]}"#,
        r#"{"Json":{"x":1}}"#,
        r#"{"Label":"m"}"#,
        r#"{"Knowledge":{"endpoint":{"sid":0,"role":"A"},"fact":"f"}}"#,
    ] {
        let decoded = serde_json::from_str::<Value>(json);
        assert!(
            decoded.is_err(),
            "legacy schema tag should fail for Value: {json}"
        );
    }
}
