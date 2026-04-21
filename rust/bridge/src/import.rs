//! Import Lean JSON into Rust types.
//!
//! This module provides functions to parse JSON (from Lean output)
//! back into GlobalType and LocalTypeR.

use serde_json::Value;
use telltale_types::{GlobalType, Label, LocalTypeR, PayloadSort, ValType};
use thiserror::Error;

pub const MAX_BRIDGE_JSON_BYTES: usize = 8 * 1024 * 1024;
pub const MAX_BRIDGE_JSON_DEPTH: usize = 256;

/// Errors that can occur during JSON import.
#[derive(Debug, Error)]
pub enum ImportError {
    #[error("Missing field: {0}")]
    MissingField(String),

    #[error("Invalid kind: {0}")]
    InvalidKind(String),

    #[error("Invalid sort: {0}")]
    InvalidSort(String),

    #[error("Expected string, got: {0}")]
    ExpectedString(String),

    #[error("Expected array, got: {0}")]
    ExpectedArray(String),

    #[error("Expected object, got: {0}")]
    ExpectedObject(String),

    #[error("Unexpected field '{field}' in {context}")]
    UnexpectedField { context: String, field: String },

    #[error("Input too large: {0}")]
    InputTooLarge(String),

    #[error("Input too deep: {0}")]
    InputTooDeep(String),
}

fn check_depth(depth: usize) -> Result<(), ImportError> {
    if depth > MAX_BRIDGE_JSON_DEPTH {
        return Err(ImportError::InputTooDeep(format!(
            "JSON type depth exceeds {MAX_BRIDGE_JSON_DEPTH}"
        )));
    }
    Ok(())
}

fn ensure_only_fields(json: &Value, context: &str, allowed: &[&str]) -> Result<(), ImportError> {
    let object = json
        .as_object()
        .ok_or_else(|| ImportError::ExpectedObject(json.to_string()))?;
    for field in object.keys() {
        if !allowed.iter().any(|allowed_field| allowed_field == field) {
            return Err(ImportError::UnexpectedField {
                context: context.to_string(),
                field: field.clone(),
            });
        }
    }
    Ok(())
}

fn required_field<'a>(json: &'a Value, field: &str) -> Result<&'a Value, ImportError> {
    json.get(field)
        .ok_or_else(|| ImportError::MissingField(field.to_string()))
}

fn required_str(json: &Value, field: &str) -> Result<String, ImportError> {
    let value = required_field(json, field)?;
    value
        .as_str()
        .map(ToString::to_string)
        .ok_or_else(|| ImportError::ExpectedString(value.to_string()))
}

fn required_array<'a>(json: &'a Value, field: &str) -> Result<&'a [Value], ImportError> {
    let value = required_field(json, field)?;
    value
        .as_array()
        .map(Vec::as_slice)
        .ok_or_else(|| ImportError::ExpectedArray(value.to_string()))
}

fn parse_global_comm(json: &Value, depth: usize) -> Result<GlobalType, ImportError> {
    ensure_only_fields(
        json,
        "global comm",
        &["kind", "sender", "receiver", "branches"],
    )?;
    let sender = required_str(json, "sender")?;
    let receiver = required_str(json, "receiver")?;
    let branches = parse_global_branches(required_array(json, "branches")?, depth + 1)?;
    Ok(GlobalType::Comm {
        sender,
        receiver,
        branches,
    })
}

fn parse_global_branches(
    branches: &[Value],
    depth: usize,
) -> Result<Vec<(Label, GlobalType)>, ImportError> {
    check_depth(depth)?;
    let mut parsed = Vec::with_capacity(branches.len());
    for branch in branches {
        ensure_only_fields(branch, "global branch", &["label", "continuation"])?;
        let label = parse_label(
            branch
                .get("label")
                .ok_or_else(|| ImportError::MissingField("label in branch".to_string()))?,
        )?;
        let cont = json_to_global_with_depth(
            branch
                .get("continuation")
                .ok_or_else(|| ImportError::MissingField("continuation in branch".to_string()))?,
            depth + 1,
        )?;
        parsed.push((label, cont));
    }
    Ok(parsed)
}

fn parse_global_rec(json: &Value, depth: usize) -> Result<GlobalType, ImportError> {
    ensure_only_fields(json, "global rec", &["kind", "var", "body"])?;
    let var = required_str(json, "var")?;
    let body = json_to_global_with_depth(required_field(json, "body")?, depth + 1)?;
    Ok(GlobalType::mu(var, body))
}

fn parse_global_var(json: &Value) -> Result<GlobalType, ImportError> {
    ensure_only_fields(json, "global var", &["kind", "name"])?;
    Ok(GlobalType::var(required_str(json, "name")?))
}

/// Parse JSON into a GlobalType.
///
/// # Example
///
/// ```
/// use telltale_bridge::import::json_to_global;
/// use serde_json::json;
///
/// let json = json!({ "kind": "end" });
/// let g = json_to_global(&json).unwrap();
/// assert!(matches!(g, telltale_types::GlobalType::End));
/// ```
pub fn json_to_global(json: &Value) -> Result<GlobalType, ImportError> {
    json_to_global_with_depth(json, 0)
}

fn json_to_global_with_depth(json: &Value, depth: usize) -> Result<GlobalType, ImportError> {
    check_depth(depth)?;
    let kind = json
        .get("kind")
        .and_then(|v| v.as_str())
        .ok_or_else(|| ImportError::MissingField("kind".to_string()))?;

    match kind {
        "end" => {
            ensure_only_fields(json, "global end", &["kind"])?;
            Ok(GlobalType::End)
        }
        "comm" => parse_global_comm(json, depth + 1),
        "rec" => parse_global_rec(json, depth + 1),
        "var" => parse_global_var(json),
        other => Err(ImportError::InvalidKind(other.to_string())),
    }
}

fn parse_local_branches(
    branches: &[Value],
    depth: usize,
) -> Result<Vec<(Label, Option<ValType>, LocalTypeR)>, ImportError> {
    check_depth(depth)?;
    let mut parsed = Vec::with_capacity(branches.len());
    for branch in branches {
        ensure_only_fields(branch, "local branch", &["label", "continuation"])?;
        let label = parse_label(
            branch
                .get("label")
                .ok_or_else(|| ImportError::MissingField("label in branch".to_string()))?,
        )?;
        let cont = json_to_local_with_depth(
            branch
                .get("continuation")
                .ok_or_else(|| ImportError::MissingField("continuation in branch".to_string()))?,
            depth + 1,
        )?;
        parsed.push((label, None, cont));
    }
    Ok(parsed)
}

fn parse_local_send(json: &Value, depth: usize) -> Result<LocalTypeR, ImportError> {
    ensure_only_fields(json, "local send", &["kind", "partner", "branches"])?;
    let partner = required_str(json, "partner")?;
    let branches = parse_local_branches(required_array(json, "branches")?, depth + 1)?;
    Ok(LocalTypeR::Send { partner, branches })
}

fn parse_local_recv(json: &Value, depth: usize) -> Result<LocalTypeR, ImportError> {
    ensure_only_fields(json, "local recv", &["kind", "partner", "branches"])?;
    let partner = required_str(json, "partner")?;
    let branches = parse_local_branches(required_array(json, "branches")?, depth + 1)?;
    Ok(LocalTypeR::Recv { partner, branches })
}

fn parse_local_rec(json: &Value, depth: usize) -> Result<LocalTypeR, ImportError> {
    ensure_only_fields(json, "local rec", &["kind", "var", "body"])?;
    let var = required_str(json, "var")?;
    let body = json_to_local_with_depth(required_field(json, "body")?, depth + 1)?;
    Ok(LocalTypeR::mu(var, body))
}

fn parse_local_var(json: &Value) -> Result<LocalTypeR, ImportError> {
    ensure_only_fields(json, "local var", &["kind", "name"])?;
    Ok(LocalTypeR::var(required_str(json, "name")?))
}

/// Parse JSON into a LocalTypeR.
///
/// # Example
///
/// ```
/// use telltale_bridge::import::json_to_local;
/// use serde_json::json;
///
/// let json = json!({ "kind": "end" });
/// let lt = json_to_local(&json).unwrap();
/// assert!(matches!(lt, telltale_types::LocalTypeR::End));
/// ```
pub fn json_to_local(json: &Value) -> Result<LocalTypeR, ImportError> {
    json_to_local_with_depth(json, 0)
}

fn json_to_local_with_depth(json: &Value, depth: usize) -> Result<LocalTypeR, ImportError> {
    check_depth(depth)?;
    let kind = json
        .get("kind")
        .and_then(|v| v.as_str())
        .ok_or_else(|| ImportError::MissingField("kind".to_string()))?;

    match kind {
        "end" => {
            ensure_only_fields(json, "local end", &["kind"])?;
            Ok(LocalTypeR::End)
        }
        "send" => parse_local_send(json, depth + 1),
        "recv" => parse_local_recv(json, depth + 1),
        "rec" => parse_local_rec(json, depth + 1),
        "var" => parse_local_var(json),
        other => Err(ImportError::InvalidKind(other.to_string())),
    }
}

/// Parse a Label from JSON.
fn parse_label(json: &Value) -> Result<Label, ImportError> {
    ensure_only_fields(json, "label", &["name", "sort"])?;
    let name = json
        .get("name")
        .and_then(|v| v.as_str())
        .ok_or_else(|| ImportError::MissingField("name in label".to_string()))?
        .to_string();

    let sort = json
        .get("sort")
        .map(parse_sort)
        .transpose()?
        .unwrap_or(PayloadSort::Unit);

    Ok(Label { name, sort })
}

/// Parse a PayloadSort from JSON.
fn parse_sort(json: &Value) -> Result<PayloadSort, ImportError> {
    if let Some(s) = json.as_str() {
        match s {
            "unit" => Ok(PayloadSort::Unit),
            "nat" => Ok(PayloadSort::Nat),
            "bool" => Ok(PayloadSort::Bool),
            "string" => Ok(PayloadSort::String),
            "real" => Ok(PayloadSort::Real),
            other => Err(ImportError::InvalidSort(other.to_string())),
        }
    } else if let Some(obj) = json.as_object() {
        if obj.len() != 1 {
            let unexpected = obj.keys().cloned().collect::<Vec<_>>().join(", ");
            return Err(ImportError::UnexpectedField {
                context: "sort".to_string(),
                field: unexpected,
            });
        }
        if let Some(arr) = obj.get("prod").and_then(|v| v.as_array()) {
            if arr.len() == 2 {
                let left = parse_sort(&arr[0])?;
                let right = parse_sort(&arr[1])?;
                Ok(PayloadSort::Prod(Box::new(left), Box::new(right)))
            } else {
                Err(ImportError::InvalidSort(
                    "prod must have 2 elements".to_string(),
                ))
            }
        } else if let Some(n) = obj.get("vector").and_then(|v| v.as_u64()) {
            let size = usize::try_from(n)
                .map_err(|_| ImportError::InvalidSort("vector size exceeds usize".to_string()))?;
            Ok(PayloadSort::Vector(size))
        } else {
            Err(ImportError::InvalidSort(format!("{:?}", obj)))
        }
    } else {
        Err(ImportError::InvalidSort(format!("{}", json)))
    }
}

/// Parse a GlobalType from a JSON string.
pub fn parse_global_from_str(s: &str) -> Result<GlobalType, ImportError> {
    if s.len() > MAX_BRIDGE_JSON_BYTES {
        return Err(ImportError::InputTooLarge(format!(
            "bridge JSON input is {} bytes, max is {MAX_BRIDGE_JSON_BYTES}",
            s.len()
        )));
    }
    let json: Value = serde_json::from_str(s)
        .map_err(|_| ImportError::ExpectedObject("invalid JSON".to_string()))?;
    json_to_global(&json)
}

/// Parse a LocalTypeR from a JSON string.
pub fn parse_local_from_str(s: &str) -> Result<LocalTypeR, ImportError> {
    if s.len() > MAX_BRIDGE_JSON_BYTES {
        return Err(ImportError::InputTooLarge(format!(
            "bridge JSON input is {} bytes, max is {MAX_BRIDGE_JSON_BYTES}",
            s.len()
        )));
    }
    let json: Value = serde_json::from_str(s)
        .map_err(|_| ImportError::ExpectedObject("invalid JSON".to_string()))?;
    json_to_local(&json)
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn test_parse_global_end() {
        let json = json!({ "kind": "end" });
        let g = json_to_global(&json).unwrap();
        assert!(matches!(g, GlobalType::End));
    }

    #[test]
    fn test_parse_global_comm() {
        let json = json!({
            "kind": "comm",
            "sender": "A",
            "receiver": "B",
            "branches": [{
                "label": { "name": "msg", "sort": "unit" },
                "continuation": { "kind": "end" }
            }]
        });
        let g = json_to_global(&json).unwrap();

        match g {
            GlobalType::Comm {
                sender,
                receiver,
                branches,
            } => {
                assert_eq!(sender, "A");
                assert_eq!(receiver, "B");
                assert_eq!(branches.len(), 1);
            }
            _ => panic!("Expected Comm"),
        }
    }

    #[test]
    fn test_parse_global_rejects_unknown_field() {
        let json = json!({
            "kind": "end",
            "extra": true
        });
        let err = json_to_global(&json).expect_err("unknown fields must fail closed");
        assert!(matches!(
            err,
            ImportError::UnexpectedField { context, field }
            if context == "global end" && field == "extra"
        ));
    }

    #[test]
    fn test_parse_global_rec() {
        let json = json!({
            "kind": "rec",
            "var": "X",
            "body": {
                "kind": "var",
                "name": "X"
            }
        });
        let g = json_to_global(&json).unwrap();

        match g {
            GlobalType::Mu { var, .. } => assert_eq!(var, "X"),
            _ => panic!("Expected Mu"),
        }
    }

    #[test]
    fn test_parse_local_end() {
        let json = json!({ "kind": "end" });
        let lt = json_to_local(&json).unwrap();
        assert!(matches!(lt, LocalTypeR::End));
    }

    #[test]
    fn test_parse_local_send() {
        let json = json!({
            "kind": "send",
            "partner": "B",
            "branches": [{
                "label": { "name": "hello", "sort": "string" },
                "continuation": { "kind": "end" }
            }]
        });
        let lt = json_to_local(&json).unwrap();

        match lt {
            LocalTypeR::Send { partner, branches } => {
                assert_eq!(partner, "B");
                assert_eq!(branches.len(), 1);
                assert_eq!(branches[0].0.sort, PayloadSort::String);
            }
            _ => panic!("Expected Send"),
        }
    }

    #[test]
    fn test_parse_local_rejects_unknown_field() {
        let json = json!({
            "kind": "send",
            "partner": "B",
            "branches": [],
            "extra": true
        });
        let err = json_to_local(&json).expect_err("unknown fields must fail closed");
        assert!(matches!(
            err,
            ImportError::UnexpectedField { context, field }
            if context == "local send" && field == "extra"
        ));
    }

    #[test]
    fn test_parse_label_rejects_unknown_field() {
        let json = json!({
            "kind": "comm",
            "sender": "A",
            "receiver": "B",
            "branches": [{
                "label": { "name": "msg", "sort": "unit", "extra": true },
                "continuation": { "kind": "end" }
            }]
        });
        let err = json_to_global(&json).expect_err("unknown label fields must fail closed");
        assert!(matches!(
            err,
            ImportError::UnexpectedField { context, field }
            if context == "label" && field == "extra"
        ));
    }

    #[test]
    fn test_parse_prod_sort() {
        let json = json!({
            "kind": "send",
            "partner": "B",
            "branches": [{
                "label": {
                    "name": "pair",
                    "sort": { "prod": ["nat", "bool"] }
                },
                "continuation": { "kind": "end" }
            }]
        });
        let lt = json_to_local(&json).unwrap();

        match lt {
            LocalTypeR::Send { branches, .. } => {
                let sort = &branches[0].0.sort;
                assert!(matches!(sort, PayloadSort::Prod(..)));
            }
            _ => panic!("Expected Send"),
        }
    }

    #[test]
    fn test_parse_real_sort() {
        let json = json!({
            "kind": "send",
            "partner": "B",
            "branches": [{
                "label": { "name": "value", "sort": "real" },
                "continuation": { "kind": "end" }
            }]
        });
        let lt = json_to_local(&json).unwrap();
        match lt {
            LocalTypeR::Send { branches, .. } => {
                assert_eq!(branches[0].0.sort, PayloadSort::Real);
            }
            _ => panic!("Expected Send"),
        }
    }

    #[test]
    fn test_parse_vector_sort() {
        let json = json!({
            "kind": "send",
            "partner": "B",
            "branches": [{
                "label": { "name": "config", "sort": { "vector": 4 } },
                "continuation": { "kind": "end" }
            }]
        });
        let lt = json_to_local(&json).unwrap();
        match lt {
            LocalTypeR::Send { branches, .. } => {
                assert_eq!(branches[0].0.sort, PayloadSort::Vector(4));
            }
            _ => panic!("Expected Send"),
        }
    }

    #[test]
    fn test_roundtrip() {
        use crate::export::global_to_json;

        let original = GlobalType::comm(
            "Client",
            "Server",
            vec![
                (Label::new("request"), GlobalType::End),
                (Label::with_sort("data", PayloadSort::Nat), GlobalType::End),
            ],
        );

        let json = global_to_json(&original);
        let parsed = json_to_global(&json).unwrap();

        // Compare structure
        match (&original, &parsed) {
            (
                GlobalType::Comm {
                    sender: s1,
                    receiver: r1,
                    branches: b1,
                },
                GlobalType::Comm {
                    sender: s2,
                    receiver: r2,
                    branches: b2,
                },
            ) => {
                assert_eq!(s1, s2);
                assert_eq!(r1, r2);
                assert_eq!(b1.len(), b2.len());
            }
            _ => panic!("Structure mismatch"),
        }
    }

    #[test]
    fn test_parse_global_reports_expected_string_for_sender() {
        let json = json!({
            "kind": "comm",
            "sender": 1,
            "receiver": "B",
            "branches": []
        });

        let err = json_to_global(&json).expect_err("sender should require string");
        assert!(matches!(err, ImportError::ExpectedString(_)));
    }

    #[test]
    fn test_parse_global_reports_expected_array_for_branches() {
        let json = json!({
            "kind": "comm",
            "sender": "A",
            "receiver": "B",
            "branches": { "bad": true }
        });

        let err = json_to_global(&json).expect_err("branches should require array");
        assert!(matches!(err, ImportError::ExpectedArray(_)));
    }

    #[test]
    fn test_parse_global_rejects_excessive_depth() {
        let mut json = json!({ "kind": "end" });
        for _ in 0..(MAX_BRIDGE_JSON_DEPTH + 1) {
            json = json!({
                "kind": "rec",
                "var": "x",
                "body": json
            });
        }

        let err = json_to_global(&json).expect_err("deep import should fail closed");
        assert!(matches!(err, ImportError::InputTooDeep(_)));
    }

    #[test]
    fn test_parse_global_from_str_rejects_oversized_input() {
        let input = " ".repeat(MAX_BRIDGE_JSON_BYTES + 1);
        let err = parse_global_from_str(&input).expect_err("oversized import should fail closed");
        assert!(matches!(err, ImportError::InputTooLarge(_)));
    }

    #[cfg(target_pointer_width = "32")]
    #[test]
    fn test_parse_vector_sort_rejects_overflow() {
        let json = json!({
            "kind": "send",
            "partner": "B",
            "branches": [{
                "label": { "name": "config", "sort": { "vector": 4294967296u64 } },
                "continuation": { "kind": "end" }
            }]
        });

        let err = json_to_local(&json).expect_err("vector size should overflow on 32-bit");
        assert!(matches!(err, ImportError::InvalidSort(_)));
    }
}
