//! Import Lean JSON into Rust types.
//!
//! This module provides functions to parse JSON (from Lean output)
//! back into GlobalType and LocalTypeR.

use serde_json::Value;
use telltale_types::{GlobalType, Label, LocalTypeR, PayloadSort, ValType};
use thiserror::Error;

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
}

fn required_field<'a>(json: &'a Value, field: &str) -> Result<&'a Value, ImportError> {
    json.get(field)
        .ok_or_else(|| ImportError::MissingField(field.to_string()))
}

fn required_str(json: &Value, field: &str) -> Result<String, ImportError> {
    required_field(json, field)?
        .as_str()
        .map(ToString::to_string)
        .ok_or_else(|| ImportError::MissingField(field.to_string()))
}

fn required_array<'a>(json: &'a Value, field: &str) -> Result<&'a [Value], ImportError> {
    required_field(json, field)?
        .as_array()
        .map(Vec::as_slice)
        .ok_or_else(|| ImportError::MissingField(field.to_string()))
}

fn parse_global_comm(json: &Value) -> Result<GlobalType, ImportError> {
    let sender = required_str(json, "sender")?;
    let receiver = required_str(json, "receiver")?;
    let branches = parse_global_branches(required_array(json, "branches")?)?;
    Ok(GlobalType::Comm {
        sender,
        receiver,
        branches,
    })
}

fn parse_global_branches(branches: &[Value]) -> Result<Vec<(Label, GlobalType)>, ImportError> {
    let mut parsed = Vec::with_capacity(branches.len());
    for branch in branches {
        let label = parse_label(
            branch
                .get("label")
                .ok_or_else(|| ImportError::MissingField("label in branch".to_string()))?,
        )?;
        let cont = json_to_global(
            branch
                .get("continuation")
                .ok_or_else(|| ImportError::MissingField("continuation in branch".to_string()))?,
        )?;
        parsed.push((label, cont));
    }
    Ok(parsed)
}

fn parse_global_rec(json: &Value) -> Result<GlobalType, ImportError> {
    let var = required_str(json, "var")?;
    let body = json_to_global(required_field(json, "body")?)?;
    Ok(GlobalType::mu(var, body))
}

fn parse_global_var(json: &Value) -> Result<GlobalType, ImportError> {
    Ok(GlobalType::var(required_str(json, "name")?))
}

/// Parse JSON into a GlobalType.
///
/// # Example
///
/// ```
/// use telltale_lean_bridge::import::json_to_global;
/// use serde_json::json;
///
/// let json = json!({ "kind": "end" });
/// let g = json_to_global(&json).unwrap();
/// assert!(matches!(g, telltale_types::GlobalType::End));
/// ```
pub fn json_to_global(json: &Value) -> Result<GlobalType, ImportError> {
    let kind = json
        .get("kind")
        .and_then(|v| v.as_str())
        .ok_or_else(|| ImportError::MissingField("kind".to_string()))?;

    match kind {
        "end" => Ok(GlobalType::End),
        "comm" => parse_global_comm(json),
        "rec" => parse_global_rec(json),
        "var" => parse_global_var(json),
        other => Err(ImportError::InvalidKind(other.to_string())),
    }
}

fn parse_local_branches(
    branches: &[Value],
) -> Result<Vec<(Label, Option<ValType>, LocalTypeR)>, ImportError> {
    let mut parsed = Vec::with_capacity(branches.len());
    for branch in branches {
        let label = parse_label(
            branch
                .get("label")
                .ok_or_else(|| ImportError::MissingField("label in branch".to_string()))?,
        )?;
        let cont = json_to_local(
            branch
                .get("continuation")
                .ok_or_else(|| ImportError::MissingField("continuation in branch".to_string()))?,
        )?;
        parsed.push((label, None, cont));
    }
    Ok(parsed)
}

fn parse_local_send(json: &Value) -> Result<LocalTypeR, ImportError> {
    let partner = required_str(json, "partner")?;
    let branches = parse_local_branches(required_array(json, "branches")?)?;
    Ok(LocalTypeR::Send { partner, branches })
}

fn parse_local_recv(json: &Value) -> Result<LocalTypeR, ImportError> {
    let partner = required_str(json, "partner")?;
    let branches = parse_local_branches(required_array(json, "branches")?)?;
    Ok(LocalTypeR::Recv { partner, branches })
}

fn parse_local_rec(json: &Value) -> Result<LocalTypeR, ImportError> {
    let var = required_str(json, "var")?;
    let body = json_to_local(required_field(json, "body")?)?;
    Ok(LocalTypeR::mu(var, body))
}

fn parse_local_var(json: &Value) -> Result<LocalTypeR, ImportError> {
    Ok(LocalTypeR::var(required_str(json, "name")?))
}

/// Parse JSON into a LocalTypeR.
///
/// # Example
///
/// ```
/// use telltale_lean_bridge::import::json_to_local;
/// use serde_json::json;
///
/// let json = json!({ "kind": "end" });
/// let lt = json_to_local(&json).unwrap();
/// assert!(matches!(lt, telltale_types::LocalTypeR::End));
/// ```
pub fn json_to_local(json: &Value) -> Result<LocalTypeR, ImportError> {
    let kind = json
        .get("kind")
        .and_then(|v| v.as_str())
        .ok_or_else(|| ImportError::MissingField("kind".to_string()))?;

    match kind {
        "end" => Ok(LocalTypeR::End),
        "send" => parse_local_send(json),
        "recv" => parse_local_recv(json),
        "rec" => parse_local_rec(json),
        "var" => parse_local_var(json),
        other => Err(ImportError::InvalidKind(other.to_string())),
    }
}

/// Parse a Label from JSON.
fn parse_label(json: &Value) -> Result<Label, ImportError> {
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
            Ok(PayloadSort::Vector(n as usize))
        } else {
            Err(ImportError::InvalidSort(format!("{:?}", obj)))
        }
    } else {
        Err(ImportError::InvalidSort(format!("{}", json)))
    }
}

/// Parse a GlobalType from a JSON string.
pub fn parse_global_from_str(s: &str) -> Result<GlobalType, ImportError> {
    let json: Value = serde_json::from_str(s)
        .map_err(|_| ImportError::ExpectedObject("invalid JSON".to_string()))?;
    json_to_global(&json)
}

/// Parse a LocalTypeR from a JSON string.
pub fn parse_local_from_str(s: &str) -> Result<LocalTypeR, ImportError> {
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
}
