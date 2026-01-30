//! Import Lean JSON into Rust types.
//!
//! This module provides functions to parse JSON (from Lean output)
//! back into GlobalType and LocalTypeR.

use telltale_types::{GlobalType, Label, LocalTypeR, PayloadSort};
use serde_json::Value;
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

        "comm" => {
            let sender = json
                .get("sender")
                .and_then(|v| v.as_str())
                .ok_or_else(|| ImportError::MissingField("sender".to_string()))?
                .to_string();

            let receiver = json
                .get("receiver")
                .and_then(|v| v.as_str())
                .ok_or_else(|| ImportError::MissingField("receiver".to_string()))?
                .to_string();

            let branches_json = json
                .get("branches")
                .and_then(|v| v.as_array())
                .ok_or_else(|| ImportError::MissingField("branches".to_string()))?;

            let mut branches = Vec::new();
            for branch in branches_json {
                let label =
                    parse_label(branch.get("label").ok_or_else(|| {
                        ImportError::MissingField("label in branch".to_string())
                    })?)?;
                let cont = json_to_global(branch.get("continuation").ok_or_else(|| {
                    ImportError::MissingField("continuation in branch".to_string())
                })?)?;
                branches.push((label, cont));
            }

            Ok(GlobalType::Comm {
                sender,
                receiver,
                branches,
            })
        }

        "rec" => {
            let var = json
                .get("var")
                .and_then(|v| v.as_str())
                .ok_or_else(|| ImportError::MissingField("var".to_string()))?
                .to_string();

            let body = json_to_global(
                json.get("body")
                    .ok_or_else(|| ImportError::MissingField("body".to_string()))?,
            )?;

            Ok(GlobalType::mu(var, body))
        }

        "var" => {
            let name = json
                .get("name")
                .and_then(|v| v.as_str())
                .ok_or_else(|| ImportError::MissingField("name".to_string()))?
                .to_string();

            Ok(GlobalType::var(name))
        }

        other => Err(ImportError::InvalidKind(other.to_string())),
    }
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

        "send" => {
            let partner = json
                .get("partner")
                .and_then(|v| v.as_str())
                .ok_or_else(|| ImportError::MissingField("partner".to_string()))?
                .to_string();

            let branches_json = json
                .get("branches")
                .and_then(|v| v.as_array())
                .ok_or_else(|| ImportError::MissingField("branches".to_string()))?;

            let mut branches = Vec::new();
            for branch in branches_json {
                let label =
                    parse_label(branch.get("label").ok_or_else(|| {
                        ImportError::MissingField("label in branch".to_string())
                    })?)?;
                let cont = json_to_local(branch.get("continuation").ok_or_else(|| {
                    ImportError::MissingField("continuation in branch".to_string())
                })?)?;
                branches.push((label, cont));
            }

            Ok(LocalTypeR::Send { partner, branches })
        }

        "recv" => {
            let partner = json
                .get("partner")
                .and_then(|v| v.as_str())
                .ok_or_else(|| ImportError::MissingField("partner".to_string()))?
                .to_string();

            let branches_json = json
                .get("branches")
                .and_then(|v| v.as_array())
                .ok_or_else(|| ImportError::MissingField("branches".to_string()))?;

            let mut branches = Vec::new();
            for branch in branches_json {
                let label =
                    parse_label(branch.get("label").ok_or_else(|| {
                        ImportError::MissingField("label in branch".to_string())
                    })?)?;
                let cont = json_to_local(branch.get("continuation").ok_or_else(|| {
                    ImportError::MissingField("continuation in branch".to_string())
                })?)?;
                branches.push((label, cont));
            }

            Ok(LocalTypeR::Recv { partner, branches })
        }

        "rec" => {
            let var = json
                .get("var")
                .and_then(|v| v.as_str())
                .ok_or_else(|| ImportError::MissingField("var".to_string()))?
                .to_string();

            let body = json_to_local(
                json.get("body")
                    .ok_or_else(|| ImportError::MissingField("body".to_string()))?,
            )?;

            Ok(LocalTypeR::mu(var, body))
        }

        "var" => {
            let name = json
                .get("name")
                .and_then(|v| v.as_str())
                .ok_or_else(|| ImportError::MissingField("name".to_string()))?
                .to_string();

            Ok(LocalTypeR::var(name))
        }

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
