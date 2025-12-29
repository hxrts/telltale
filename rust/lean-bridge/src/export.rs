//! Export Rust types to Lean-compatible JSON.
//!
//! This module provides functions to convert GlobalType and LocalTypeR
//! into JSON format that matches the Lean type definitions.

use rumpsteak_types::{GlobalType, Label, LocalTypeR, PayloadSort};
use serde_json::{json, Value};

/// Convert a GlobalType to Lean-compatible JSON.
///
/// # JSON Format
///
/// The output matches the Lean `GlobalType` inductive type:
///
/// - `End` → `{"kind": "end"}`
/// - `Comm` → `{"kind": "comm", "sender": "...", "receiver": "...", "branches": [...]}`
/// - `Mu` → `{"kind": "rec", "var": "...", "body": {...}}`
/// - `Var` → `{"kind": "var", "name": "..."}`
///
/// # Example
///
/// ```
/// use rumpsteak_types::{GlobalType, Label};
/// use rumpsteak_lean_bridge::export::global_to_json;
///
/// let g = GlobalType::End;
/// let json = global_to_json(&g);
/// assert_eq!(json["kind"], "end");
/// ```
pub fn global_to_json(g: &GlobalType) -> Value {
    match g {
        GlobalType::End => json!({ "kind": "end" }),

        GlobalType::Comm {
            sender,
            receiver,
            branches,
        } => {
            let branches_json: Vec<Value> = branches
                .iter()
                .map(|(label, cont)| {
                    json!({
                        "label": label_to_json(label),
                        "continuation": global_to_json(cont)
                    })
                })
                .collect();

            json!({
                "kind": "comm",
                "sender": sender,
                "receiver": receiver,
                "branches": branches_json
            })
        }

        GlobalType::Mu { var, body } => {
            json!({
                "kind": "rec",
                "var": var,
                "body": global_to_json(body)
            })
        }

        GlobalType::Var(name) => {
            json!({
                "kind": "var",
                "name": name
            })
        }
    }
}

/// Convert a LocalTypeR to Lean-compatible JSON.
///
/// # JSON Format
///
/// The output matches the Lean `LocalTypeR` inductive type:
///
/// - `End` → `{"kind": "end"}`
/// - `Send` → `{"kind": "send", "partner": "...", "branches": [...]}`
/// - `Recv` → `{"kind": "recv", "partner": "...", "branches": [...]}`
/// - `Mu` → `{"kind": "rec", "var": "...", "body": {...}}`
/// - `Var` → `{"kind": "var", "name": "..."}`
///
/// # Example
///
/// ```
/// use rumpsteak_types::{LocalTypeR, Label};
/// use rumpsteak_lean_bridge::export::local_to_json;
///
/// let lt = LocalTypeR::End;
/// let json = local_to_json(&lt);
/// assert_eq!(json["kind"], "end");
/// ```
pub fn local_to_json(lt: &LocalTypeR) -> Value {
    match lt {
        LocalTypeR::End => json!({ "kind": "end" }),

        LocalTypeR::Send { partner, branches } => {
            let branches_json: Vec<Value> = branches
                .iter()
                .map(|(label, cont)| {
                    json!({
                        "label": label_to_json(label),
                        "continuation": local_to_json(cont)
                    })
                })
                .collect();

            json!({
                "kind": "send",
                "partner": partner,
                "branches": branches_json
            })
        }

        LocalTypeR::Recv { partner, branches } => {
            let branches_json: Vec<Value> = branches
                .iter()
                .map(|(label, cont)| {
                    json!({
                        "label": label_to_json(label),
                        "continuation": local_to_json(cont)
                    })
                })
                .collect();

            json!({
                "kind": "recv",
                "partner": partner,
                "branches": branches_json
            })
        }

        LocalTypeR::Mu { var, body } => {
            json!({
                "kind": "rec",
                "var": var,
                "body": local_to_json(body)
            })
        }

        LocalTypeR::Var(name) => {
            json!({
                "kind": "var",
                "name": name
            })
        }
    }
}

/// Convert a Label to JSON.
fn label_to_json(label: &Label) -> Value {
    json!({
        "name": label.name,
        "sort": sort_to_json(&label.sort)
    })
}

/// Convert a PayloadSort to JSON.
fn sort_to_json(sort: &PayloadSort) -> Value {
    match sort {
        PayloadSort::Unit => json!("unit"),
        PayloadSort::Nat => json!("nat"),
        PayloadSort::Bool => json!("bool"),
        PayloadSort::String => json!("string"),
        PayloadSort::Prod(left, right) => {
            json!({
                "prod": [sort_to_json(left), sort_to_json(right)]
            })
        }
    }
}

/// Convert a GlobalType to a pretty-printed JSON string.
pub fn global_to_json_string(g: &GlobalType) -> String {
    serde_json::to_string_pretty(&global_to_json(g)).unwrap_or_default()
}

/// Convert a LocalTypeR to a pretty-printed JSON string.
pub fn local_to_json_string(lt: &LocalTypeR) -> String {
    serde_json::to_string_pretty(&local_to_json(lt)).unwrap_or_default()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_global_end() {
        let json = global_to_json(&GlobalType::End);
        assert_eq!(json["kind"], "end");
    }

    #[test]
    fn test_global_comm() {
        let g = GlobalType::comm("A", "B", vec![(Label::new("msg"), GlobalType::End)]);
        let json = global_to_json(&g);

        assert_eq!(json["kind"], "comm");
        assert_eq!(json["sender"], "A");
        assert_eq!(json["receiver"], "B");
        assert!(json["branches"].is_array());
    }

    #[test]
    fn test_global_rec() {
        let g = GlobalType::mu(
            "X",
            GlobalType::comm("A", "B", vec![(Label::new("ping"), GlobalType::var("X"))]),
        );
        let json = global_to_json(&g);

        assert_eq!(json["kind"], "rec");
        assert_eq!(json["var"], "X");
        assert_eq!(json["body"]["kind"], "comm");
    }

    #[test]
    fn test_local_end() {
        let json = local_to_json(&LocalTypeR::End);
        assert_eq!(json["kind"], "end");
    }

    #[test]
    fn test_local_send() {
        let lt = LocalTypeR::send("B", Label::new("hello"), LocalTypeR::End);
        let json = local_to_json(&lt);

        assert_eq!(json["kind"], "send");
        assert_eq!(json["partner"], "B");
    }

    #[test]
    fn test_local_recv() {
        let lt = LocalTypeR::recv("A", Label::new("world"), LocalTypeR::End);
        let json = local_to_json(&lt);

        assert_eq!(json["kind"], "recv");
        assert_eq!(json["partner"], "A");
    }

    #[test]
    fn test_label_with_sort() {
        let label = Label::with_sort("count", PayloadSort::Nat);
        let json = label_to_json(&label);

        assert_eq!(json["name"], "count");
        assert_eq!(json["sort"], "nat");
    }

    #[test]
    fn test_prod_sort() {
        let sort = PayloadSort::Prod(Box::new(PayloadSort::Nat), Box::new(PayloadSort::Bool));
        let json = sort_to_json(&sort);

        assert!(json["prod"].is_array());
        assert_eq!(json["prod"][0], "nat");
        assert_eq!(json["prod"][1], "bool");
    }
}
