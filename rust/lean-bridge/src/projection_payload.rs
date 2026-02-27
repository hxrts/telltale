use serde_json::Value;
use std::collections::HashMap;

pub(crate) fn parse_projections_field(payload: &Value) -> Result<HashMap<String, Value>, String> {
    let projections_val = payload
        .get("projections")
        .ok_or_else(|| "missing projections field".to_string())?;

    match projections_val {
        Value::Object(map) => Ok(map
            .iter()
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect::<HashMap<_, _>>()),
        Value::Array(items) => {
            let mut out = HashMap::new();
            for item in items {
                let obj = item
                    .as_object()
                    .ok_or_else(|| "invalid projection entry".to_string())?;
                let role = obj
                    .get("role")
                    .and_then(Value::as_str)
                    .ok_or_else(|| "missing role in projection".to_string())?;
                let local = obj
                    .get("local_type")
                    .or_else(|| obj.get("localType"))
                    .ok_or_else(|| "missing local_type in projection".to_string())?;
                out.insert(role.to_string(), local.clone());
            }
            Ok(out)
        }
        _ => Err("invalid projections format".to_string()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_projections_field_accepts_object_form() {
        let payload = serde_json::json!({
            "projections": {
                "A": {"kind": "end"},
                "B": {"kind": "end"}
            }
        });
        let parsed = parse_projections_field(&payload).expect("parse object projections");
        assert!(parsed.contains_key("A"));
        assert!(parsed.contains_key("B"));
    }

    #[test]
    fn parse_projections_field_accepts_array_form() {
        let payload = serde_json::json!({
            "projections": [
                {"role": "A", "local_type": {"kind": "end"}},
                {"role": "B", "localType": {"kind": "end"}}
            ]
        });
        let parsed = parse_projections_field(&payload).expect("parse array projections");
        assert!(parsed.contains_key("A"));
        assert!(parsed.contains_key("B"));
    }
}
