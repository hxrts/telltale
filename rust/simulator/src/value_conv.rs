//! Helpers for converting between VM values and numeric state vectors.

use telltale_types::FixedQ32;
use telltale_vm::coroutine::Value;

/// Extract numeric state values from a register file.
///
/// Non-numeric values are ignored.
pub(crate) fn values_to_f64s(values: &[Value]) -> Vec<FixedQ32> {
    values
        .iter()
        .filter_map(|v| match v {
            Value::Real(r) => Some(*r),
            Value::Int(i) => FixedQ32::try_from_i64(*i).ok(),
            _ => None,
        })
        .collect()
}

/// Extract numeric state values from a full register file.
///
/// Skips the first two reserved registers.
pub(crate) fn registers_to_f64s(values: &[Value]) -> Vec<FixedQ32> {
    let slice = values.get(2..).unwrap_or(&[]);
    values_to_f64s(slice)
}

/// Convert numeric state values into VM register values.
pub(crate) fn f64s_to_values(state: &[FixedQ32]) -> Vec<Value> {
    state.iter().copied().map(Value::Real).collect()
}

/// Overwrite the numeric portion of a register file with new state values.
///
/// Writes start at register index 2, matching the VM runner convention.
pub(crate) fn write_f64s(state: &mut Vec<Value>, values: &[FixedQ32]) {
    if state.len() < 2 {
        state.resize(2, Value::Unit);
    }
    for (i, &v) in values.iter().enumerate() {
        let idx = i + 2;
        if idx < state.len() {
            state[idx] = Value::Real(v);
        } else {
            state.push(Value::Real(v));
        }
    }
}

/// Convert a payload value to a scalar FixedQ32.
pub(crate) fn value_to_f64(value: &Value) -> Result<FixedQ32, String> {
    match value {
        Value::Real(r) => Ok(*r),
        Value::Int(i) => {
            FixedQ32::try_from_i64(*i).map_err(|e| format!("int conversion error: {e}"))
        }
        Value::Vec(v) => v
            .first()
            .copied()
            .ok_or_else(|| "empty vector payload".into()),
        Value::Json(v) => v
            .as_f64()
            .map(FixedQ32::from)
            .ok_or_else(|| "non-numeric json payload".into()),
        other => Err(format!("unsupported payload: {other:?}")),
    }
}
