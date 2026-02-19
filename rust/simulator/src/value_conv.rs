//! Helpers for converting between VM values and numeric state vectors.

use telltale_types::FixedQ32;
use telltale_vm::coroutine::Value;

const Q32_SCALAR_PREFIX: &str = "q32:";
const Q32_VEC_PREFIX: &str = "q32vec:";

fn parse_q32_scalar_text(text: &str) -> Option<FixedQ32> {
    let bits_text = text.strip_prefix(Q32_SCALAR_PREFIX)?;
    let bits = bits_text.parse::<i64>().ok()?;
    Some(FixedQ32::from_bits(bits))
}

fn parse_q32_vec_text(text: &str) -> Option<Vec<FixedQ32>> {
    let payload = text.strip_prefix(Q32_VEC_PREFIX)?;
    if payload.is_empty() {
        return Some(Vec::new());
    }
    payload
        .split(',')
        .map(|bits_text| bits_text.parse::<i64>().ok().map(FixedQ32::from_bits))
        .collect()
}

/// Encode one fixed-point value into the current VM value surface.
pub(crate) fn fixed_to_value(value: FixedQ32) -> Value {
    Value::Str(format!("{Q32_SCALAR_PREFIX}{}", value.to_bits()))
}

/// Encode a fixed-point vector into the current VM value surface.
pub(crate) fn fixed_vec_to_value(values: &[FixedQ32]) -> Value {
    let joined = values
        .iter()
        .map(|value| value.to_bits().to_string())
        .collect::<Vec<_>>()
        .join(",");
    Value::Str(format!("{Q32_VEC_PREFIX}{joined}"))
}

/// Decode one fixed-point value from a VM value when possible.
pub(crate) fn try_decode_fixed(value: &Value) -> Option<FixedQ32> {
    match value {
        Value::Str(text) => parse_q32_scalar_text(text),
        _ => None,
    }
}

/// Decode a fixed-point vector from a VM value when possible.
pub(crate) fn try_decode_fixed_vec(value: &Value) -> Option<Vec<FixedQ32>> {
    match value {
        Value::Str(text) => parse_q32_vec_text(text),
        _ => None,
    }
}

/// Extract numeric state values from a register file.
///
/// Non-numeric values are ignored.
pub(crate) fn values_to_f64s(values: &[Value]) -> Vec<FixedQ32> {
    values
        .iter()
        .filter_map(|v| match v {
            Value::Str(text) => parse_q32_scalar_text(text),
            Value::Nat(n) => i64::try_from(*n)
                .ok()
                .and_then(|i| FixedQ32::try_from_i64(i).ok()),
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
    state.iter().copied().map(fixed_to_value).collect()
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
            state[idx] = fixed_to_value(v);
        } else {
            state.push(fixed_to_value(v));
        }
    }
}

/// Convert a payload value to a scalar FixedQ32.
pub(crate) fn value_to_f64(value: &Value) -> Result<FixedQ32, String> {
    match value {
        Value::Str(text) if text.starts_with(Q32_SCALAR_PREFIX) => {
            parse_q32_scalar_text(text).ok_or_else(|| format!("invalid q32 scalar payload: {text}"))
        }
        Value::Str(text) if text.starts_with(Q32_VEC_PREFIX) => parse_q32_vec_text(text)
            .and_then(|v| v.first().copied())
            .ok_or_else(|| "empty vector payload".into()),
        Value::Nat(n) => i64::try_from(*n)
            .map_err(|e| format!("nat overflow: {e}"))
            .and_then(|i| {
                FixedQ32::try_from_i64(i).map_err(|e| format!("nat conversion error: {e}"))
            }),
        other => Err(format!("unsupported payload: {other:?}")),
    }
}
