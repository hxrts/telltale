//! Shared instruction operand decoding helpers used by both VM executors.

use crate::coroutine::Fault;
use crate::coroutine::{Coroutine, Value};
use crate::instr::Endpoint;

fn val_type_of(value: &Value) -> telltale_types::ValType {
    use telltale_types::ValType;
    match value {
        Value::Unit => ValType::Unit,
        Value::Nat(_) => ValType::Nat,
        Value::Bool(_) => ValType::Bool,
        Value::Str(_) => ValType::String,
        Value::Prod(left, right) => {
            ValType::Prod(Box::new(val_type_of(left)), Box::new(val_type_of(right)))
        }
        Value::Endpoint(ep) => ValType::Chan {
            sid: ep.sid,
            role: ep.role.clone(),
        },
    }
}

/// Decode an endpoint operand register for channel/session instructions.
///
/// # Errors
///
/// Returns a `Fault::OutOfRegisters` if the register is out-of-bounds, or
/// `Fault::TypeViolation` if the register is not an endpoint value.
pub fn endpoint_from_reg(coro: &Coroutine, reg: u16) -> Result<Endpoint, Fault> {
    match coro.regs.get(usize::from(reg)).cloned() {
        Some(Value::Endpoint(ep)) => Ok(ep),
        Some(other) => Err(Fault::TypeViolation {
            expected: telltale_types::ValType::Chan {
                sid: 0,
                role: String::new(),
            },
            actual: val_type_of(&other),
            message: "expected endpoint register".to_string(),
        }),
        None => Err(Fault::OutOfRegisters),
    }
}

/// Decode a `(endpoint, string)` product used by epistemic tag/check ops.
#[must_use]
pub fn decode_endpoint_fact(value: Value) -> Option<(Endpoint, String)> {
    match value {
        Value::Prod(left, right) => match (*left, *right) {
            (Value::Endpoint(endpoint), Value::Str(fact)) => Some((endpoint, fact)),
            _ => None,
        },
        _ => None,
    }
}
