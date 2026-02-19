//! Shared transfer/delegation semantics used by cooperative and threaded VMs.

use crate::coroutine::{Coroutine, Fault, Value};
use crate::faults::{
    transfer_fault_endpoint_not_owned, transfer_fault_expect_endpoint_register,
    transfer_fault_expect_nat_target, transfer_fault_target_id_out_of_range,
};
use crate::instr::Endpoint;

/// Decoded transfer request from one instruction instance.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TransferRequest {
    /// Endpoint to be transferred.
    pub endpoint: Endpoint,
    /// Destination coroutine id.
    pub target_id: usize,
}

/// Decode transfer endpoint/target operands and enforce source ownership.
pub fn decode_transfer_request(
    coro: &Coroutine,
    role: &str,
    endpoint_reg: u16,
    target_reg: u16,
) -> Result<TransferRequest, Fault> {
    let endpoint_val = coro
        .regs
        .get(usize::from(endpoint_reg))
        .ok_or(Fault::OutOfRegisters)?
        .clone();
    let endpoint = match endpoint_val {
        Value::Endpoint(endpoint) => endpoint,
        _ => return Err(transfer_fault_expect_endpoint_register(role)),
    };

    let target_val = coro
        .regs
        .get(usize::from(target_reg))
        .ok_or(Fault::OutOfRegisters)?
        .clone();
    let target_id = match target_val {
        Value::Nat(v) => {
            usize::try_from(v).map_err(|_| transfer_fault_target_id_out_of_range(role))?
        }
        _ => return Err(transfer_fault_expect_nat_target(role)),
    };

    if !coro.owned_endpoints.contains(&endpoint) {
        return Err(transfer_fault_endpoint_not_owned());
    }

    Ok(TransferRequest {
        endpoint,
        target_id,
    })
}

/// Move endpoint ownership plus all endpoint-scoped progress/knowledge bundles.
///
/// If `target` is `None`, ownership is removed then restored on `source`.
pub fn move_endpoint_bundle(
    endpoint: &Endpoint,
    source: &mut Coroutine,
    target: Option<&mut Coroutine>,
) -> Result<(), Fault> {
    if !source.owned_endpoints.contains(endpoint) {
        return Err(transfer_fault_endpoint_not_owned());
    }

    let mut moved_tokens = Vec::new();
    source.progress_tokens.retain(|token| {
        if token.endpoint == *endpoint {
            moved_tokens.push(token.clone());
            false
        } else {
            true
        }
    });
    let mut moved_knowledge = Vec::new();
    source.knowledge_set.retain(|fact| {
        if fact.endpoint == *endpoint {
            moved_knowledge.push(fact.clone());
            false
        } else {
            true
        }
    });
    source.owned_endpoints.retain(|e| e != endpoint);

    if let Some(target) = target {
        target.owned_endpoints.push(endpoint.clone());
        target.progress_tokens.extend(moved_tokens);
        target.knowledge_set.extend(moved_knowledge);
    } else {
        source.owned_endpoints.push(endpoint.clone());
        source.progress_tokens.extend(moved_tokens);
        source.knowledge_set.extend(moved_knowledge);
    }

    Ok(())
}

/// Snapshot endpoint owners by coroutine id.
#[must_use]
pub fn endpoint_owner_ids(coroutines: &[Coroutine], endpoint: &Endpoint) -> Vec<usize> {
    coroutines
        .iter()
        .filter_map(|coro| coro.owned_endpoints.contains(endpoint).then_some(coro.id))
        .collect()
}
