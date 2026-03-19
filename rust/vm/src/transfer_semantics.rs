//! Shared transfer/delegation semantics used by cooperative and threaded VMs.

use std::collections::BTreeSet;

use crate::coroutine::{Coroutine, Fault, Value};
use crate::faults::{
    transfer_fault_endpoint_not_owned, transfer_fault_expect_endpoint_register,
    transfer_fault_expect_nat_target, transfer_fault_target_id_out_of_range,
};
use crate::instr::Endpoint;
use crate::session::{OwnershipScope, SessionId};

/// Decoded transfer request from one instruction instance.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TransferRequest {
    /// Endpoint to be transferred.
    pub endpoint: Endpoint,
    /// Destination coroutine id.
    pub target_id: usize,
}

/// Typed receipt for one delegation/transfer handoff.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct DelegationReceipt {
    /// Monotonic receipt id within one runtime.
    pub receipt_id: u64,
    /// Session carrying the delegated endpoint/fragment.
    pub session: SessionId,
    /// Endpoint being delegated.
    pub endpoint: Endpoint,
    /// Source coroutine id.
    pub from_coro: usize,
    /// Target coroutine id.
    pub to_coro: usize,
    /// Scope explicitly transferred by this delegation.
    pub scope: OwnershipScope,
}

/// Auditable outcome for one delegation attempt.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct DelegationAuditRecord {
    /// Scheduler tick at which the delegation was recorded.
    pub tick: u64,
    /// Typed transfer receipt.
    pub receipt: DelegationReceipt,
    /// Final transfer status.
    pub status: DelegationStatus,
    /// Optional failure detail when delegation did not commit.
    pub reason: Option<String>,
}

/// Final state of one delegation attempt.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum DelegationStatus {
    /// Delegation committed successfully.
    Committed,
    /// Delegation failed and was rolled back.
    RolledBack,
}

/// Decode transfer endpoint/target operands and enforce source ownership.
///
/// # Errors
///
/// Returns a `Fault` if registers are invalid, type mismatches occur, or
/// the source coroutine does not own the endpoint.
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

/// Build the explicit authority scope transferred for one endpoint handoff.
#[must_use]
pub fn delegation_scope_for_endpoint(endpoint: &Endpoint) -> OwnershipScope {
    OwnershipScope::Fragments(BTreeSet::from([endpoint.role.clone()]))
}

/// Build a typed receipt for one endpoint handoff.
#[must_use]
pub fn delegation_receipt(
    receipt_id: u64,
    endpoint: Endpoint,
    from_coro: usize,
    to_coro: usize,
) -> DelegationReceipt {
    DelegationReceipt {
        receipt_id,
        session: endpoint.sid,
        scope: delegation_scope_for_endpoint(&endpoint),
        endpoint,
        from_coro,
        to_coro,
    }
}

/// Validate the local coherence requirements for one delegation handoff.
///
/// This is the runtime analogue of requiring delegation to stay inside the
/// intended session/fragment boundary rather than mutating ownership ad hoc.
///
/// # Errors
///
/// Returns a `Fault` if source/target coroutine session binding disagrees with
/// the delegated endpoint session.
pub fn validate_delegation_coherence(
    source: &Coroutine,
    target: &Coroutine,
    endpoint: &Endpoint,
    role: &str,
) -> Result<(), Fault> {
    if source.session_id != endpoint.sid {
        return Err(Fault::Transfer {
            message: format!(
                "{role}: delegated endpoint {}:{} is not owned by source session {}",
                endpoint.sid, endpoint.role, source.session_id
            ),
        });
    }
    if target.session_id != endpoint.sid {
        return Err(Fault::Transfer {
            message: format!(
                "{role}: target coroutine session {} mismatches delegated endpoint session {}",
                target.session_id, endpoint.sid
            ),
        });
    }
    Ok(())
}

/// Move endpoint ownership plus all endpoint-scoped progress/knowledge bundles.
///
/// If `target` is `None`, ownership is removed then restored on `source`.
///
/// # Errors
///
/// Returns a `Fault` if the source coroutine does not own the endpoint.
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
