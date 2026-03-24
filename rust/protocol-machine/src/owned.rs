//! Preferred owned-session helpers for host integration.
//!
//! These wrappers are the preferred public path for embedders that want to
//! respect the host-runtime ownership contract. Lower-level session accessors
//! remain available for tests and internal runtime wiring, but production host
//! mutation should flow through an owned capability.

use crate::loader::CodeImage;
use crate::session::{
    CancellationWitness, OwnershipCapability, OwnershipError, OwnershipReceipt, OwnershipScope,
    ReadinessWitness, SessionHostMutation, SessionId,
};
use crate::engine::{ProtocolMachineError, ProtocolMachine};

/// Capability-bearing handle returned by the preferred owned open path.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OwnedSession {
    session_id: SessionId,
    capability: OwnershipCapability,
}

impl OwnedSession {
    pub(crate) fn new(session_id: SessionId, capability: OwnershipCapability) -> Self {
        Self {
            session_id,
            capability,
        }
    }

    /// Session identifier for this owned handle.
    #[must_use]
    pub fn session_id(&self) -> SessionId {
        self.session_id
    }

    /// Live ownership capability carried by this handle.
    #[must_use]
    pub fn capability(&self) -> &OwnershipCapability {
        &self.capability
    }

    /// Apply one session-local host mutation through the ownership gate.
    ///
    /// # Errors
    ///
    /// Returns an `OwnershipError` if the capability is stale or lacks scope.
    pub fn apply_host_mutation(
        &self,
        vm: &mut ProtocolMachine,
        mutation: SessionHostMutation,
    ) -> Result<(), OwnershipError> {
        vm.sessions_mut()
            .apply_owned_session_mutation(&self.capability, mutation)
    }

    /// Issue a single-use readiness witness for a protocol-critical check.
    ///
    /// # Errors
    ///
    /// Returns an `OwnershipError` if the capability is stale or lacks session scope.
    pub fn issue_readiness_witness(
        &self,
        vm: &mut ProtocolMachine,
        predicate_ref: impl Into<String>,
    ) -> Result<ReadinessWitness, OwnershipError> {
        vm.sessions_mut()
            .issue_readiness_witness(&self.capability, predicate_ref)
    }

    /// Consume a previously issued readiness witness exactly once.
    ///
    /// # Errors
    ///
    /// Returns an `OwnershipError` if the witness is stale, forged, mismatched, or reused.
    pub fn consume_readiness_witness(
        &self,
        vm: &mut ProtocolMachine,
        witness: &ReadinessWitness,
    ) -> Result<(), OwnershipError> {
        vm.sessions_mut()
            .consume_readiness_witness(&self.capability, witness)
    }

    /// Begin an explicit ownership transfer from this handle.
    ///
    /// # Errors
    ///
    /// Returns an `OwnershipError` if the capability is stale.
    pub fn begin_transfer(
        &self,
        vm: &mut ProtocolMachine,
        new_owner_id: impl Into<String>,
        new_scope: OwnershipScope,
    ) -> Result<OwnershipReceipt, OwnershipError> {
        vm.sessions_mut()
            .begin_ownership_transfer(&self.capability, new_owner_id, new_scope)
    }

    /// Commit an explicit ownership transfer and return the refreshed handle.
    ///
    /// # Errors
    ///
    /// Returns an `OwnershipError` if the receipt is stale or mismatched.
    pub fn commit_transfer(
        &self,
        vm: &mut ProtocolMachine,
        receipt: &OwnershipReceipt,
    ) -> Result<Self, OwnershipError> {
        let capability = vm.sessions_mut().commit_ownership_transfer(receipt)?;
        Ok(Self::new(receipt.session_id, capability))
    }

    /// Attenuate the handle scope and return the refreshed capability.
    ///
    /// # Errors
    ///
    /// Returns an `OwnershipError` if the capability is stale or transfer-pending.
    pub fn attenuate_scope(
        &self,
        vm: &mut ProtocolMachine,
        new_scope: OwnershipScope,
    ) -> Result<Self, OwnershipError> {
        let capability = vm
            .sessions_mut()
            .attenuate_ownership_scope(&self.capability, new_scope)?;
        Ok(Self::new(self.session_id, capability))
    }

    /// Release the live ownership claim for this handle.
    ///
    /// # Errors
    ///
    /// Returns an `OwnershipError` if the capability is stale.
    pub fn release(&self, vm: &mut ProtocolMachine) -> Result<(), OwnershipError> {
        vm.sessions_mut().release_ownership(&self.capability)
    }

    /// Fault the session because the current owner died.
    ///
    /// # Errors
    ///
    /// Returns an `OwnershipError` if the live owner no longer matches this handle.
    pub fn mark_owner_died(&self, vm: &mut ProtocolMachine) -> Result<CancellationWitness, OwnershipError> {
        vm.mark_owner_died(self.session_id, &self.capability.owner_id)
    }

    /// Cancel the session because this transfer was abandoned.
    ///
    /// # Errors
    ///
    /// Returns an `OwnershipError` if the receipt no longer matches the live staged transfer.
    pub fn cancel_abandoned_transfer(
        &self,
        vm: &mut ProtocolMachine,
        receipt: &OwnershipReceipt,
    ) -> Result<CancellationWitness, OwnershipError> {
        vm.cancel_abandoned_transfer(receipt)
    }
}

impl ProtocolMachine {
    /// Preferred choreography open path that immediately claims session ownership.
    ///
    /// Third-party host integrations use this owned helper so subsequent
    /// session-local mutation flows through an explicit ownership capability.
    ///
    /// # Errors
    ///
    /// Returns a `ProtocolMachineError` if the choreography cannot be loaded or the initial
    /// ownership claim fails.
    pub fn load_choreography_owned(
        &mut self,
        image: &CodeImage,
        owner_id: impl Into<String>,
    ) -> Result<OwnedSession, ProtocolMachineError> {
        let sid = self.load_choreography(image)?;
        let capability = self
            .sessions_mut()
            .claim_ownership(sid, owner_id, OwnershipScope::Session)
            .map_err(|err| ProtocolMachineError::OwnershipContract(format!("{err:?}")))?;
        Ok(OwnedSession::new(sid, capability))
    }
}
