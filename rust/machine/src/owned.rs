//! Preferred owned-session helpers for host integration.
//!
//! These wrappers are the preferred public path for embedders that want to
//! respect the host-runtime ownership contract. Lower-level session accessors
//! remain available for tests and internal runtime wiring, but production host
//! mutation should flow through an owned capability.

use crate::engine::{ProtocolMachine, ProtocolMachineError};
use crate::loader::CodeImage;
use crate::session::{
    CancellationWitness, OwnershipCapability, OwnershipError, OwnershipReceipt, OwnershipScope,
    ReadinessWitness, SessionHostMutation, SessionId, SessionState,
};

/// Capability-bearing handle returned by the preferred owned open path.
///
/// Serializable ownership metadata cannot construct an issued handle:
///
/// ```compile_fail,E0451
/// use telltale_machine::{OwnedSession, OwnershipCapability, OwnershipScope};
/// let capability = OwnershipCapability { session_id: 0, owner_id: "owner".into(), generation: 0, scope: OwnershipScope::Session };
/// let owner = OwnedSession { session_id: 0, capability };
/// ```
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

    pub(crate) fn require_receipt_session(
        &self,
        receipt: &OwnershipReceipt,
    ) -> Result<(), OwnershipError> {
        if receipt.session_id != self.session_id {
            return Err(OwnershipError::ReceiptMismatch {
                session_id: self.session_id,
                claim_id: receipt.claim_id,
            });
        }
        Ok(())
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
        machine: &mut impl OwnedSessionMachine,
        mutation: SessionHostMutation,
    ) -> Result<(), OwnershipError> {
        machine.apply_owned_session_mutation(self, mutation)
    }

    /// Issue a single-use readiness witness for a protocol-critical check.
    ///
    /// # Errors
    ///
    /// Returns an `OwnershipError` if the capability is stale or lacks session scope.
    pub fn issue_readiness_witness(
        &self,
        machine: &mut impl OwnedSessionMachine,
        predicate_ref: impl Into<String>,
    ) -> Result<ReadinessWitness, OwnershipError> {
        machine.issue_readiness_witness(self, predicate_ref)
    }

    /// Consume a previously issued readiness witness exactly once.
    ///
    /// # Errors
    ///
    /// Returns an `OwnershipError` if the witness is stale, forged, mismatched, or reused.
    pub fn consume_readiness_witness(
        &self,
        machine: &mut impl OwnedSessionMachine,
        witness: &ReadinessWitness,
    ) -> Result<(), OwnershipError> {
        machine.consume_readiness_witness(self, witness)
    }

    /// Begin an explicit ownership transfer from this handle.
    ///
    /// # Errors
    ///
    /// Returns an `OwnershipError` if the capability is stale.
    pub fn begin_transfer(
        &self,
        machine: &mut impl OwnedSessionMachine,
        new_owner_id: impl Into<String>,
        new_scope: OwnershipScope,
    ) -> Result<OwnershipReceipt, OwnershipError> {
        machine.begin_ownership_transfer(self, new_owner_id, new_scope)
    }

    /// Commit an explicit ownership transfer and return the refreshed handle.
    ///
    /// # Errors
    ///
    /// Returns an `OwnershipError` if the receipt is stale or mismatched.
    pub fn commit_transfer(
        &self,
        machine: &mut impl OwnedSessionMachine,
        receipt: &OwnershipReceipt,
    ) -> Result<Self, OwnershipError> {
        machine.validate_owned_operation(self)?;
        self.require_receipt_session(receipt)?;
        let capability = machine.commit_ownership_transfer(self, receipt)?;
        Ok(Self::new(receipt.session_id, capability))
    }

    /// Roll back exactly this handle's staged transfer, preserving its live owner.
    ///
    /// # Errors
    ///
    /// Returns an ownership error for a stale handle or mismatched receipt.
    pub fn rollback_transfer(
        &self,
        machine: &mut impl OwnedSessionMachine,
        receipt: &OwnershipReceipt,
    ) -> Result<(), OwnershipError> {
        machine.validate_owned_operation(self)?;
        self.require_receipt_session(receipt)?;
        machine.rollback_ownership_transfer(self, receipt)
    }

    /// Attenuate the handle scope and return the refreshed capability.
    ///
    /// # Errors
    ///
    /// Returns an `OwnershipError` if the capability is stale or transfer-pending.
    pub fn attenuate_scope(
        &self,
        machine: &mut impl OwnedSessionMachine,
        new_scope: OwnershipScope,
    ) -> Result<Self, OwnershipError> {
        let capability = machine.attenuate_ownership_scope(self, new_scope)?;
        Ok(Self::new(self.session_id, capability))
    }

    /// Release the live ownership claim for this handle.
    ///
    /// # Errors
    ///
    /// Returns an `OwnershipError` if the capability is stale.
    pub fn release(&self, machine: &mut impl OwnedSessionMachine) -> Result<(), OwnershipError> {
        machine.release_ownership(self)
    }

    /// Fault the session because the current owner died.
    ///
    /// # Errors
    ///
    /// Returns an `OwnershipError` if the live owner no longer matches this handle.
    pub fn mark_owner_died(
        &self,
        machine: &mut impl OwnedSessionMachine,
    ) -> Result<CancellationWitness, OwnershipError> {
        machine.validate_owned_operation(self)?;
        machine.owned_mark_owner_died(self)
    }

    /// Fault the original session when its staged transfer cannot commit.
    ///
    /// The reason is diagnostic semantic data. The host retains any original
    /// native failure and remains responsible for acknowledged resource cleanup.
    ///
    /// # Errors
    ///
    /// Rejects a stale handle or a receipt outside this handle's staged session.
    pub fn fault_failed_transfer_commit(
        &self,
        machine: &mut impl OwnedSessionMachine,
        receipt: &OwnershipReceipt,
        reason: impl Into<String>,
    ) -> Result<(), OwnershipError> {
        machine.validate_owned_operation(self)?;
        self.require_receipt_session(receipt)?;
        machine.owned_fault_failed_transfer_commit(self, receipt, reason)
    }

    /// Cancel the session because this transfer was abandoned.
    ///
    /// # Errors
    ///
    /// Returns an `OwnershipError` if the receipt no longer matches the live staged transfer.
    pub fn cancel_abandoned_transfer(
        &self,
        machine: &mut impl OwnedSessionMachine,
        receipt: &OwnershipReceipt,
    ) -> Result<CancellationWitness, OwnershipError> {
        machine.validate_owned_operation(self)?;
        self.require_receipt_session(receipt)?;
        machine.owned_cancel_abandoned_transfer(self, receipt)
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
        let tick = self.clock().tick;
        let capability = self
            .sessions_mut()
            .with_owned_session_at(sid, Some(tick), |session| {
                session.claim_ownership(sid, owner_id, OwnershipScope::Session)
            })
            .map_err(ProtocolMachineError::OwnershipContract)?;
        let owner = OwnedSession::new(sid, capability);
        self.bind_nominal_owner(&owner);
        Ok(owner)
    }
}

mod private {
    pub trait Sealed {}
    impl Sealed for crate::ProtocolMachine {}
    #[cfg(feature = "multi-thread")]
    impl Sealed for crate::ThreadedProtocolMachine {}
}
/// Sanctioned host-ownership operations shared by both machine backends.
///
/// Implementations exclusively borrow the real resident session and use the same
/// canonical transitions. This capability contract does not own host futures or
/// acknowledge asynchronous resource cleanup.
/// Raw capability fields cannot replace the issued handle at this boundary:
///
/// ```compile_fail,E0308
/// use telltale_machine::{ProtocolMachine, ProtocolMachineConfig, OwnershipCapability, OwnershipScope, SessionHostMutation};
/// use telltale_machine::owned::OwnedSessionMachine;
/// let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
/// let fields = OwnershipCapability { session_id: 0, owner_id: "owner".into(), generation: 0, scope: OwnershipScope::Session };
/// machine.apply_owned_session_mutation(&fields, SessionHostMutation::SetDefaultHandler { handler: "replacement".into() }).unwrap();
/// ```
pub trait OwnedSessionMachine: private::Sealed {
    /// Admit an owned operation and retain actual capability-rejection evidence.
    ///
    /// # Errors
    ///
    /// Rejects missing, stale, mismatched or insufficient authority.
    fn validate_owned_operation(&mut self, owner: &OwnedSession) -> Result<(), OwnershipError>;

    /// Apply owned session mutation using the actual resident session.
    ///
    /// # Errors
    ///
    /// Rejects missing, stale, mismatched or insufficient authority.
    fn apply_owned_session_mutation(
        &mut self,
        owner: &OwnedSession,
        mutation: SessionHostMutation,
    ) -> Result<(), OwnershipError>;

    /// Issue readiness witness using the actual resident session.
    ///
    /// # Errors
    ///
    /// Rejects missing, stale, mismatched or insufficient authority.
    fn issue_readiness_witness(
        &mut self,
        owner: &OwnedSession,
        predicate_ref: impl Into<String>,
    ) -> Result<ReadinessWitness, OwnershipError>;

    /// Consume readiness witness using the actual resident session.
    ///
    /// # Errors
    ///
    /// Rejects missing, stale, mismatched or insufficient authority.
    fn consume_readiness_witness(
        &mut self,
        owner: &OwnedSession,
        witness: &ReadinessWitness,
    ) -> Result<(), OwnershipError>;

    /// Begin ownership transfer using the actual resident session.
    ///
    /// # Errors
    ///
    /// Rejects missing, stale, mismatched or insufficient authority.
    fn begin_ownership_transfer(
        &mut self,
        owner: &OwnedSession,
        new_owner_id: impl Into<String>,
        new_scope: OwnershipScope,
    ) -> Result<OwnershipReceipt, OwnershipError>;

    /// Commit ownership transfer using the actual resident session.
    ///
    /// # Errors
    ///
    /// Rejects missing, stale, mismatched or insufficient authority.
    fn commit_ownership_transfer(
        &mut self,
        owner: &OwnedSession,
        receipt: &OwnershipReceipt,
    ) -> Result<OwnershipCapability, OwnershipError>;

    /// Rollback ownership transfer using the actual resident session.
    ///
    /// # Errors
    ///
    /// Rejects missing, stale, mismatched or insufficient authority.
    fn rollback_ownership_transfer(
        &mut self,
        owner: &OwnedSession,
        receipt: &OwnershipReceipt,
    ) -> Result<(), OwnershipError>;

    /// Attenuate ownership scope using the actual resident session.
    ///
    /// # Errors
    ///
    /// Rejects missing, stale, mismatched or insufficient authority.
    fn attenuate_ownership_scope(
        &mut self,
        owner: &OwnedSession,
        new_scope: OwnershipScope,
    ) -> Result<OwnershipCapability, OwnershipError>;

    /// Release ownership using the actual resident session.
    ///
    /// # Errors
    ///
    /// Rejects missing, stale, mismatched or insufficient authority.
    fn release_ownership(&mut self, owner: &OwnedSession) -> Result<(), OwnershipError>;
    /// Fault the actual session and invalidate its outstanding semantic work.
    ///
    /// # Errors
    ///
    /// Rejects missing, stale or terminal ownership.
    fn owned_mark_owner_died(
        &mut self,
        owner: &OwnedSession,
    ) -> Result<CancellationWitness, OwnershipError>;
    /// Record a failed transfer commit and invalidate its semantic work.
    ///
    /// # Errors
    ///
    /// Rejects a receipt outside the actual staged transfer.
    fn owned_fault_failed_transfer_commit(
        &mut self,
        owner: &OwnedSession,
        receipt: &OwnershipReceipt,
        reason: impl Into<String>,
    ) -> Result<(), OwnershipError>;

    /// Cancel the actual staged transfer and record its semantic terminal order.
    ///
    /// # Errors
    ///
    /// Rejects a receipt that does not match the live staged transfer.
    fn owned_cancel_abandoned_transfer(
        &mut self,
        owner: &OwnedSession,
        receipt: &OwnershipReceipt,
    ) -> Result<CancellationWitness, OwnershipError>;
}
impl OwnedSessionMachine for ProtocolMachine {
    fn validate_owned_operation(&mut self, owner: &OwnedSession) -> Result<(), OwnershipError> {
        let tick = self.clock().tick;
        self.sessions_mut()
            .with_owned_session_at(owner.session_id(), Some(tick), |session| {
                SessionState::validate_mutating_owner(session, owner.capability())
            })
    }

    fn apply_owned_session_mutation(
        &mut self,
        owner: &OwnedSession,
        mutation: SessionHostMutation,
    ) -> Result<(), OwnershipError> {
        let capability = owner.capability();
        let tick = self.clock().tick;
        self.sessions_mut()
            .with_owned_session_at(capability.session_id, Some(tick), |session| {
                session.apply_owned_session_mutation(capability, mutation)
            })
    }

    fn issue_readiness_witness(
        &mut self,
        owner: &OwnedSession,
        predicate_ref: impl Into<String>,
    ) -> Result<ReadinessWitness, OwnershipError> {
        let capability = owner.capability();
        let tick = self.clock().tick;
        self.sessions_mut()
            .with_owned_session_at(capability.session_id, Some(tick), |session| {
                session.issue_readiness_witness(capability, predicate_ref)
            })
    }

    fn consume_readiness_witness(
        &mut self,
        owner: &OwnedSession,
        witness: &ReadinessWitness,
    ) -> Result<(), OwnershipError> {
        let capability = owner.capability();
        let tick = self.clock().tick;
        self.sessions_mut()
            .with_owned_session_at(capability.session_id, Some(tick), |session| {
                session.consume_readiness_witness(capability, witness)
            })
    }

    fn begin_ownership_transfer(
        &mut self,
        owner: &OwnedSession,
        new_owner_id: impl Into<String>,
        new_scope: OwnershipScope,
    ) -> Result<OwnershipReceipt, OwnershipError> {
        let capability = owner.capability();
        let tick = self.clock().tick;
        self.sessions_mut()
            .with_owned_session_at(capability.session_id, Some(tick), |session| {
                session.begin_ownership_transfer(capability, new_owner_id, new_scope)
            })
    }

    fn commit_ownership_transfer(
        &mut self,
        owner: &OwnedSession,
        receipt: &OwnershipReceipt,
    ) -> Result<OwnershipCapability, OwnershipError> {
        self.validate_owned_operation(owner)?;
        owner.require_receipt_session(receipt)?;
        let tick = self.clock().tick;
        self.sessions_mut()
            .with_owned_session_at(receipt.session_id, Some(tick), |session| {
                session.commit_ownership_transfer(receipt)
            })
    }

    fn rollback_ownership_transfer(
        &mut self,
        owner: &OwnedSession,
        receipt: &OwnershipReceipt,
    ) -> Result<(), OwnershipError> {
        self.validate_owned_operation(owner)?;
        owner.require_receipt_session(receipt)?;
        let tick = self.clock().tick;
        self.sessions_mut()
            .with_owned_session_at(receipt.session_id, Some(tick), |session| {
                session.rollback_ownership_transfer(receipt)
            })
    }

    fn attenuate_ownership_scope(
        &mut self,
        owner: &OwnedSession,
        new_scope: OwnershipScope,
    ) -> Result<OwnershipCapability, OwnershipError> {
        let capability = owner.capability();
        let tick = self.clock().tick;
        self.sessions_mut()
            .with_owned_session_at(capability.session_id, Some(tick), |session| {
                session.attenuate_ownership_scope(capability, new_scope)
            })
    }

    fn release_ownership(&mut self, owner: &OwnedSession) -> Result<(), OwnershipError> {
        let capability = owner.capability();
        let tick = self.clock().tick;
        self.sessions_mut()
            .with_owned_session_at(capability.session_id, Some(tick), |session| {
                session.release_ownership(capability)
            })
    }
    fn owned_mark_owner_died(
        &mut self,
        owner: &OwnedSession,
    ) -> Result<CancellationWitness, OwnershipError> {
        self.validate_owned_operation(owner)?;
        self.mark_owner_died(owner.session_id(), &owner.capability().owner_id)
    }
    fn owned_cancel_abandoned_transfer(
        &mut self,
        owner: &OwnedSession,
        receipt: &OwnershipReceipt,
    ) -> Result<CancellationWitness, OwnershipError> {
        self.validate_owned_operation(owner)?;
        owner.require_receipt_session(receipt)?;
        self.cancel_abandoned_transfer(receipt)
    }
    fn owned_fault_failed_transfer_commit(
        &mut self,
        owner: &OwnedSession,
        receipt: &OwnershipReceipt,
        reason: impl Into<String>,
    ) -> Result<(), OwnershipError> {
        self.validate_owned_operation(owner)?;
        owner.require_receipt_session(receipt)?;
        self.fault_failed_transfer_commit(receipt, reason)
    }
}
