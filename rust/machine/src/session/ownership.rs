// Canonical host-ownership transitions shared by both storage backends.
// Store adapters select and exclusively borrow the real resident session.
impl SessionState {
    pub(crate) fn authority_records_since(&mut self, start: usize) -> &mut [AuthorityAuditRecord] {
        &mut self.ownership.audit_log[start..]
    }

    fn terminal_error(session: &SessionState) -> Option<OwnershipError> {
        session
            .ownership
            .terminal_reason
            .clone()
            .map(|reason| OwnershipError::Terminal {
                session_id: session.sid,
                reason,
            })
    }

    fn ensure_mutable_ownership(session: &SessionState) -> Result<(), OwnershipError> {
        if let Some(err) = Self::terminal_error(session) {
            return Err(err);
        }
        Ok(())
    }

    pub(crate) fn validate_current_owner(
        session: &SessionState,
        capability: &OwnershipCapability,
    ) -> Result<(), OwnershipError> {
        Self::ensure_mutable_ownership(session)?;
        let Some(current) = session.ownership.current.as_ref() else {
            return Err(OwnershipError::Unclaimed {
                session_id: session.sid,
            });
        };
        if current.owner_id != capability.owner_id || current.generation != capability.generation {
            return Err(OwnershipError::StaleCapability {
                session_id: session.sid,
                owner_id: capability.owner_id.clone(),
                expected_generation: capability.generation,
                actual_generation: current.generation,
            });
        }
        Ok(())
    }

    pub(crate) fn validate_mutating_owner(
        session: &mut SessionState,
        capability: &OwnershipCapability,
    ) -> Result<(), OwnershipError> {
        let result = Self::validate_current_owner(session, capability);
        if let Err(error) = &result {
            Self::push_authority_audit(
                session,
                AuthorityArtifact::OwnershipCapability(capability.clone()),
                AuthorityAuditEvent::Rejected,
                Some(error.to_string()),
            );
        }
        result
    }

    fn require_session_scope(
        session: &mut SessionState,
        capability: &OwnershipCapability,
    ) -> Result<(), OwnershipError> {
        Self::validate_mutating_owner(session, capability)?;
        let Some(current) = session.ownership.current.as_ref() else {
            return Err(OwnershipError::Unclaimed {
                session_id: session.sid,
            });
        };
        if !current.scope.allows_session_mutation() {
            return Err(OwnershipError::ScopeViolation {
                session_id: session.sid,
                owner_id: current.owner_id.clone(),
                required: OwnershipScope::Session,
                actual: current.scope.clone(),
            });
        }
        Ok(())
    }

    fn next_witness_id(session: &mut SessionState) -> Result<AuthorityWitnessId, OwnershipError> {
        let witness_id = session.ownership.next_witness_id;
        session.ownership.next_witness_id = Self::advance_counter(session, witness_id, "witness")?;
        Ok(witness_id)
    }

    fn advance_counter(
        session: &SessionState,
        value: u64,
        counter: &str,
    ) -> Result<u64, OwnershipError> {
        value
            .checked_add(1)
            .ok_or_else(|| OwnershipError::CounterExhausted {
                session_id: session.sid,
                counter: counter.to_string(),
            })
    }

    fn require_attenuation(
        session: &SessionState,
        new_scope: &OwnershipScope,
    ) -> Result<(), OwnershipError> {
        let current = session
            .ownership
            .current
            .as_ref()
            .ok_or(OwnershipError::Unclaimed {
                session_id: session.sid,
            })?;
        if !new_scope.is_attenuation_of(&current.scope) {
            return Err(OwnershipError::ScopeViolation {
                session_id: session.sid,
                owner_id: current.owner_id.clone(),
                required: new_scope.clone(),
                actual: current.scope.clone(),
            });
        }
        Ok(())
    }

    fn push_authority_audit(
        session: &mut SessionState,
        artifact: AuthorityArtifact,
        event: AuthorityAuditEvent,
        reason: Option<String>,
    ) {
        session.ownership.audit_log.push(AuthorityAuditRecord {
            tick: None,
            artifact,
            event,
            reason,
        });
    }

    pub(crate) fn claim_ownership(
        &mut self,
        sid: SessionId,
        owner_id: impl Into<FragmentOwnerId>,
        scope: OwnershipScope,
    ) -> Result<OwnershipCapability, OwnershipError> {
        let session = self;
        Self::ensure_mutable_ownership(session)?;
        if let Some(current) = session.ownership.current.as_ref() {
            return Err(OwnershipError::AlreadyClaimed {
                session_id: sid,
                current_owner_id: current.owner_id.clone(),
            });
        }
        if let Some(pending) = session.ownership.pending_transfer.as_ref() {
            return Err(OwnershipError::TransferPending {
                session_id: sid,
                claim_id: pending.receipt.claim_id,
            });
        }
        let previous_generation = session.ownership.last_generation.or_else(|| {
            session
                .ownership
                .audit_log
                .iter()
                .filter_map(|record| match &record.artifact {
                    AuthorityArtifact::OwnershipCapability(capability) => {
                        Some(capability.generation)
                    }
                    _ => None,
                })
                .max()
        });
        let generation = match previous_generation {
            Some(previous) => Self::advance_counter(session, previous, "generation")?,
            None => 0,
        };
        let capability = OwnershipCapability {
            session_id: sid,
            owner_id: owner_id.into(),
            generation,
            scope,
        };
        session.ownership.last_generation = Some(capability.generation);
        session.ownership.current = Some(capability.clone());
        Self::push_authority_audit(
            session,
            AuthorityArtifact::OwnershipCapability(capability.clone()),
            AuthorityAuditEvent::Issued,
            None,
        );
        Ok(capability)
    }

    pub(crate) fn release_ownership(
        &mut self,
        capability: &OwnershipCapability,
    ) -> Result<(), OwnershipError> {
        let session = self;
        Self::validate_mutating_owner(session, capability)?;
        if let Some(pending) = session.ownership.pending_transfer.as_ref() {
            return Err(OwnershipError::TransferPending {
                session_id: capability.session_id,
                claim_id: pending.receipt.claim_id,
            });
        }
        Self::push_authority_audit(
            session,
            AuthorityArtifact::OwnershipCapability(capability.clone()),
            AuthorityAuditEvent::Invalidated,
            Some("ownership released".to_string()),
        );
        session.ownership.last_generation = Some(capability.generation);
        session.ownership.current = None;
        Ok(())
    }

    pub(crate) fn begin_ownership_transfer(
        &mut self,
        capability: &OwnershipCapability,
        new_owner_id: impl Into<FragmentOwnerId>,
        new_scope: OwnershipScope,
    ) -> Result<OwnershipReceipt, OwnershipError> {
        let session = self;
        Self::validate_mutating_owner(session, capability)?;
        if let Some(pending) = session.ownership.pending_transfer.as_ref() {
            return Err(OwnershipError::TransferPending {
                session_id: capability.session_id,
                claim_id: pending.receipt.claim_id,
            });
        }
        Self::require_attenuation(session, &new_scope)?;
        let to_generation = Self::advance_counter(session, capability.generation, "generation")?;
        let claim_id = session.ownership.next_claim_id;
        session.ownership.next_claim_id = Self::advance_counter(session, claim_id, "claim")?;
        let receipt = OwnershipReceipt {
            session_id: capability.session_id,
            claim_id,
            from_owner_id: capability.owner_id.clone(),
            from_generation: capability.generation,
            to_owner_id: new_owner_id.into(),
            to_generation,
            scope: new_scope,
        };
        session.ownership.pending_transfer = Some(PendingOwnershipTransfer {
            receipt: receipt.clone(),
        });
        Self::push_authority_audit(
            session,
            AuthorityArtifact::OwnershipReceipt(receipt.clone()),
            AuthorityAuditEvent::Issued,
            None,
        );
        Ok(receipt)
    }

    pub(crate) fn commit_ownership_transfer(
        &mut self,
        receipt: &OwnershipReceipt,
    ) -> Result<OwnershipCapability, OwnershipError> {
        let session = self;
        Self::ensure_mutable_ownership(session)?;
        let Some(current) = session.ownership.current.as_ref() else {
            return Err(OwnershipError::Unclaimed {
                session_id: receipt.session_id,
            });
        };
        let Some(pending) = session.ownership.pending_transfer.as_ref() else {
            Self::push_authority_audit(
                session,
                AuthorityArtifact::OwnershipReceipt(receipt.clone()),
                AuthorityAuditEvent::Rejected,
                Some("receipt is no longer pending".to_string()),
            );
            return Err(OwnershipError::TransferNotPending {
                session_id: receipt.session_id,
            });
        };
        if pending.receipt != *receipt {
            Self::push_authority_audit(
                session,
                AuthorityArtifact::OwnershipReceipt(receipt.clone()),
                AuthorityAuditEvent::Rejected,
                Some("receipt payload mismatch".to_string()),
            );
            return Err(OwnershipError::ReceiptMismatch {
                session_id: receipt.session_id,
                claim_id: receipt.claim_id,
            });
        }
        if current.owner_id != receipt.from_owner_id
            || current.generation != receipt.from_generation
        {
            return Err(OwnershipError::StaleCapability {
                session_id: receipt.session_id,
                owner_id: receipt.from_owner_id.clone(),
                expected_generation: receipt.from_generation,
                actual_generation: current.generation,
            });
        }
        let capability = OwnershipCapability {
            session_id: receipt.session_id,
            owner_id: receipt.to_owner_id.clone(),
            generation: receipt.to_generation,
            scope: receipt.scope.clone(),
        };
        let old_capability = current.clone();
        session.ownership.last_generation = Some(capability.generation);
        session.ownership.current = Some(capability.clone());
        session.ownership.pending_transfer = None;
        Self::push_authority_audit(
            session,
            AuthorityArtifact::OwnershipCapability(old_capability),
            AuthorityAuditEvent::Invalidated,
            Some("ownership transferred".to_string()),
        );
        Self::push_authority_audit(
            session,
            AuthorityArtifact::OwnershipReceipt(receipt.clone()),
            AuthorityAuditEvent::Committed,
            None,
        );
        Self::push_authority_audit(
            session,
            AuthorityArtifact::OwnershipCapability(capability.clone()),
            AuthorityAuditEvent::Issued,
            None,
        );
        Ok(capability)
    }

    pub(crate) fn rollback_ownership_transfer(
        &mut self,
        receipt: &OwnershipReceipt,
    ) -> Result<(), OwnershipError> {
        let session = self;
        Self::ensure_mutable_ownership(session)?;
        let Some(pending) = session.ownership.pending_transfer.as_ref() else {
            Self::push_authority_audit(
                session,
                AuthorityArtifact::OwnershipReceipt(receipt.clone()),
                AuthorityAuditEvent::Rejected,
                Some("receipt is no longer pending".to_string()),
            );
            return Err(OwnershipError::TransferNotPending {
                session_id: receipt.session_id,
            });
        };
        if pending.receipt != *receipt {
            Self::push_authority_audit(
                session,
                AuthorityArtifact::OwnershipReceipt(receipt.clone()),
                AuthorityAuditEvent::Rejected,
                Some("receipt payload mismatch".to_string()),
            );
            return Err(OwnershipError::ReceiptMismatch {
                session_id: receipt.session_id,
                claim_id: receipt.claim_id,
            });
        }
        session.ownership.pending_transfer = None;
        Self::push_authority_audit(
            session,
            AuthorityArtifact::OwnershipReceipt(receipt.clone()),
            AuthorityAuditEvent::RolledBack,
            None,
        );
        Ok(())
    }

    pub(crate) fn attenuate_ownership_scope(
        &mut self,
        capability: &OwnershipCapability,
        new_scope: OwnershipScope,
    ) -> Result<OwnershipCapability, OwnershipError> {
        let session = self;
        Self::validate_mutating_owner(session, capability)?;
        if let Some(pending) = session.ownership.pending_transfer.as_ref() {
            return Err(OwnershipError::TransferPending {
                session_id: capability.session_id,
                claim_id: pending.receipt.claim_id,
            });
        }
        Self::require_attenuation(session, &new_scope)?;
        let generation = Self::advance_counter(session, capability.generation, "generation")?;
        let next = OwnershipCapability {
            session_id: capability.session_id,
            owner_id: capability.owner_id.clone(),
            generation,
            scope: new_scope,
        };
        Self::push_authority_audit(
            session,
            AuthorityArtifact::OwnershipCapability(capability.clone()),
            AuthorityAuditEvent::Invalidated,
            Some("ownership scope attenuated".to_string()),
        );
        session.ownership.last_generation = Some(next.generation);
        session.ownership.current = Some(next.clone());
        Self::push_authority_audit(
            session,
            AuthorityArtifact::OwnershipCapability(next.clone()),
            AuthorityAuditEvent::Issued,
            None,
        );
        Ok(next)
    }

    pub(crate) fn apply_owned_session_mutation(
        &mut self,
        capability: &OwnershipCapability,
        mutation: SessionHostMutation,
    ) -> Result<(), OwnershipError> {
        let session = self;
        Self::require_session_scope(session, capability)?;
        let edge = match &mutation {
            SessionHostMutation::UpdateEdgeHandler { edge, .. }
            | SessionHostMutation::UpdateTrace { edge, .. } => Some(edge),
            SessionHostMutation::SetDefaultHandler { .. } => None,
        };
        if let Some(edge) = edge {
            if edge.sid != session.sid {
                return Err(OwnershipError::SessionMismatch {
                    session_id: session.sid,
                    supplied_session_id: edge.sid,
                });
            }
        }
        match mutation {
            SessionHostMutation::SetDefaultHandler { handler } => {
                let handler_id = session.intern_handler_binding(&handler);
                session.default_handler = handler;
                session.default_handler_id = Some(handler_id);
            }
            SessionHostMutation::UpdateEdgeHandler { edge, handler } => {
                let handler_id = session.intern_handler_binding(&handler);
                if let Some(edge_key) = session.edge_key_for_roles(&edge.sender, &edge.receiver) {
                    session.edge_handler_lookup.insert(edge_key, handler_id);
                }
                session.edge_handlers.insert(edge, handler);
            }
            SessionHostMutation::UpdateTrace { edge, trace } => {
                session.edge_traces.insert(edge, trace);
            }
        }
        Ok(())
    }

    pub(crate) fn issue_readiness_witness(
        &mut self,
        capability: &OwnershipCapability,
        predicate_ref: impl Into<String>,
    ) -> Result<ReadinessWitness, OwnershipError> {
        let session = self;
        Self::require_session_scope(session, capability)?;
        let witness = ReadinessWitness {
            witness_id: Self::next_witness_id(session)?,
            session_id: capability.session_id,
            owner_id: capability.owner_id.clone(),
            generation: capability.generation,
            scope: capability.scope.clone(),
            predicate_ref: predicate_ref.into(),
        };
        session
            .ownership
            .issued_readiness
            .insert(witness.witness_id, witness.clone());
        Self::push_authority_audit(
            session,
            AuthorityArtifact::Readiness(witness.clone()),
            AuthorityAuditEvent::Issued,
            None,
        );
        Ok(witness)
    }

    pub(crate) fn consume_readiness_witness(
        &mut self,
        capability: &OwnershipCapability,
        witness: &ReadinessWitness,
    ) -> Result<(), OwnershipError> {
        let session = self;
        Self::require_session_scope(session, capability)?;
        if session
            .ownership
            .consumed_witnesses
            .contains(&witness.witness_id)
        {
            Self::push_authority_audit(
                session,
                AuthorityArtifact::Readiness(witness.clone()),
                AuthorityAuditEvent::Rejected,
                Some("witness already consumed".to_string()),
            );
            return Err(OwnershipError::WitnessConsumed {
                session_id: witness.session_id,
                witness_id: witness.witness_id,
            });
        }
        let Some(issued) = session.ownership.issued_readiness.get(&witness.witness_id) else {
            Self::push_authority_audit(
                session,
                AuthorityArtifact::Readiness(witness.clone()),
                AuthorityAuditEvent::Rejected,
                Some("witness was never issued".to_string()),
            );
            return Err(OwnershipError::InvalidWitness {
                session_id: capability.session_id,
                witness_id: witness.witness_id,
                reason: "witness was never issued".to_string(),
            });
        };
        if issued != witness {
            Self::push_authority_audit(
                session,
                AuthorityArtifact::Readiness(witness.clone()),
                AuthorityAuditEvent::Rejected,
                Some("witness payload mismatch".to_string()),
            );
            return Err(OwnershipError::InvalidWitness {
                session_id: capability.session_id,
                witness_id: witness.witness_id,
                reason: "witness payload mismatch".to_string(),
            });
        }
        if witness.session_id != capability.session_id
            || witness.owner_id != capability.owner_id
            || witness.generation != capability.generation
            || witness.scope != capability.scope
        {
            Self::push_authority_audit(
                session,
                AuthorityArtifact::Readiness(witness.clone()),
                AuthorityAuditEvent::Rejected,
                Some("live ownership no longer matches witness".to_string()),
            );
            return Err(OwnershipError::InvalidWitness {
                session_id: capability.session_id,
                witness_id: witness.witness_id,
                reason: "live ownership no longer matches witness".to_string(),
            });
        }
        session
            .ownership
            .issued_readiness
            .remove(&witness.witness_id);
        session
            .ownership
            .consumed_witnesses
            .insert(witness.witness_id);
        Self::push_authority_audit(
            session,
            AuthorityArtifact::Readiness(witness.clone()),
            AuthorityAuditEvent::Consumed,
            None,
        );
        Ok(())
    }

    pub(crate) fn mark_owner_died(
        &mut self,
        sid: SessionId,
        owner_id: &str,
    ) -> Result<CancellationWitness, OwnershipError> {
        let session = self;
        Self::ensure_mutable_ownership(session)?;
        let Some(current) = session.ownership.current.clone() else {
            return Err(OwnershipError::Unclaimed { session_id: sid });
        };
        if current.owner_id != owner_id {
            return Err(OwnershipError::StaleCapability {
                session_id: sid,
                owner_id: owner_id.to_string(),
                expected_generation: current.generation,
                actual_generation: current.generation,
            });
        }
        let generation = current.generation;
        let reason = OwnershipTerminalReason::OwnerDied {
            owner_id: owner_id.to_string(),
        };
        let witness_id = Self::next_witness_id(session)?;
        session.status = SessionStatus::Faulted {
            reason: format!("ownership owner `{owner_id}` died"),
        };
        let witness = CancellationWitness {
            witness_id,
            session_id: sid,
            owner_id: owner_id.to_string(),
            generation,
            reason: reason.clone(),
        };
        session.ownership.current = None;
        session.ownership.pending_transfer = None;
        session.ownership.terminal_reason = Some(reason);
        Self::push_authority_audit(
            session,
            AuthorityArtifact::OwnershipCapability(current),
            AuthorityAuditEvent::Invalidated,
            Some("owner died".to_string()),
        );
        Self::push_authority_audit(
            session,
            AuthorityArtifact::Cancellation(witness.clone()),
            AuthorityAuditEvent::Issued,
            None,
        );
        Ok(witness)
    }

    pub(crate) fn cancel_abandoned_transfer(
        &mut self,
        receipt: &OwnershipReceipt,
    ) -> Result<CancellationWitness, OwnershipError> {
        let session = self;
        Self::ensure_mutable_ownership(session)?;
        let Some(pending) = session.ownership.pending_transfer.as_ref() else {
            return Err(OwnershipError::TransferNotPending {
                session_id: receipt.session_id,
            });
        };
        if pending.receipt != *receipt {
            return Err(OwnershipError::ReceiptMismatch {
                session_id: receipt.session_id,
                claim_id: receipt.claim_id,
            });
        }
        let reason = OwnershipTerminalReason::TransferAbandoned {
            owner_id: receipt.from_owner_id.clone(),
            claim_id: receipt.claim_id,
        };
        let witness_id = Self::next_witness_id(session)?;
        session.status = SessionStatus::Cancelled;
        let witness = CancellationWitness {
            witness_id,
            session_id: receipt.session_id,
            owner_id: receipt.from_owner_id.clone(),
            generation: receipt.from_generation,
            reason: reason.clone(),
        };
        if let Some(current) = session.ownership.current.clone() {
            Self::push_authority_audit(
                session,
                AuthorityArtifact::OwnershipCapability(current),
                AuthorityAuditEvent::Invalidated,
                Some("transfer abandoned".to_string()),
            );
        }
        session.ownership.current = None;
        session.ownership.pending_transfer = None;
        session.ownership.terminal_reason = Some(reason);
        Self::push_authority_audit(
            session,
            AuthorityArtifact::OwnershipReceipt(receipt.clone()),
            AuthorityAuditEvent::RolledBack,
            Some("transfer abandoned".to_string()),
        );
        Self::push_authority_audit(
            session,
            AuthorityArtifact::Cancellation(witness.clone()),
            AuthorityAuditEvent::Issued,
            None,
        );
        Ok(witness)
    }

    pub(crate) fn fault_failed_transfer_commit(
        &mut self,
        receipt: &OwnershipReceipt,
        reason: impl Into<String>,
    ) -> Result<(), OwnershipError> {
        let session = self;
        Self::ensure_mutable_ownership(session)?;
        let Some(pending) = session.ownership.pending_transfer.as_ref() else {
            return Err(OwnershipError::TransferNotPending {
                session_id: receipt.session_id,
            });
        };
        if pending.receipt != *receipt {
            return Err(OwnershipError::ReceiptMismatch {
                session_id: receipt.session_id,
                claim_id: receipt.claim_id,
            });
        }
        let reason = reason.into();
        let terminal = OwnershipTerminalReason::TransferCommitFailed {
            owner_id: receipt.from_owner_id.clone(),
            claim_id: receipt.claim_id,
            reason: reason.clone(),
        };
        session.status = SessionStatus::Faulted {
            reason: format!("ownership transfer commit failed: {reason}"),
        };
        if let Some(current) = session.ownership.current.clone() {
            Self::push_authority_audit(
                session,
                AuthorityArtifact::OwnershipCapability(current),
                AuthorityAuditEvent::Invalidated,
                Some("transfer commit failed".to_string()),
            );
        }
        session.ownership.current = None;
        session.ownership.pending_transfer = None;
        session.ownership.terminal_reason = Some(terminal);
        Self::push_authority_audit(
            session,
            AuthorityArtifact::OwnershipReceipt(receipt.clone()),
            AuthorityAuditEvent::RolledBack,
            Some(reason),
        );
        Ok(())
    }
}

#[cfg(test)]
mod ownership_preflight_tests {
    use super::*;

    fn owned_session() -> (SessionState, OwnershipCapability) {
        let roles = vec!["A".to_string(), "B".to_string()];
        let plan = SessionOpenPlan::new(&roles, &BTreeMap::new());
        let mut session = SessionState::from_open_plan(0, &plan, &BufferConfig::default());
        let capability = session
            .claim_ownership(0, "owner", OwnershipScope::Session)
            .unwrap();
        (session, capability)
    }

    #[wasm_bindgen_test::wasm_bindgen_test(unsupported = test)]
    fn ownership_release_reclaim_never_reactivates_an_old_generation() {
        let (mut session, old) = owned_session();
        session.release_ownership(&old).unwrap();
        // Older snapshots do not carry last_generation; canonical issued history
        // still prevents resetting the generation to zero on a subsequent claim.
        session.ownership.last_generation = None;
        let mut bytes = Vec::new();
        ciborium::into_writer(&session, &mut bytes).unwrap();
        let mut restored: SessionState = ciborium::from_reader(bytes.as_slice()).unwrap();
        let new = restored
            .claim_ownership(0, "owner", OwnershipScope::Session)
            .unwrap();
        assert!(new.generation > old.generation);
        assert!(matches!(
            SessionState::validate_current_owner(&restored, &old),
            Err(OwnershipError::StaleCapability { .. })
        ));
        SessionState::validate_current_owner(&restored, &new).unwrap();
    }

    #[wasm_bindgen_test::wasm_bindgen_test(unsupported = test)]
    fn ownership_scope_transfer_and_attenuation_cannot_escalate() {
        let (mut session, owner) = owned_session();
        let narrow = session
            .attenuate_ownership_scope(
                &owner,
                OwnershipScope::Fragments(BTreeSet::from(["A".into()])),
            )
            .unwrap();
        let before = session.ownership.clone();
        for scope in [
            OwnershipScope::Session,
            OwnershipScope::Fragments(BTreeSet::from(["B".into()])),
        ] {
            assert!(matches!(
                session.attenuate_ownership_scope(&narrow, scope.clone()),
                Err(OwnershipError::ScopeViolation { .. })
            ));
            assert_eq!(before, session.ownership);
            assert!(matches!(
                session.begin_ownership_transfer(&narrow, "next", scope),
                Err(OwnershipError::ScopeViolation { .. })
            ));
            assert_eq!(before, session.ownership);
        }
    }

    #[wasm_bindgen_test::wasm_bindgen_test(unsupported = test)]
    fn ownership_identifier_exhaustion_is_preflight_only() {
        let (mut session, mut owner) = owned_session();
        session.ownership.next_claim_id = u64::MAX;
        let before = session.ownership.clone();
        assert!(matches!(
            session.begin_ownership_transfer(&owner, "next", OwnershipScope::Session),
            Err(OwnershipError::CounterExhausted { .. })
        ));
        assert_eq!(before, session.ownership);
        session.ownership.next_claim_id = 1;
        owner.generation = u64::MAX;
        session.ownership.current = Some(owner.clone());
        let before = session.ownership.clone();
        assert!(matches!(
            session.begin_ownership_transfer(&owner, "next", OwnershipScope::Session),
            Err(OwnershipError::CounterExhausted { .. })
        ));
        assert_eq!(before, session.ownership);
        assert!(matches!(
            session.attenuate_ownership_scope(&owner, OwnershipScope::Fragments(BTreeSet::new())),
            Err(OwnershipError::CounterExhausted { .. })
        ));
        assert_eq!(before, session.ownership);
        session.release_ownership(&owner).unwrap();
        let before = session.ownership.clone();
        assert!(matches!(
            session.claim_ownership(0, "owner", OwnershipScope::Session),
            Err(OwnershipError::CounterExhausted { .. })
        ));
        assert_eq!(before, session.ownership);
    }

    #[wasm_bindgen_test::wasm_bindgen_test(unsupported = test)]
    fn ownership_witness_exhaustion_preserves_original_pending_owner() {
        let (mut session, owner) = owned_session();
        let receipt = session
            .begin_ownership_transfer(&owner, "next", OwnershipScope::Session)
            .unwrap();
        session.ownership.next_witness_id = u64::MAX;
        let before = session.ownership.clone();
        assert!(matches!(
            session.issue_readiness_witness(&owner, "ready"),
            Err(OwnershipError::CounterExhausted { .. })
        ));
        assert_eq!(before, session.ownership);
        assert!(matches!(
            session.mark_owner_died(0, "owner"),
            Err(OwnershipError::CounterExhausted { .. })
        ));
        assert_eq!(SessionStatus::Active, session.status);
        assert_eq!(before, session.ownership);
        assert!(matches!(
            session.cancel_abandoned_transfer(&receipt),
            Err(OwnershipError::CounterExhausted { .. })
        ));
        assert_eq!(SessionStatus::Active, session.status);
        assert_eq!(before, session.ownership);
        session.rollback_ownership_transfer(&receipt).unwrap();
        session
            .apply_owned_session_mutation(
                &owner,
                SessionHostMutation::SetDefaultHandler {
                    handler: "still-owned".into(),
                },
            )
            .unwrap();
    }

    #[wasm_bindgen_test::wasm_bindgen_test(unsupported = test)]
    fn ownership_host_mutation_rejects_foreign_session_edges() {
        let (mut session, owner) = owned_session();
        let foreign = Edge::new(1, "A", "B");
        for mutation in [
            SessionHostMutation::UpdateEdgeHandler {
                edge: foreign.clone(),
                handler: "foreign".into(),
            },
            SessionHostMutation::UpdateTrace {
                edge: foreign.clone(),
                trace: vec![ValType::Nat],
            },
        ] {
            assert!(matches!(
                session.apply_owned_session_mutation(&owner, mutation),
                Err(OwnershipError::SessionMismatch { .. })
            ));
            assert!(!session.edge_handlers.contains_key(&foreign));
            assert!(!session.edge_traces.contains_key(&foreign));
        }
    }
}
