// Both backends delegate ownership transitions to SessionState.
impl crate::owned::OwnedSessionMachine for ThreadedProtocolMachine {
    fn inject_owned_message_with_sequence(
        &mut self,
        owner: &OwnedSession,
        from: &str,
        to: &str,
        value: Value,
        sequence_no: u64,
    ) -> Result<EnqueueResult, crate::owned::OwnedSessionEnqueueError> {
        self.sessions
            .with_owned_session_at(owner.session_id(), Some(self.clock.tick), |session| {
                session.send_owned_with_sequence(owner.capability(), from, to, value, sequence_no)
            })
            .map_err(crate::owned::OwnedSessionEnqueueError::Ownership)?
            .map_err(|message| crate::owned::OwnedSessionEnqueueError::Enqueue { message })
    }

    fn validate_owned_operation(&mut self, owner: &OwnedSession) -> Result<(), OwnershipError> {
        let capability = owner.capability();
        self.sessions.with_owned_session_at(
            capability.session_id,
            Some(self.clock.tick),
            |session| SessionState::validate_mutating_owner(session, capability),
        )
    }

    fn apply_owned_session_mutation(
        &mut self,
        owner: &OwnedSession,
        mutation: SessionHostMutation,
    ) -> Result<(), OwnershipError> {
        let capability = owner.capability();
        self.sessions.with_owned_session_at(
            capability.session_id,
            Some(self.clock.tick),
            |session| session.apply_owned_session_mutation(capability, mutation),
        )
    }

    fn issue_readiness_witness(
        &mut self,
        owner: &OwnedSession,
        predicate_ref: impl Into<String>,
    ) -> Result<ReadinessWitness, OwnershipError> {
        let capability = owner.capability();
        self.sessions.with_owned_session_at(
            capability.session_id,
            Some(self.clock.tick),
            |session| session.issue_readiness_witness(capability, predicate_ref),
        )
    }

    fn consume_readiness_witness(
        &mut self,
        owner: &OwnedSession,
        witness: &ReadinessWitness,
    ) -> Result<(), OwnershipError> {
        let capability = owner.capability();
        self.sessions.with_owned_session_at(
            capability.session_id,
            Some(self.clock.tick),
            |session| session.consume_readiness_witness(capability, witness),
        )
    }

    fn begin_ownership_transfer(
        &mut self,
        owner: &OwnedSession,
        new_owner_id: impl Into<String>,
        new_scope: OwnershipScope,
    ) -> Result<OwnershipReceipt, OwnershipError> {
        let capability = owner.capability();
        self.sessions.with_owned_session_at(
            capability.session_id,
            Some(self.clock.tick),
            |session| session.begin_ownership_transfer(capability, new_owner_id, new_scope),
        )
    }

    fn commit_ownership_transfer(
        &mut self,
        owner: &OwnedSession,
        receipt: &OwnershipReceipt,
    ) -> Result<OwnershipCapability, OwnershipError> {
        self.validate_owned_operation(owner)?;
        owner.require_receipt_session(receipt)?;
        self.sessions
            .with_owned_session_at(receipt.session_id, Some(self.clock.tick), |session| {
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
        self.sessions
            .with_owned_session_at(receipt.session_id, Some(self.clock.tick), |session| {
                session.rollback_ownership_transfer(receipt)
            })
    }

    fn attenuate_ownership_scope(
        &mut self,
        owner: &OwnedSession,
        new_scope: OwnershipScope,
    ) -> Result<OwnershipCapability, OwnershipError> {
        let capability = owner.capability();
        self.sessions.with_owned_session_at(
            capability.session_id,
            Some(self.clock.tick),
            |session| session.attenuate_ownership_scope(capability, new_scope),
        )
    }

    fn release_ownership(&mut self, owner: &OwnedSession) -> Result<(), OwnershipError> {
        let capability = owner.capability();
        self.sessions.with_owned_session_at(
            capability.session_id,
            Some(self.clock.tick),
            |session| session.release_ownership(capability),
        )
    }
    fn owned_mark_owner_died(
        &mut self,
        owner: &OwnedSession,
    ) -> Result<CancellationWitness, OwnershipError> {
        self.validate_owned_operation(owner)?;
        let sid = owner.session_id();
        let owner_id = owner.capability().owner_id.as_str();
        let witness =
            self.sessions
                .with_owned_session_at(sid, Some(self.clock.tick), |session| {
                    session.mark_owner_died(sid, owner_id)
                })?;
        self.invalidate_outstanding_effects_for_session(
            sid,
            &format!("ownership owner `{owner_id}` died"),
        );
        self.trace.push(ObsEvent::SessionTerminal {
            tick: self.clock.tick,
            session: sid,
            reason: crate::engine::SessionTerminalReason::Faulted {
                reason: format!("ownership owner `{owner_id}` died"),
            },
        });
        Ok(witness)
    }
    fn owned_cancel_abandoned_transfer(
        &mut self,
        owner: &OwnedSession,
        receipt: &OwnershipReceipt,
    ) -> Result<CancellationWitness, OwnershipError> {
        self.validate_owned_operation(owner)?;
        owner.require_receipt_session(receipt)?;
        let requested_reason = crate::OwnershipTerminalReason::TransferAbandoned {
            owner_id: receipt.from_owner_id.clone(),
            claim_id: receipt.claim_id,
        };
        let witness = self.sessions.with_owned_session_at(
            receipt.session_id,
            Some(self.clock.tick),
            |session| session.cancel_abandoned_transfer(receipt),
        )?;
        self.invalidate_outstanding_effects_for_session(
            receipt.session_id,
            "ownership transfer abandoned",
        );
        self.trace.push(ObsEvent::CancellationRequested {
            tick: self.clock.tick,
            session: receipt.session_id,
            witness_id: witness.witness_id,
            owner_id: receipt.from_owner_id.clone(),
            reason: requested_reason.clone(),
        });
        self.trace.push(ObsEvent::Cancelled {
            tick: self.clock.tick,
            session: receipt.session_id,
            witness_id: witness.witness_id,
            reason: requested_reason.clone(),
        });
        self.trace.push(ObsEvent::SessionTerminal {
            tick: self.clock.tick,
            session: receipt.session_id,
            reason: crate::engine::SessionTerminalReason::Cancelled {
                reason: format!(
                    "ownership transfer {} abandoned by {}",
                    receipt.claim_id, receipt.from_owner_id
                ),
            },
        });
        Ok(witness)
    }
    fn owned_fault_failed_transfer_commit(
        &mut self,
        owner: &OwnedSession,
        receipt: &OwnershipReceipt,
        reason: impl Into<String>,
    ) -> Result<(), OwnershipError> {
        self.validate_owned_operation(owner)?;
        owner.require_receipt_session(receipt)?;
        let reason = reason.into();
        self.sessions.with_owned_session_at(
            receipt.session_id,
            Some(self.clock.tick),
            |session| session.fault_failed_transfer_commit(receipt, reason.clone()),
        )?;
        self.invalidate_outstanding_effects_for_session(receipt.session_id, &reason);
        self.trace.push(ObsEvent::SessionTerminal {
            tick: self.clock.tick,
            session: receipt.session_id,
            reason: crate::engine::SessionTerminalReason::Faulted {
                reason: format!("ownership transfer commit failed: {reason}"),
            },
        });
        Ok(())
    }
}

#[cfg(all(test, not(target_arch = "wasm32")))]
mod ownership_lock_tests {
    use super::*;

    #[test]
    fn ownership_poisoned_session_refuses_mutation_without_replacement() {
        let image = CodeImage {
            programs: BTreeMap::from([("A".into(), vec![Instr::Halt])]),
            global_type: telltale_types::GlobalType::End,
            local_types: BTreeMap::from([("A".into(), LocalTypeR::End)]),
        };
        let mut machine =
            ThreadedProtocolMachine::with_workers(ProtocolMachineConfig::default(), 1);
        let owner = machine.load_choreography_owned(&image, "original").unwrap();
        let original = machine.sessions.get(owner.session_id()).unwrap();
        let poisoned = Arc::clone(&original);
        let joined = std::thread::spawn(move || {
            let _guard = poisoned.lock().unwrap();
            panic!("poison the actual original session custody lock");
        })
        .join();
        let mutation = owner.apply_host_mutation(
            &mut machine,
            SessionHostMutation::SetDefaultHandler {
                handler: "never-applied".into(),
            },
        );
        let ingress = owner.inject_message_with_sequence(&mut machine, "A", "B", Value::Unit, 0);
        let retained = machine.sessions.get(owner.session_id()).unwrap();
        let unchanged =
            original.lock().unwrap_err().into_inner().default_handler != "never-applied";
        let workers = machine
            .shutdown_worker_pool()
            .expect("same actual original pool joined")
            .joined_workers();
        assert_eq!(workers, 1);
        assert!(joined.is_err());
        assert!(
            matches!(mutation, Err(OwnershipError::LockPoisoned { session_id }) if session_id == owner.session_id())
        );
        assert!(
            matches!(ingress, Err(crate::owned::OwnedSessionEnqueueError::Ownership(OwnershipError::LockPoisoned { session_id })) if session_id == owner.session_id())
        );
        assert!(Arc::ptr_eq(&original, &retained));
        assert!(unchanged);
    }
    #[test]
    fn ownership_poisoned_audit_refuses_transition_before_state_mutation() {
        let image = CodeImage {
            programs: BTreeMap::from([("A".into(), vec![Instr::Halt])]),
            global_type: telltale_types::GlobalType::End,
            local_types: BTreeMap::from([("A".into(), LocalTypeR::End)]),
        };
        let mut machine =
            ThreadedProtocolMachine::with_workers(ProtocolMachineConfig::default(), 1);
        let owner = machine.load_choreography_owned(&image, "original").unwrap();
        let original = machine.sessions.get(owner.session_id()).unwrap();
        let before = original.lock().unwrap().ownership().clone();
        let journal = &machine.sessions.authority_audit_log;
        let joined = std::thread::scope(|scope| {
            scope
                .spawn(move || {
                    let _guard = journal.lock().unwrap();
                    panic!("poison the actual canonical authority journal");
                })
                .join()
        });
        let transfer = owner.begin_transfer(&mut machine, "next", OwnershipScope::Session);
        let ingress = owner.inject_message_with_sequence(&mut machine, "A", "B", Value::Unit, 0);
        let retained = machine.sessions.get(owner.session_id()).unwrap();
        let after = original.lock().unwrap().ownership().clone();
        let workers = machine
            .shutdown_worker_pool()
            .expect("same actual original pool joined")
            .joined_workers();
        assert_eq!(workers, 1);
        assert!(joined.is_err());
        assert!(
            matches!(transfer, Err(OwnershipError::LockPoisoned { session_id }) if session_id == owner.session_id())
        );
        assert!(
            matches!(ingress, Err(crate::owned::OwnedSessionEnqueueError::Ownership(OwnershipError::LockPoisoned { session_id })) if session_id == owner.session_id())
        );
        assert!(Arc::ptr_eq(&original, &retained));
        assert_eq!(before, after);
    }
}
