impl ThreadedVM {
    /// Get the observable trace.
    #[must_use]
    pub fn trace(&self) -> &[ObsEvent] {
        &self.trace
    }

    /// Get recorded effect-trace entries.
    #[must_use]
    pub fn effect_trace(&self) -> &[EffectTraceEntry] {
        &self.effect_trace
    }

    /// Get canonical typed effect request/outcome exchanges.
    #[must_use]
    pub fn effect_exchanges(&self) -> &[EffectExchangeRecord] {
        &self.effect_exchanges
    }

    /// Get canonical operation instances tracked as runtime state.
    #[must_use]
    pub fn operation_instances(&self) -> &[OperationInstance] {
        &self.operation_instances
    }

    /// Get canonical outstanding effects tracked as runtime state.
    #[must_use]
    pub fn outstanding_effects(&self) -> &[OutstandingEffect] {
        &self.outstanding_effects
    }

    /// Get recorded delegation audit records.
    #[must_use]
    pub fn delegation_audit_log(&self) -> &[DelegationAuditRecord] {
        &self.delegation_audit_log
    }

    /// Get canonical semantic audit records derived from delegation,
    /// failure-visible events, and effect/interface traces.
    #[must_use]
    pub fn semantic_audit_log(&self) -> Vec<SemanticAuditRecord> {
        semantic_audit_log_v1(
            &[],
            &self.delegation_audit_log,
            &self.operation_instances,
            &self.trace,
            &self.outstanding_effects,
        )
    }

    /// Get canonical semantic objects derived from handoff, effect, and
    /// output-condition surfaces.
    #[must_use]
    pub fn semantic_objects(&self) -> ProtocolMachineSemanticObjects {
        protocol_machine_semantic_objects_v1(
            &[],
            &self.delegation_audit_log,
            &self.operation_instances,
            &self.outstanding_effects,
            &self.output_condition_checks,
        )
    }

    /// Get canonical semantic publication events.
    #[must_use]
    pub fn publication_events(&self) -> Vec<crate::semantic_objects::PublicationEvent> {
        self.semantic_objects().publication_events
    }

    /// Require that one semantic-path read be authoritative.
    ///
    /// # Errors
    ///
    /// Returns a contract violation when the requested read is observational or unknown.
    pub fn require_authoritative_read(
        &self,
        read_id: &str,
    ) -> Result<crate::semantic_objects::AuthoritativeRead, VMError> {
        self.semantic_objects()
            .require_authoritative_read(read_id)
            .cloned()
            .map_err(|message| VMError::HandlerError(crate::effect::EffectFailure::contract_violation(message)))
    }

    /// Require that one parity-critical path use a canonical handle.
    ///
    /// # Errors
    ///
    /// Returns a contract violation when the requested handle is missing.
    pub fn require_canonical_handle(
        &self,
        handle_id: &str,
    ) -> Result<crate::semantic_objects::CanonicalHandle, VMError> {
        self.semantic_objects()
            .require_canonical_handle(handle_id)
            .cloned()
            .map_err(|message| VMError::HandlerError(crate::effect::EffectFailure::contract_violation(message)))
    }

    /// Deterministic communication replay-state root.
    ///
    /// # Panics
    ///
    /// Panics if an internal threaded VM lock is poisoned.
    ///
    #[must_use]
    pub fn communication_replay_root(&self) -> crate::verification::Hash {
        self.communication_consumption
            .lock()
            .expect("threaded VM lock poisoned")
            .root()
    }

    /// Receive-boundary replay-consumption artifacts.
    ///
    /// # Panics
    ///
    /// Panics if an internal threaded VM lock is poisoned.
    ///
    #[must_use]
    pub fn communication_consumption_artifacts(&self) -> Vec<CommunicationConsumptionArtifact> {
        self.communication_consumption_artifacts
            .lock()
            .expect("threaded VM lock poisoned")
            .clone()
    }

    /// Canonical replay/state fragment for deterministic diffing and snapshots.
    ///
    /// # Panics
    ///
    /// Panics if an internal threaded VM lock is poisoned.
    ///
    #[must_use]
    pub fn canonical_replay_fragment(&self) -> CanonicalReplayFragmentV1 {
        let communication_replay_root = self
            .communication_consumption
            .lock()
            .expect("threaded VM lock poisoned")
            .root();
        let communication_consumption_artifacts = self
            .communication_consumption_artifacts
            .lock()
            .expect("threaded VM lock poisoned")
            .clone();
        let corrupted_edges = self
            .corrupted_edges
            .iter()
            .map(|(edge, corruption)| (edge.clone(), *corruption))
            .collect();
        let timed_out_sites = self
            .timed_out_sites
            .iter()
            .map(|(site, until_tick)| (site.clone(), *until_tick))
            .collect();
        canonical_replay_fragment_v1(
            &self.trace,
            &self.effect_trace,
            &[],
            &self.delegation_audit_log,
            &self.operation_instances,
            &self.outstanding_effects,
            &self.output_condition_checks,
            self.crashed_sites.iter().cloned().collect(),
            self.partitioned_edges.iter().cloned().collect(),
            corrupted_edges,
            timed_out_sites,
            self.config.effect_determinism_tier,
            self.config.communication_replay_mode,
            Some(communication_replay_root),
            communication_consumption_artifacts,
        )
    }

    /// Get recorded output-condition verification checks.
    #[must_use]
    pub fn output_condition_checks(&self) -> &[OutputConditionCheck] {
        &self.output_condition_checks
    }

    /// Crashed sites currently active in topology state.
    #[must_use]
    pub fn crashed_sites(&self) -> &BTreeSet<String> {
        &self.crashed_sites
    }
}
