impl VM {
    fn combined_authority_audit_log(&self) -> Vec<AuthorityAuditRecord> {
        let mut out = self.authority_audit_log.as_slice().to_vec();
        for sid in self.sessions.session_ids() {
            if let Some(records) = self.sessions.authority_audit_log(sid) {
                out.extend_from_slice(records);
            }
        }
        out.sort_by(|lhs, rhs| {
            let lhs_key = (
                lhs.tick.unwrap_or(0),
                serde_json::to_string(lhs).unwrap_or_default(),
            );
            let rhs_key = (
                rhs.tick.unwrap_or(0),
                serde_json::to_string(rhs).unwrap_or_default(),
            );
            lhs_key.cmp(&rhs_key)
        });
        out.dedup_by(|lhs, rhs| lhs == rhs);
        out
    }

/// Approximate retained state for the VM runtime.
    #[must_use]
    pub fn memory_usage(&self) -> VmMemoryUsage {
        let session_store = self.sessions.memory_usage();
        let retained_bytes = self.retained_bytes(session_store.retained_bytes.total);
        VmMemoryUsage {
            session_store,
            coroutine_records: self.coroutines.len(),
            terminal_coroutines: self.coroutines.iter().filter(|coro| coro.is_terminal()).count(),
            program_count: self.programs.len(),
            program_instruction_count: self.programs.instruction_count(),
            obs_events: self.obs_trace.len(),
            effect_trace_entries: self.effect_trace.len(),
            communication_artifacts: self.communication_consumption_artifacts.len(),
            output_condition_checks: self.output_condition_checks.len(),
            delegation_audits: self.delegation_audit_log.len(),
            authority_audits: self.authority_audit_log.len(),
            retained_bytes,
        }
    }

    fn retained_bytes(&self, session_store_bytes: usize) -> VmRetainedBytes {
        let mut retained_bytes = VmRetainedBytes {
            session_store: session_store_bytes,
            coroutines: self.coroutines.iter().map(vm_serialized_bytes).sum(),
            programs: vm_serialized_bytes(&self.programs)
                .saturating_add(vm_serialized_bytes(&self.code)),
            resource_states: vm_serialized_bytes(&self.resource_states),
            traces: vm_serialized_bytes(&self.obs_trace)
                .saturating_add(vm_serialized_bytes(&self.effect_trace))
                .saturating_add(vm_serialized_bytes(&self.delegation_audit_log))
                .saturating_add(vm_serialized_bytes(&self.authority_audit_log)),
            replay: vm_serialized_bytes(&self.communication_consumption)
                .saturating_add(vm_serialized_bytes(&self.communication_consumption_artifacts)),
            output_condition_checks: vm_serialized_bytes(&self.output_condition_checks),
            scheduler_and_control: vm_serialized_bytes(&self.sched)
                .saturating_add(vm_serialized_bytes(&self.eligible_ready))
                .saturating_add(vm_serialized_bytes(&self.paused_roles))
                .saturating_add(vm_serialized_bytes(&self.crashed_sites))
                .saturating_add(vm_serialized_bytes(&self.partitioned_edges))
                .saturating_add(vm_serialized_bytes(&self.corrupted_edges))
                .saturating_add(vm_serialized_bytes(&self.timed_out_sites))
                .saturating_add(vm_serialized_bytes(&self.clock))
                .saturating_add(vm_serialized_bytes(&self.last_sched_step))
                .saturating_add(vm_serialized_bytes(&self.handler_identity_anchor))
                .saturating_add(vm_serialized_bytes(&self.next_coro_id))
                .saturating_add(vm_serialized_bytes(&self.next_session_id)),
            symbols: vm_serialized_bytes(&self.role_symbols)
                .saturating_add(vm_serialized_bytes(&self.label_symbols))
                .saturating_add(vm_serialized_bytes(&self.handler_symbols))
                .saturating_add(vm_serialized_bytes(&self.edge_symbols)),
            guard_layer: vm_serialized_bytes(&self.guard_layer),
            monitor: vm_serialized_bytes(&self.monitor),
            arena: vm_serialized_bytes(&self.arena),
            total: 0,
        };
        retained_bytes.total = Self::retained_bytes_total(&retained_bytes);
        retained_bytes
    }

    fn retained_bytes_total(retained_bytes: &VmRetainedBytes) -> usize {
        retained_bytes
            .session_store
            .saturating_add(retained_bytes.coroutines)
            .saturating_add(retained_bytes.programs)
            .saturating_add(retained_bytes.resource_states)
            .saturating_add(retained_bytes.traces)
            .saturating_add(retained_bytes.replay)
            .saturating_add(retained_bytes.output_condition_checks)
            .saturating_add(retained_bytes.scheduler_and_control)
            .saturating_add(retained_bytes.symbols)
            .saturating_add(retained_bytes.guard_layer)
            .saturating_add(retained_bytes.monitor)
            .saturating_add(retained_bytes.arena)
    }

    /// Get recorded output-condition verification checks.
    #[must_use]
    pub fn output_condition_checks(&self) -> &[OutputConditionCheck] {
        self.output_condition_checks.as_slice()
    }

    /// Get recorded effect-trace entries.
    #[must_use]
    pub fn effect_trace(&self) -> &[EffectTraceEntry] {
        self.effect_trace.as_slice()
    }

    /// Get canonical typed effect request/outcome exchanges.
    #[must_use]
    pub fn effect_exchanges(&self) -> &[EffectExchangeRecord] {
        self.effect_exchanges.as_slice()
    }

    /// Get canonical operation instances tracked as runtime state.
    #[must_use]
    pub fn operation_instances(&self) -> &[OperationInstance] {
        self.operation_instances.as_slice()
    }

    /// Get canonical outstanding effects tracked as runtime state.
    #[must_use]
    pub fn outstanding_effects(&self) -> &[OutstandingEffect] {
        self.outstanding_effects.as_slice()
    }

    /// Get recorded delegation audit records.
    #[must_use]
    pub fn delegation_audit_log(&self) -> &[DelegationAuditRecord] {
        self.delegation_audit_log.as_slice()
    }

    /// Get recorded authority witness audit records.
    #[must_use]
    pub fn authority_audit_log(&self) -> &[AuthorityAuditRecord] {
        self.authority_audit_log.as_slice()
    }

    /// Get canonical semantic audit records derived from authority, delegation,
    /// failure, and effect/interface traces.
    #[must_use]
    pub fn semantic_audit_log(&self) -> Vec<SemanticAuditRecord> {
        let authority_audit_log = self.combined_authority_audit_log();
        semantic_audit_log_v1(
            authority_audit_log.as_slice(),
            self.delegation_audit_log.as_slice(),
            self.operation_instances.as_slice(),
            self.obs_trace.as_slice(),
            self.outstanding_effects.as_slice(),
        )
    }

    /// Get canonical semantic objects derived from authority, handoff, effect,
    /// and output-condition surfaces.
    #[must_use]
    pub fn semantic_objects(&self) -> ProtocolMachineSemanticObjects {
        let authority_audit_log = self.combined_authority_audit_log();
        protocol_machine_semantic_objects_v1(
            authority_audit_log.as_slice(),
            self.delegation_audit_log.as_slice(),
            self.operation_instances.as_slice(),
            self.outstanding_effects.as_slice(),
            self.output_condition_checks.as_slice(),
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
    #[must_use]
    pub fn communication_replay_root(&self) -> crate::verification::Hash {
        self.communication_consumption.root()
    }

    /// Receive-boundary replay-consumption artifacts.
    #[must_use]
    pub fn communication_consumption_artifacts(&self) -> &[CommunicationConsumptionArtifact] {
        self.communication_consumption_artifacts.as_slice()
    }

    /// Drain retained observable events in canonical insertion order.
    pub fn drain_obs_trace(&mut self) -> Vec<ObsEvent> {
        self.obs_trace.drain()
    }

    /// Drain retained effect-trace entries in canonical insertion order.
    pub fn drain_effect_trace(&mut self) -> Vec<EffectTraceEntry> {
        self.effect_trace.drain()
    }

    /// Drain retained output-condition diagnostics in canonical insertion order.
    pub fn drain_output_condition_checks(&mut self) -> Vec<OutputConditionCheck> {
        self.output_condition_checks.drain()
    }

    /// Drain retained delegation audit records in canonical insertion order.
    pub fn drain_delegation_audit_log(&mut self) -> Vec<DelegationAuditRecord> {
        self.delegation_audit_log.drain()
    }

    /// Drain retained authority witness audit records in canonical insertion order.
    pub fn drain_authority_audit_log(&mut self) -> Vec<AuthorityAuditRecord> {
        self.authority_audit_log.drain()
    }

    /// Drain retained communication replay-consumption artifacts in canonical insertion order.
    pub fn drain_communication_consumption_artifacts(
        &mut self,
    ) -> Vec<CommunicationConsumptionArtifact> {
        self.communication_consumption_artifacts.drain()
    }

    /// Canonical replay/state fragment for deterministic diffing and snapshots.
    #[must_use]
    pub fn canonical_replay_fragment(&self) -> CanonicalReplayFragmentV1 {
        let authority_audit_log = self.combined_authority_audit_log();
        let partitioned_edges = self.partitioned_edges.iter().cloned().collect();
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
            self.obs_trace.as_slice(),
            self.effect_trace.as_slice(),
            authority_audit_log.as_slice(),
            self.delegation_audit_log.as_slice(),
            self.operation_instances.as_slice(),
            self.outstanding_effects.as_slice(),
            self.output_condition_checks.as_slice(),
            self.crashed_sites.iter().cloned().collect(),
            partitioned_edges,
            corrupted_edges,
            timed_out_sites,
            self.config.effect_determinism_tier,
            self.config.communication_replay_mode,
            Some(self.communication_consumption.root()),
            self.communication_consumption_artifacts.as_slice().to_vec(),
        )
    }

    /// Crashed sites currently active in topology state.
    #[must_use]
    pub fn crashed_sites(&self) -> &BTreeSet<SiteId> {
        &self.crashed_sites
    }

    /// Partitioned site-links currently active in topology state.
    #[must_use]
    pub fn partitioned_edges(&self) -> &BTreeSet<(SiteId, SiteId)> {
        &self.partitioned_edges
    }

    /// Corrupted directed edges currently active in topology state.
    #[must_use]
    pub fn corrupted_edges(&self) -> &BTreeMap<(SiteId, SiteId), CorruptionType> {
        &self.corrupted_edges
    }

    /// Active site timeouts.
    #[must_use]
    pub fn timed_out_sites(&self) -> &BTreeMap<SiteId, u64> {
        &self.timed_out_sites
    }
}
