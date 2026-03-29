impl ThreadedProtocolMachine {
    /// Export the concrete runtime slice used for exact refinement checks.
    ///
    /// # Panics
    ///
    /// Panics if an internal threaded ProtocolMachine lock is poisoned.
    ///
    /// # Errors
    ///
    /// Returns an error when the exported counts do not fit the bridge-safe `u64` schema.
    pub fn refinement_slice(
        &self,
    ) -> Result<ProtocolMachineRefinementSlice, RefinementSliceError> {
        let coroutines = self.refinement_coroutines()?;
        let sessions = self.refinement_sessions()?;
        let scheduler = self.refinement_scheduler()?;
        Ok(ProtocolMachineRefinementSlice {
            coroutines,
            sessions,
            scheduler,
        })
    }

    fn refinement_coroutines(
        &self,
    ) -> Result<Vec<crate::refinement::CoroutineRefinementSlice>, RefinementSliceError> {
        self.coroutines
            .iter()
            .map(|coro| {
                let guard = coro.lock().expect("threaded ProtocolMachine lock poisoned");
                Ok::<_, RefinementSliceError>(crate::refinement::CoroutineRefinementSlice {
                    coro_id: u64::try_from(guard.id).map_err(|_| {
                        RefinementSliceError::CountOverflow {
                            field: "coroutine.id",
                            value: guard.id,
                        }
                    })?,
                    session_id: u64::try_from(guard.session_id).map_err(|_| {
                        RefinementSliceError::CountOverflow {
                            field: "coroutine.session_id",
                            value: guard.session_id,
                        }
                    })?,
                    pc: u64::try_from(guard.pc).map_err(|_| RefinementSliceError::CountOverflow {
                        field: "coroutine.pc",
                        value: guard.pc,
                    })?,
                    status: coro_status_tag(&guard.status).to_string(),
                    owned_endpoints: u64::try_from(guard.owned_endpoints.len()).map_err(|_| {
                        RefinementSliceError::CountOverflow {
                            field: "coroutine.owned_endpoints",
                            value: guard.owned_endpoints.len(),
                        }
                    })?,
                    progress_tokens: u64::try_from(guard.progress_tokens.len()).map_err(|_| {
                        RefinementSliceError::CountOverflow {
                            field: "coroutine.progress_tokens",
                            value: guard.progress_tokens.len(),
                        }
                    })?,
                })
            })
            .collect()
    }

    fn refinement_sessions(&self) -> Result<Vec<SessionRefinementSlice>, RefinementSliceError> {
        self.sessions
            .sessions
            .read()
            .expect("threaded ProtocolMachine lock poisoned")
            .values()
            .map(|session| {
                let guard = session.lock().expect("threaded ProtocolMachine lock poisoned");
                let buffered_messages =
                    guard.buffers.values().try_fold(0_u64, |acc, buffer| {
                        Ok::<_, RefinementSliceError>(
                            acc + u64::try_from(buffer.len()).map_err(|_| {
                                RefinementSliceError::CountOverflow {
                                    field: "session.buffered_messages",
                                    value: buffer.len(),
                                }
                            })?,
                        )
                    })?;
                Ok::<_, RefinementSliceError>(SessionRefinementSlice {
                    sid: u64::try_from(guard.sid).map_err(|_| RefinementSliceError::CountOverflow {
                        field: "session.sid",
                        value: guard.sid,
                    })?,
                    role_count: u64::try_from(guard.roles.len()).map_err(|_| {
                        RefinementSliceError::CountOverflow {
                            field: "session.role_count",
                            value: guard.roles.len(),
                        }
                    })?,
                    local_type_entries: u64::try_from(guard.local_types.len()).map_err(|_| {
                        RefinementSliceError::CountOverflow {
                            field: "session.local_type_entries",
                            value: guard.local_types.len(),
                        }
                    })?,
                    buffer_edges: u64::try_from(guard.buffers.len()).map_err(|_| {
                        RefinementSliceError::CountOverflow {
                            field: "session.buffer_edges",
                            value: guard.buffers.len(),
                        }
                    })?,
                    buffered_messages,
                    status: crate::refinement::session_status_tag(&guard.status).to_string(),
                    epoch: u64::try_from(guard.epoch).map_err(|_| {
                        RefinementSliceError::CountOverflow {
                            field: "session.epoch",
                            value: guard.epoch,
                        }
                    })?,
                })
            })
            .collect()
    }

    fn refinement_scheduler(&self) -> Result<SchedulerRefinementSlice, RefinementSliceError> {
        let ready_queue = self
            .scheduler
            .ready_snapshot()
            .into_iter()
            .map(|id| {
                u64::try_from(id).map_err(|_| RefinementSliceError::CountOverflow {
                    field: "scheduler.ready_queue",
                    value: id,
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        let blocked = self
            .scheduler
            .blocked_snapshot()
            .into_iter()
            .map(|(id, reason)| {
                Ok::<_, RefinementSliceError>((
                    u64::try_from(id).map_err(|_| RefinementSliceError::CountOverflow {
                        field: "scheduler.blocked",
                        value: id,
                    })?,
                    block_reason_tag(&reason).to_string(),
                ))
            })
            .collect::<Result<std::collections::BTreeMap<_, _>, _>>()?;
        let step_count = self.scheduler.step_count();
        Ok(SchedulerRefinementSlice {
            ready_queue,
            blocked,
            step_count: u64::try_from(step_count).map_err(|_| {
                RefinementSliceError::CountOverflow {
                    field: "scheduler.step_count",
                    value: step_count,
                }
            })?,
        })
    }

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

    /// Get canonical progress contracts tracked as runtime state.
    #[must_use]
    pub fn progress_contracts(&self) -> &[crate::semantic_objects::ProgressContract] {
        &self.progress_contracts
    }

    /// Get replay-visible progress transitions tracked as runtime state.
    #[must_use]
    pub fn progress_transitions(&self) -> &[crate::semantic_objects::ProgressTransition] {
        &self.progress_transitions
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
            &self.progress_contracts,
            &self.progress_transitions,
        )
    }

    /// Get canonical semantic objects derived from handoff, effect, and
    /// output-condition surfaces.
    #[must_use]
    pub fn semantic_objects(&self) -> ProtocolMachineSemanticObjects {
        protocol_machine_semantic_objects(
            &[],
            &self.delegation_audit_log,
            &self.operation_instances,
            &self.outstanding_effects,
            &self.output_condition_checks,
            &self.progress_contracts,
            &self.progress_transitions,
        )
    }

    /// Get canonical semantic publication events.
    #[must_use]
    pub fn publication_events(&self) -> Vec<crate::semantic_objects::PublicationEvent> {
        self.semantic_objects().publication_events
    }

    /// Get canonical prestate bindings.
    #[must_use]
    pub fn prestate_bindings(&self) -> Vec<crate::semantic_objects::PrestateBinding> {
        self.semantic_objects().prestate_bindings
    }

    /// Get canonical named agreement profiles.
    #[must_use]
    pub fn agreement_profiles(&self) -> Vec<crate::semantic_objects::AgreementProfile> {
        self.semantic_objects().agreement_profiles
    }

    /// Get canonical agreement contracts.
    #[must_use]
    pub fn agreement_contracts(&self) -> Vec<crate::semantic_objects::AgreementContract> {
        self.semantic_objects().agreement_contracts
    }

    /// Get canonical agreement evidence objects.
    #[must_use]
    pub fn agreement_evidence(&self) -> Vec<crate::semantic_objects::AgreementEvidence> {
        self.semantic_objects().agreement_evidence
    }

    /// Get canonical agreement states.
    #[must_use]
    pub fn agreement_states(&self) -> Vec<crate::semantic_objects::AgreementState> {
        self.semantic_objects().agreement_states
    }

    /// Require that one semantic-path read be authoritative.
    ///
    /// # Errors
    ///
    /// Returns a contract violation when the requested read is observational or unknown.
    pub fn require_authoritative_read(
        &self,
        read_id: &str,
    ) -> Result<crate::semantic_objects::AuthoritativeRead, ProtocolMachineError> {
        self.semantic_objects()
            .require_authoritative_read(read_id)
            .cloned()
            .map_err(|message| ProtocolMachineError::HandlerError(crate::effect::EffectFailure::contract_violation(message)))
    }

    /// Require that one parity-critical path use a canonical handle.
    ///
    /// # Errors
    ///
    /// Returns a contract violation when the requested handle is missing.
    pub fn require_canonical_handle(
        &self,
        handle_id: &str,
    ) -> Result<crate::semantic_objects::CanonicalHandle, ProtocolMachineError> {
        self.semantic_objects()
            .require_canonical_handle(handle_id)
            .cloned()
            .map_err(|message| ProtocolMachineError::HandlerError(crate::effect::EffectFailure::contract_violation(message)))
    }

    /// Deterministic communication replay-state root.
    ///
    /// # Panics
    ///
    /// Panics if an internal threaded ProtocolMachine lock is poisoned.
    ///
    #[must_use]
    pub fn communication_replay_root(&self) -> crate::verification::Hash {
        self.communication_consumption
            .lock()
            .expect("threaded ProtocolMachine lock poisoned")
            .root()
    }

    /// Receive-boundary replay-consumption artifacts.
    ///
    /// # Panics
    ///
    /// Panics if an internal threaded ProtocolMachine lock is poisoned.
    ///
    #[must_use]
    pub fn communication_consumption_artifacts(&self) -> Vec<CommunicationConsumptionArtifact> {
        self.communication_consumption_artifacts
            .lock()
            .expect("threaded ProtocolMachine lock poisoned")
            .clone()
    }

    /// Canonical replay/state fragment for deterministic diffing and snapshots.
    ///
    /// # Panics
    ///
    /// Panics if an internal threaded ProtocolMachine lock is poisoned.
    ///
    #[must_use]
    pub fn canonical_replay_fragment(&self) -> CanonicalReplayFragmentV1 {
        let communication_replay_root = self
            .communication_consumption
            .lock()
            .expect("threaded ProtocolMachine lock poisoned")
            .root();
        let communication_consumption_artifacts = self
            .communication_consumption_artifacts
            .lock()
            .expect("threaded ProtocolMachine lock poisoned")
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
            &self.progress_contracts,
            &self.progress_transitions,
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
