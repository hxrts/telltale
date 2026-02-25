impl VM {
    /// Access the simulation clock.
    #[must_use]
    pub fn clock(&self) -> &SimClock {
        &self.clock
    }

    /// Whether all coroutines are terminal (done or faulted).
    #[must_use]
    pub fn all_done(&self) -> bool {
        self.coroutines.iter().all(|c| c.is_terminal())
    }

    /// Get a coroutine by ID.
    #[must_use]
    pub fn coroutine(&self, id: usize) -> Option<&Coroutine> {
        self.coroutines.iter().find(|c| c.id == id)
    }

    /// Program length for a coroutine by id.
    #[must_use]
    pub fn coroutine_program_len(&self, id: usize) -> Option<usize> {
        let coro = self.coroutine(id)?;
        self.programs.get(coro.program_id).map(std::vec::Vec::len)
    }

    /// Get a mutable coroutine by ID.
    pub fn coroutine_mut(&mut self, id: usize) -> Option<&mut Coroutine> {
        self.coroutines.iter_mut().find(|c| c.id == id)
    }

    /// Get all coroutines for a session.
    #[must_use]
    pub fn session_coroutines(&self, sid: SessionId) -> Vec<&Coroutine> {
        self.coroutines
            .iter()
            .filter(|c| c.session_id == sid)
            .collect()
    }

    /// Access the session store.
    #[must_use]
    pub fn sessions(&self) -> &SessionStore {
        &self.sessions
    }

    /// Access the session store mutably.
    pub fn sessions_mut(&mut self) -> &mut SessionStore {
        &mut self.sessions
    }

    /// Runtime well-formedness predicate used by debug assertions.
    ///
    /// # Errors
    ///
    /// Returns a description of the invariant violation if the VM state is invalid.
    #[allow(clippy::too_many_lines)]
    fn wf_coroutine_state(&self, coro: &Coroutine) -> Result<(), String> {
        if self.sessions.get(coro.session_id).is_none() {
            return Err(format!(
                "coroutine {} references missing session {}",
                coro.id, coro.session_id
            ));
        }
        let Some(program) = self.programs.get(coro.program_id) else {
            return Err(format!("missing program for coroutine {}", coro.id));
        };
        if coro.pc > program.len() {
            return Err(format!("pc out of bounds for coroutine {}", coro.id));
        }
        if coro.regs.len() != usize::from(self.config.num_registers) {
            return Err(format!("register width mismatch for coroutine {}", coro.id));
        }
        for ep in &coro.owned_endpoints {
            let Some(session) = self.sessions.get(ep.sid) else {
                return Err(format!(
                    "owned endpoint missing session {}:{}",
                    ep.sid, ep.role
                ));
            };
            if !session.roles.iter().any(|role| role == &ep.role) {
                return Err(format!(
                    "owned endpoint role not in session {}:{}",
                    ep.sid, ep.role
                ));
            }
        }
        for token in &coro.progress_tokens {
            let Some(session) = self.sessions.get(token.sid) else {
                return Err(format!(
                    "progress token missing session {} for coroutine {}",
                    token.sid, coro.id
                ));
            };
            if !session
                .roles
                .iter()
                .any(|role| role == &token.endpoint.role)
            {
                return Err(format!(
                    "progress token role not in session {}:{}",
                    token.sid, token.endpoint.role
                ));
            }
        }
        for fact in &coro.knowledge_set {
            let Some(session) = self.sessions.get(fact.endpoint.sid) else {
                return Err(format!(
                    "knowledge fact missing session {}:{}",
                    fact.endpoint.sid, fact.endpoint.role
                ));
            };
            if !session.roles.iter().any(|role| role == &fact.endpoint.role) {
                return Err(format!(
                    "knowledge fact role not in session {}:{}",
                    fact.endpoint.sid, fact.endpoint.role
                ));
            }
        }
        Ok(())
    }

    fn wf_collect_session_sets(
        &self,
    ) -> Result<(BTreeSet<SessionId>, BTreeSet<SessionId>), String> {
        let mut active_sids = BTreeSet::new();
        let mut monitor_required_sids = BTreeSet::new();
        for session in self.sessions.iter() {
            active_sids.insert(session.sid);
            if !matches!(
                session.status,
                SessionStatus::Closed | SessionStatus::Cancelled | SessionStatus::Faulted { .. }
            ) {
                monitor_required_sids.insert(session.sid);
            }
            for ep in session.local_types.keys() {
                if ep.sid != session.sid {
                    return Err(format!("local type sid mismatch for role {}", ep.role));
                }
            }
            for (edge, buffer) in &session.buffers {
                if edge.sid != session.sid {
                    return Err("buffer edge sid mismatch".to_string());
                }
                if buffer.len() > buffer.capacity() {
                    return Err("buffer length exceeds capacity".to_string());
                }
            }
        }
        Ok((active_sids, monitor_required_sids))
    }

    fn wf_monitor_state(
        &self,
        active_sids: &BTreeSet<SessionId>,
        monitor_required_sids: &BTreeSet<SessionId>,
    ) -> Result<(), String> {
        for sid in self.monitor.session_kinds.keys() {
            if !active_sids.contains(sid) {
                return Err(format!("monitor tracks unknown session {sid}"));
            }
        }
        for sid in monitor_required_sids {
            if !self.monitor.session_kinds.contains_key(sid) {
                return Err(format!("monitor missing kind for active session {sid}"));
            }
        }
        Ok(())
    }

    /// Runtime well-formedness predicate used by debug assertions.
    ///
    /// # Errors
    ///
    /// Returns a description of the invariant violation if the VM state is invalid.
    #[allow(clippy::too_many_lines)]
    pub fn wf_vm_state(&self) -> Result<(), String> {
        for coro in &self.coroutines {
            self.wf_coroutine_state(coro)?;
        }

        let (active_sids, monitor_required_sids) = self.wf_collect_session_sets()?;
        self.wf_monitor_state(&active_sids, &monitor_required_sids)?;

        if !self.arena.check_invariants() {
            return Err("arena invariant violation".to_string());
        }
        Ok(())
    }

    /// Inject a message directly into a session buffer.
    ///
    /// Used by simulation middleware (network/fault injection) to deliver
    /// in-flight messages without executing a VM send instruction.
    ///
    /// # Errors
    ///
    /// Returns an error if the session does not exist.
    pub fn inject_message(
        &mut self,
        sid: SessionId,
        from: &str,
        to: &str,
        value: Value,
    ) -> Result<EnqueueResult, VMError> {
        let session = self
            .sessions
            .get_mut(sid)
            .ok_or(VMError::SessionNotFound(sid))?;
        session
            .send(from, to, value)
            .map_err(|_| VMError::SessionNotFound(sid))
    }

    /// Access all coroutines.
    #[must_use]
    pub fn coroutines(&self) -> &[Coroutine] {
        &self.coroutines
    }

    /// Pause execution for all coroutines of a role.
    pub fn pause_role(&mut self, role: &str) {
        self.paused_roles.insert(role.to_string());
    }

    /// Resume execution for all coroutines of a role.
    pub fn resume_role(&mut self, role: &str) {
        self.paused_roles.remove(role);
    }

    /// Replace the paused role set.
    pub fn set_paused_roles(&mut self, roles: &BTreeSet<String>) {
        self.paused_roles = roles.clone();
    }

    /// Access paused roles.
    #[must_use]
    pub fn paused_roles(&self) -> &BTreeSet<String> {
        &self.paused_roles
    }

    // ---- Private ----

    fn coro_index(&self, id: usize) -> usize {
        self.coroutines
            .iter()
            .position(|c| c.id == id)
            .expect("coroutine exists")
    }

    pub(crate) fn read_reg(&self, coro_idx: usize, reg: u16) -> Value {
        self.coroutines[coro_idx].regs[usize::from(reg)].clone()
    }

    fn read_reg_checked(&self, coro_idx: usize, reg: u16) -> Result<Value, Fault> {
        self.coroutines[coro_idx]
            .regs
            .get(usize::from(reg))
            .cloned()
            .ok_or(Fault::OutOfRegisters)
    }

    fn endpoint_from_reg(&self, coro_idx: usize, reg: u16) -> Result<Endpoint, Fault> {
        decode_endpoint_from_reg(&self.coroutines[coro_idx], reg)
    }

    fn decode_fact(value: Value) -> Option<(Endpoint, String)> {
        decode_endpoint_fact(value)
    }

    fn validate_payload(
        &self,
        role: &str,
        context: &str,
        label: &str,
        expected_type: Option<&ValType>,
        value: &Value,
        strict_requires_annotation: bool,
    ) -> Result<(), Fault> {
        let mode = self.config.payload_validation_mode;
        if mode == PayloadValidationMode::Off {
            return Ok(());
        }

        let actual_type = runtime_value_val_type(value);
        let payload_bytes = runtime_value_wire_size_bytes(value);
        if payload_bytes > self.config.max_payload_bytes {
            return Err(Fault::TypeViolation {
                expected: expected_type.cloned().unwrap_or_else(|| actual_type.clone()),
                actual: actual_type,
                message: format!(
                    "{role}: {context} payload '{label}' exceeds max_payload_bytes={} (actual={payload_bytes})",
                    self.config.max_payload_bytes
                ),
            });
        }

        match expected_type {
            Some(expected) => {
                if runtime_value_matches_val_type(value, expected) {
                    Ok(())
                } else {
                    Err(Fault::TypeViolation {
                        expected: expected.clone(),
                        actual: actual_type,
                        message: format!(
                            "{role}: {context} payload '{label}' violated expected type {expected:?}"
                        ),
                    })
                }
            }
            None
                if mode == PayloadValidationMode::StrictSchema && strict_requires_annotation =>
            {
                Err(Fault::TypeViolation {
                    expected: ValType::Unit,
                    actual: actual_type,
                    message: format!(
                        "{role}: {context} payload '{label}' requires explicit ValType annotation in strict_schema mode"
                    ),
                })
            }
            None => Ok(()),
        }
    }

    /// Extract partner and branches from a Recv local type.
    fn expect_recv_type(
        local_type: &LocalTypeR,
        role: &str,
    ) -> Result<(String, BranchList), Fault> {
        match local_type {
            LocalTypeR::Recv {
                partner, branches, ..
            } => Ok((partner.clone(), branches.clone())),
            other => Err(Fault::TypeViolation {
                expected: telltale_types::ValType::Unit,
                actual: telltale_types::ValType::Unit,
                message: format!("{role}: Choose expects Recv, got {other:?}"),
            }),
        }
    }

    fn monitor_precheck(
        &mut self,
        ep: &Endpoint,
        role: &str,
        instr: &crate::instr::Instr,
    ) -> Result<(), Fault> {
        if self.config.monitor_mode == MonitorMode::Off {
            return Ok(());
        }
        match instr {
            crate::instr::Instr::Send { .. } | crate::instr::Instr::Offer { .. } => {
                let local_type =
                    self.sessions
                        .lookup_type(ep)
                        .ok_or_else(|| Fault::TypeViolation {
                            expected: telltale_types::ValType::Unit,
                            actual: telltale_types::ValType::Unit,
                            message: format!("[monitor] {role}: no type registered"),
                        })?;
                if matches!(local_type, LocalTypeR::Send { .. }) {
                    Ok(())
                } else {
                    Err(Fault::TypeViolation {
                        expected: telltale_types::ValType::Unit,
                        actual: telltale_types::ValType::Unit,
                        message: format!(
                            "[monitor] {role}: expected Send state, got {local_type:?}"
                        ),
                    })
                }
            }
            crate::instr::Instr::Receive { .. } => {
                let local_type =
                    self.sessions
                        .lookup_type(ep)
                        .ok_or_else(|| Fault::TypeViolation {
                            expected: telltale_types::ValType::Unit,
                            actual: telltale_types::ValType::Unit,
                            message: format!("[monitor] {role}: no type registered"),
                        })?;
                if matches!(local_type, LocalTypeR::Recv { .. }) {
                    Ok(())
                } else {
                    Err(Fault::TypeViolation {
                        expected: telltale_types::ValType::Unit,
                        actual: telltale_types::ValType::Unit,
                        message: format!(
                            "[monitor] {role}: expected Recv state, got {local_type:?}"
                        ),
                    })
                }
            }
            crate::instr::Instr::Choose { table, .. } => {
                let mut labels = BTreeSet::new();
                if !table
                    .iter()
                    .map(|(label, _)| label)
                    .all(|label| labels.insert(label.clone()))
                {
                    return Err(Fault::Speculation {
                        message: "[monitor] structural precheck failed: duplicate choose labels"
                            .to_string(),
                    });
                }
                let local_type =
                    self.sessions
                        .lookup_type(ep)
                        .ok_or_else(|| Fault::TypeViolation {
                            expected: telltale_types::ValType::Unit,
                            actual: telltale_types::ValType::Unit,
                            message: format!("[monitor] {role}: no type registered"),
                        })?;
                if matches!(local_type, LocalTypeR::Recv { .. }) {
                    Ok(())
                } else {
                    Err(Fault::TypeViolation {
                        expected: telltale_types::ValType::Unit,
                        actual: telltale_types::ValType::Unit,
                        message: format!(
                            "[monitor] {role}: expected Recv state, got {local_type:?}"
                        ),
                    })
                }
            }
            crate::instr::Instr::Open { roles, dsts, .. } => {
                if roles.len() == dsts.len() {
                    Ok(())
                } else {
                    Err(Fault::Speculation {
                        message: "[monitor] structural precheck failed: open arity mismatch"
                            .to_string(),
                    })
                }
            }
            _ => Ok(()),
        }?;
        self.monitor
            .record(ep, &format!("{instr:?}"), self.clock.tick);
        Ok(())
    }

}
