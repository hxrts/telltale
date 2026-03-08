/// Approximate retained state for the live VM runtime.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct VmMemoryUsage {
    /// Session-store retained state.
    pub session_store: SessionStoreMemoryUsage,
    /// Number of coroutine records still retained by the VM.
    pub coroutine_records: usize,
    /// Number of terminal coroutine records retained by the VM.
    pub terminal_coroutines: usize,
    /// Number of loaded immutable program records.
    pub program_count: usize,
    /// Total instruction count across loaded programs.
    pub program_instruction_count: usize,
    /// Number of retained observable events.
    pub obs_events: usize,
    /// Number of retained effect-trace entries.
    pub effect_trace_entries: usize,
    /// Number of retained replay-consumption artifacts.
    pub communication_artifacts: usize,
    /// Number of retained output-condition checks.
    pub output_condition_checks: usize,
    /// Estimated retained bytes by VM subsystem.
    pub retained_bytes: VmRetainedBytes,
}
/// Estimated retained bytes for VM subsystems.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct VmRetainedBytes {
    /// Session-store retained bytes.
    pub session_store: usize,
    /// Coroutine state.
    pub coroutines: usize,
    /// Immutable program storage.
    pub programs: usize,
    /// Resource-state storage.
    pub resource_states: usize,
    /// Observable/effect trace storage.
    pub traces: usize,
    /// Replay-state and replay-artifact storage.
    pub replay: usize,
    /// Output-condition diagnostics.
    pub output_condition_checks: usize,
    /// Scheduler and control-state bookkeeping.
    pub scheduler_and_control: usize,
    /// Symbol interning tables.
    pub symbols: usize,
    /// Guard-layer resources.
    pub guard_layer: usize,
    /// Session monitor metadata.
    pub monitor: usize,
    /// Arena slot storage.
    pub arena: usize,
    /// Aggregate retained bytes across VM subsystems.
    pub total: usize,
}

fn vm_serialized_bytes<T: Serialize>(value: &T) -> usize {
    bincode::serialized_size(value)
        .ok()
        .and_then(|bytes| usize::try_from(bytes).ok())
        .unwrap_or(0)
}

impl VM {
    fn communication_replay_enabled(&self) -> bool {
        !matches!(
            self.config.communication_replay_mode,
            CommunicationReplayMode::Off
        )
    }

    fn intern_load_plan_symbols(&mut self, plan: &crate::session::SessionOpenPlan, sid: SessionId) {
        for role in plan.roles() {
            let _: StringId = self.role_symbols.intern(role);
        }
        let _: StringId = self.handler_symbols.intern(crate::session::DEFAULT_HANDLER_ID);
        let edge_handlers: Vec<_> = self
            .sessions
            .get(sid)
            .map(|session| session.edge_handlers.keys().cloned().collect())
            .unwrap_or_default();
        for edge in edge_handlers {
            let _: EdgeId = self.intern_edge(&edge);
        }
    }

    /// Create a VM instance from configuration.
    #[must_use]
    pub fn new(config: VMConfig) -> Self {
        Self::new_with_models(config)
    }

    fn bind_default_handlers_for_session(&mut self, sid: SessionId) {
        self.sessions.set_default_handler_for_session(
            sid,
            crate::session::DEFAULT_HANDLER_ID.to_string(),
        );
        self.handler_symbols.intern(crate::session::DEFAULT_HANDLER_ID);
    }

    fn ensure_session_capacity(&self) -> Result<(), VMError> {
        if self.sessions.active_count() >= self.config.max_sessions {
            return Err(VMError::TooManySessions {
                max: self.config.max_sessions,
            });
        }
        Ok(())
    }

    fn coroutine_runtime_eligible(&self, coro_id: usize) -> bool {
        let Some(idx) = self.coro_index(coro_id) else {
            return false;
        };
        let role = &self.coroutines[idx].role;
        !(self.paused_coro_ids.contains(&coro_id)
            || self.paused_roles.contains(role)
            || self.crashed_sites.contains(role)
            || self.timed_out_coro_ids.contains(&coro_id)
            || self.timed_out_sites.contains_key(role))
    }

    fn mark_eligibility_dirty(&mut self) {
        self.eligibility_dirty = true;
    }

    fn sync_ready_eligibility_for(&mut self, coro_id: usize) {
        let eligible = self.sched.is_ready(coro_id) && self.coroutine_runtime_eligible(coro_id);
        let eligibility = if eligible {
            crate::scheduler::ReadyEligibility::Eligible
        } else {
            crate::scheduler::ReadyEligibility::Ineligible
        };
        self.sched.set_ready_eligibility(coro_id, eligibility);
        #[cfg(debug_assertions)]
        {
            if eligible {
                self.eligible_ready.insert(coro_id);
            } else {
                self.eligible_ready.remove(&coro_id);
            }
        }
    }

    fn refresh_ready_eligibility(&mut self) {
        self.sched.clear_ready_eligibility();
        #[cfg(debug_assertions)]
        self.eligible_ready.clear();
        for coro_id in self.sched.ready_set_snapshot() {
            let eligible = self.coroutine_runtime_eligible(coro_id);
            let eligibility = if eligible {
                crate::scheduler::ReadyEligibility::Eligible
            } else {
                crate::scheduler::ReadyEligibility::Ineligible
            };
            self.sched.set_ready_eligibility(coro_id, eligibility);
            #[cfg(debug_assertions)]
            if eligible {
                self.eligible_ready.insert(coro_id);
            }
        }
        self.eligibility_dirty = false;
    }

    fn ensure_ready_eligibility(&mut self) {
        if self.eligibility_dirty {
            self.refresh_ready_eligibility();
        }
    }

    #[cfg(debug_assertions)]
    fn debug_assert_ready_eligibility_consistent(&self) {
        for coro_id in &self.eligible_ready {
            debug_assert!(self.sched.is_ready(*coro_id));
            debug_assert!(self.coroutine_runtime_eligible(*coro_id));
        }
    }

    fn sync_communication_consumption_mode(&mut self) {
        self.communication_consumption
            .set_mode(self.config.communication_replay_mode);
    }

    fn allocate_send_sequence(&mut self, edge: &Edge) -> u64 {
        if !self.communication_replay_enabled() {
            // Off mode preserves legacy behavior and avoids replay bookkeeping.
            return 0;
        }
        self.sync_communication_consumption_mode();
        self.communication_consumption.allocate_send_sequence(edge)
    }

    fn consume_receive_identity(
        &mut self,
        identity: CommunicationIdentity,
    ) -> Result<CommunicationConsumeResult, CommunicationReplayError> {
        if !self.communication_replay_enabled() {
            // Off mode intentionally skips replay-consumption state and artifacts.
            return Ok(CommunicationConsumeResult {
                mode: CommunicationReplayMode::Off,
                pre_root: self.communication_consumption.root(),
                post_root: self.communication_consumption.root(),
                consumed_nullifier: None,
            });
        }
        self.sync_communication_consumption_mode();
        let result = self.communication_consumption.consume_receive(&identity)?;
        self.communication_consumption_artifacts.push(
            CommunicationConsumptionArtifact {
                tick: self.clock.tick,
                identity,
                mode: result.mode,
                pre_root: result.pre_root,
                post_root: result.post_root,
            },
            &self.config.observability_retention,
        );
        Ok(result)
    }

    fn session_open_plan(
        &mut self,
        image: &CodeImage,
    ) -> &crate::session::SessionOpenPlan {
        let key = format!("{image:p}");
        self.session_open_plans
            .entry(key)
            .or_insert_with(|| crate::session::SessionOpenPlan::new(&image.roles(), &image.local_types))
    }

    fn open_choreography_session(
        &mut self,
        plan: &crate::session::SessionOpenPlan,
    ) -> (SessionId, Vec<String>) {
        let sid = self.sessions.next_session_id();
        let roles = plan.roles().to_vec();
        self.sessions
            .open_with_sid_from_plan(sid, plan, &self.config.buffer_config);
        (sid, roles)
    }

    fn finalize_open_choreography_session(
        &mut self,
        sid: SessionId,
        roles: &[String],
        plan: &crate::session::SessionOpenPlan,
    ) -> Result<(), VMError> {
        self.next_session_id = self.sessions.next_session_id();
        self.bind_default_handlers_for_session(sid);
        self.intern_load_plan_symbols(plan, sid);
        self.monitor.set_kind(sid, SessionKind::Peer);
        self.resource_states
            .entry(sid)
            .or_default();
        self.apply_open_delta(sid)
            .map_err(VMError::PersistenceError)?;
        self.obs_trace.push(
            ObsEvent::Opened {
                tick: self.clock.tick,
                session: sid,
                roles: roles.to_vec(),
            },
            &self.config.observability_retention,
        );
        Ok(())
    }

    fn spawn_coroutine_for_role(
        &mut self,
        image: &CodeImage,
        sid: SessionId,
        role: &str,
    ) -> Result<(), VMError> {
        if self.coroutines.len() >= self.config.max_coroutines {
            return Err(VMError::TooManyCoroutines {
                max: self.config.max_coroutines,
            });
        }

        let program_id = self
            .programs
            .intern(image.programs.get(role).cloned().unwrap_or_default());
        if self.code.is_none() {
            let program = self
                .programs
                .get(program_id)
                .expect("interned program must exist")
                .clone();
            self.code = Some(program);
        }

        let coro_id = self.next_coro_id;
        self.next_coro_id += 1;

        let endpoint = Endpoint {
            sid,
            role: role.to_string(),
        };
        self.role_coroutines
            .entry(role.to_string())
            .or_default()
            .push(coro_id);
        if self.paused_roles.contains(role) {
            self.paused_coro_ids.insert(coro_id);
        }
        if self.timed_out_sites.contains_key(role) {
            self.timed_out_coro_ids.insert(coro_id);
        }
        let mut coro = Coroutine::new(
            coro_id,
            program_id,
            sid,
            role.to_string(),
            self.config.num_registers,
            self.config.initial_cost_budget,
        );
        coro.owned_endpoints.push(endpoint.clone());
        if !coro.regs.is_empty() {
            coro.regs[0] = Value::Endpoint(endpoint);
        }
        self.sched.add_ready(coro_id);
        self.coroutines.push(coro);
        self.coro_slots.insert(coro_id, self.coroutines.len() - 1);
        self.sync_ready_eligibility_for(coro_id);
        Ok(())
    }

    fn spawn_session_coroutines(
        &mut self,
        image: &CodeImage,
        sid: SessionId,
        roles: &[String],
    ) -> Result<(), VMError> {
        for role in roles {
            self.spawn_coroutine_for_role(image, sid, role)?;
        }
        Ok(())
    }

    /// Load a choreography from a verified code image.
    ///
    /// Creates a session (with local types), spawns coroutines per role,
    /// and returns the session ID. Type state is initialized in the
    /// session store — no separate monitor needed.
    ///
    /// # Errors
    ///
    /// Returns an error if session or coroutine limits are exceeded.
    pub fn load_choreography(&mut self, image: &CodeImage) -> Result<SessionId, VMError> {
        self.ensure_session_capacity()?;
        image.validate_runtime_shape().map_err(|reason| VMError::InvalidCodeImage { reason })?;
        let plan = self.session_open_plan(image).clone();
        let (sid, roles) = self.open_choreography_session(&plan);
        self.finalize_open_choreography_session(sid, &roles, &plan)?;
        self.programs.reserve(image.programs.len());
        self.coroutines.reserve(roles.len());
        self.spawn_session_coroutines(image, sid, &roles)?;
        Ok(sid)
    }

}
