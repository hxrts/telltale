impl ThreadedVM {
    #[allow(clippy::too_many_lines)]
    fn commit_pack(
        &mut self,
        coro: &Arc<Mutex<Coroutine>>,
        session: &Arc<Mutex<SessionState>>,
        pack: StepPack,
        output_hint: Option<OutputConditionHint>,
        handler_identity: &str,
    ) -> Result<ExecOutcome, Fault> {
        if !pack.events.is_empty() {
            apply_output_condition_gate(
                &self.config.output_condition_policy,
                &mut self.output_condition_checks,
                &mut self.trace,
                self.clock.tick,
                output_hint,
            )?;
        }

        for ev in &pack.events {
            self.intern_obs_event(ev);
            let maybe_entry = effect_trace_entry_for_event(
                ev,
                self.next_effect_id,
                handler_identity,
                self.clock.tick,
            );
            if let Some(entry) = maybe_entry {
                if self.should_capture_effect_kind(&entry.effect_kind) {
                    self.effect_trace.push(entry);
                    self.next_effect_id = self.next_effect_id.saturating_add(1);
                }
            }
        }

        let mut coro_guard = coro.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
        let was_terminal = coro_guard.is_terminal();

        match pack.coro_update {
            CoroUpdate::AdvancePc => {
                coro_guard.pc += 1;
                coro_guard.status = CoroStatus::Ready;
            }
            CoroUpdate::SetPc(pc) => {
                coro_guard.pc = pc;
                coro_guard.status = CoroStatus::Ready;
            }
            CoroUpdate::Block(ref reason) => {
                coro_guard.status = CoroStatus::Blocked(reason.clone());
            }
            CoroUpdate::Halt => {
                coro_guard.status = CoroStatus::Done;
            }
            CoroUpdate::AdvancePcWriteReg { reg, ref val } => {
                write_coro_reg(&mut coro_guard, reg, val.clone())?;
                coro_guard.pc += 1;
                coro_guard.status = CoroStatus::Ready;
            }
            CoroUpdate::AdvancePcSpawnChild { target, ref args } => {
                if self.coroutines.len() >= self.config.max_coroutines {
                    return Err(Fault::Speculation {
                        message: "max coroutines exceeded".to_string(),
                    });
                }
                let new_id = self.next_coro_id;
                self.next_coro_id = self.next_coro_id.saturating_add(1);

                let mut child = Coroutine::new(
                    new_id,
                    coro_guard.program_id,
                    coro_guard.session_id,
                    coro_guard.role.clone(),
                    self.config.num_registers,
                    self.config.initial_cost_budget,
                );
                child.pc = target;
                child.effect_ctx = coro_guard.effect_ctx.clone();
                for (dst_idx, src_reg) in args.iter().enumerate() {
                    if dst_idx >= child.regs.len() {
                        break;
                    }
                    if let Some(value) = coro_guard.regs.get(usize::from(*src_reg)).cloned() {
                        child.regs[dst_idx] = value;
                    }
                }
                self.scheduler.add_ready(new_id);
                self.coroutines.push(Arc::new(Mutex::new(child)));
                self.non_terminal_coroutines = self.non_terminal_coroutines.saturating_add(1);

                coro_guard.pc += 1;
                coro_guard.status = CoroStatus::Ready;
            }
        }
        let is_terminal = coro_guard.is_terminal();
        self.note_status_transition(was_terminal, is_terminal);

        if let Some((ep, update)) = pack.type_update {
            let mut session_guard = session.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
            match update {
                TypeUpdate::Advance(lt) => {
                    if let Some(entry) = session_guard.local_types.get_mut(&ep) {
                        entry.current = lt;
                    }
                }
                TypeUpdate::AdvanceWithOriginal(lt, orig) => {
                    if let Some(entry) = session_guard.local_types.get_mut(&ep) {
                        entry.current = lt;
                        entry.original = orig;
                    }
                }
                TypeUpdate::Remove => {
                    session_guard.local_types.remove(&ep);
                }
            }
        }

        let transfer = pack.events.iter().find_map(|event| match event {
            ObsEvent::Transferred {
                session,
                role,
                from,
                to,
                ..
            } => Some((
                Endpoint {
                    sid: *session,
                    role: role.clone(),
                },
                *from,
                *to,
            )),
            _ => None,
        });

        if let Some((endpoint, from_id, _to_id)) = &transfer {
            if *from_id != coro_guard.id {
                return Err(Fault::Transfer {
                    message: "transfer source mismatch".into(),
                });
            }
            if !coro_guard.owned_endpoints.contains(endpoint) {
                return Err(Fault::Transfer {
                    message: "endpoint not owned".into(),
                });
            }
        }

        drop(coro_guard);
        if let Some((endpoint, from_id, to_id)) = transfer {
            self.enqueue_handoff(endpoint, from_id, to_id, self.clock.tick)?;
            self.apply_handoffs_deterministically()?;
        }

        self.trace.extend(pack.events);
        let coro_guard = coro.lock().unwrap_or_else(|poisoned| poisoned.into_inner());

        match &coro_guard.status {
            CoroStatus::Ready => Ok(ExecOutcome::Continue),
            CoroStatus::Blocked(reason) => Ok(ExecOutcome::Blocked(reason.clone())),
            CoroStatus::Done => Ok(ExecOutcome::Halted),
            CoroStatus::Faulted(f) => Err(f.clone()),
            CoroStatus::Speculating => Ok(ExecOutcome::Continue),
        }
    }

    fn intern_obs_event(&mut self, ev: &ObsEvent) {
        match ev {
            ObsEvent::Sent {
                from, to, label, ..
            }
            | ObsEvent::Received {
                from, to, label, ..
            } => {
                let _: StringId = self.role_symbols.intern(from);
                let _: StringId = self.role_symbols.intern(to);
                let _: StringId = self.label_symbols.intern(label);
            }
            ObsEvent::Offered { edge, label, .. } | ObsEvent::Chose { edge, label, .. } => {
                let _: StringId = self.role_symbols.intern(&edge.sender);
                let _: StringId = self.role_symbols.intern(&edge.receiver);
                let _: StringId = self.label_symbols.intern(label);
            }
            ObsEvent::Opened { roles, .. } => {
                for role in roles {
                    let _: StringId = self.role_symbols.intern(role);
                }
            }
            ObsEvent::Invoked { role, .. }
            | ObsEvent::Tagged { role, .. }
            | ObsEvent::Checked { role, .. }
            | ObsEvent::Transferred { role, .. } => {
                let _: StringId = self.role_symbols.intern(role);
            }
            _ => {}
        }
    }

    fn enqueue_handoff(
        &mut self,
        endpoint: Endpoint,
        from_coro: usize,
        to_coro: usize,
        tick: u64,
    ) -> Result<(), Fault> {
        self.assert_delegation_handoff_owner(&endpoint, from_coro)?;
        let from_lane = self.lane_of_coro(from_coro).ok_or(Fault::Transfer {
            message: "transfer source coroutine not found".into(),
        })?;
        let to_lane = self.lane_of_coro(to_coro).ok_or(Fault::Transfer {
            message: "target coroutine not found".into(),
        })?;
        if from_lane != to_lane {
            self.contention_metrics.cross_lane_transfer_count = self
                .contention_metrics
                .cross_lane_transfer_count
                .saturating_add(1);
        }
        let handoff = LaneHandoff {
            handoff_id: self.next_handoff_id,
            tick,
            session: endpoint.sid,
            endpoint_role: endpoint.role,
            from_coro,
            to_coro,
            from_lane,
            to_lane,
        };
        self.next_handoff_id = self.next_handoff_id.saturating_add(1);
        self.pending_handoffs.push_back(handoff.clone());
        self.handoff_trace_log.push(handoff);
        Ok(())
    }

    fn apply_handoffs_deterministically(&mut self) -> Result<(), Fault> {
        while let Some(handoff) = self.pending_handoffs.pop_front() {
            self.apply_handoff(&handoff)?;
            let endpoint = Endpoint {
                sid: handoff.session,
                role: handoff.endpoint_role.clone(),
            };
            let expected_owner = if handoff.from_coro == handoff.to_coro {
                handoff.from_coro
            } else {
                handoff.to_coro
            };
            self.assert_delegation_handoff_owner(&endpoint, expected_owner)?;
            self.contention_metrics.handoff_applied_count = self
                .contention_metrics
                .handoff_applied_count
                .saturating_add(1);
        }
        Ok(())
    }

    fn apply_handoff(&mut self, handoff: &LaneHandoff) -> Result<(), Fault> {
        let endpoint = Endpoint {
            sid: handoff.session,
            role: handoff.endpoint_role.clone(),
        };
        if handoff.from_coro == handoff.to_coro {
            let source_arc =
                self.coroutines
                    .get(handoff.from_coro)
                    .cloned()
                    .ok_or(Fault::Transfer {
                        message: "transfer source coroutine not found".into(),
                    })?;
            let mut source = lock_with_contention(&source_arc, &mut self.contention_metrics);
            move_endpoint_bundle(&endpoint, &mut source, None)
        } else {
            let source_arc =
                self.coroutines
                    .get(handoff.from_coro)
                    .cloned()
                    .ok_or(Fault::Transfer {
                        message: "transfer source coroutine not found".into(),
                    })?;
            let target_arc =
                self.coroutines
                    .get(handoff.to_coro)
                    .cloned()
                    .ok_or(Fault::Transfer {
                        message: "target coroutine not found".into(),
                    })?;

            // Global lock order: lower coroutine id first.
            if handoff.from_coro < handoff.to_coro {
                let mut source = lock_with_contention(&source_arc, &mut self.contention_metrics);
                let mut target = lock_with_contention(&target_arc, &mut self.contention_metrics);
                move_endpoint_bundle(&endpoint, &mut source, Some(&mut target))
            } else {
                let mut target = lock_with_contention(&target_arc, &mut self.contention_metrics);
                let mut source = lock_with_contention(&source_arc, &mut self.contention_metrics);
                move_endpoint_bundle(&endpoint, &mut source, Some(&mut target))
            }
        }
    }

    fn assert_delegation_handoff_owner(
        &self,
        endpoint: &Endpoint,
        expected_owner: usize,
    ) -> Result<(), Fault> {
        let mut owners = Vec::new();
        for coro in &self.coroutines {
            let guard = coro.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
            if guard.owned_endpoints.contains(endpoint) {
                owners.push(guard.id);
            }
        }
        if owners == vec![expected_owner] {
            return Ok(());
        }
        // Intentional discard: values available for debugging but not in error message.
        let _ = (endpoint, owners, expected_owner);
        Err(transfer_fault_delegation_guard_violation("for handoff"))
    }
}
