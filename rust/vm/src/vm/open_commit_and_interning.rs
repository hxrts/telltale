impl VM {
    pub(crate) fn step_open(
        &mut self,
        coro_idx: usize,
        _role: &str,
        roles: &[String],
        local_types: &[(String, LocalTypeR)],
        handlers: &[((String, String), String)],
        dsts: &[(String, u16)],
    ) -> Result<StepPack, Fault> {
        if local_types.len() != dsts.len() {
            return Err(Fault::Close {
                message: "open arity mismatch".to_string(),
            });
        }
        let triples: Vec<(String, LocalTypeR, u16)> = local_types
            .iter()
            .zip(dsts.iter())
            .map(|((r, lt), (r2, dst))| (r.clone(), lt.clone(), r2.clone(), *dst))
            .map(|(r, lt, r2, dst)| {
                if r == r2 {
                    Ok((r, lt, dst))
                } else {
                    Err(Fault::Close {
                        message: "open arity mismatch".to_string(),
                    })
                }
            })
            .collect::<Result<Vec<_>, _>>()?;

        let open_roles: Vec<String> = triples.iter().map(|(r, _, _)| r.clone()).collect();
        let mut distinct = BTreeSet::new();
        let spatial_ok =
            !open_roles.is_empty() && open_roles.iter().all(|r| distinct.insert(r.clone()));
        if !spatial_ok {
            return Err(Fault::Speculation {
                message: "spatial requirements failed".to_string(),
            });
        }

        let has_handler = |sender: &str, receiver: &str| {
            handlers
                .iter()
                .any(|((s, r), _)| s == sender && r == receiver)
        };
        let covers_edges = open_roles.iter().all(|sender| {
            open_roles
                .iter()
                .all(|receiver| has_handler(sender, receiver))
        });
        if !covers_edges {
            return Err(Fault::Speculation {
                message: "handler bindings missing".to_string(),
            });
        }

        let initial_types: BTreeMap<String, LocalTypeR> = local_types.iter().cloned().collect();
        let sid = self.sessions.open(
            open_roles.clone(),
            &self.config.buffer_config,
            &initial_types,
        );
        self.next_session_id = self.sessions.next_session_id();
        for ((sender, receiver), handler_id) in handlers {
            self.sessions.update_handler(
                &Edge::new(sid, sender.clone(), receiver.clone()),
                handler_id.clone(),
            );
        }
        self.monitor.set_kind(sid, SessionKind::Peer);
        self.resource_states
            .entry(sid)
            .or_default();
        self.apply_open_delta(sid).map_err(|e| Fault::Transfer {
            message: format!("open persistence delta failed: {e}"),
        })?;

        for (_, _, reg) in &triples {
            if usize::from(*reg) >= self.coroutines[coro_idx].regs.len() {
                return Err(Fault::OutOfRegisters);
            }
        }

        {
            let coro = &mut self.coroutines[coro_idx];
            for (endpoint_role, _, reg) in &triples {
                let ep = Endpoint {
                    sid,
                    role: endpoint_role.clone(),
                };
                coro.regs[usize::from(*reg)] = Value::Endpoint(ep.clone());
                if !coro.owned_endpoints.contains(&ep) {
                    coro.owned_endpoints.push(ep);
                }
            }
        }

        Ok(StepPack {
            coro_update: CoroUpdate::AdvancePc,
            type_update: None,
            events: vec![ObsEvent::Opened {
                tick: self.clock.tick,
                session: sid,
                roles: if roles.is_empty() {
                    open_roles
                } else {
                    roles.to_vec()
                },
            }],
        })
    }

    /// Commit a `StepPack` atomically: apply coroutine update, type update, events.
    #[allow(clippy::too_many_lines)]
    fn commit_pack(
        &mut self,
        coro_idx: usize,
        pack: StepPack,
        output_hint: Option<crate::output_condition::OutputConditionHint>,
        handler_identity: &str,
    ) -> Result<ExecOutcome, Fault> {
        // Output-condition gate: any observable output must pass the configured verifier.
        if !pack.events.is_empty() {
            if let Err(fault) = apply_output_condition_gate(
                &self.config.output_condition_policy,
                &mut self.output_condition_checks,
                &mut self.obs_trace,
                self.clock.tick,
                output_hint,
            ) {
                self.coroutines[coro_idx].status = CoroStatus::Faulted(fault.clone());
                return Err(fault);
            }
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

        let coro = &mut self.coroutines[coro_idx];

        // Apply coroutine update.
        match pack.coro_update {
            CoroUpdate::AdvancePc => {
                coro.pc += 1;
                coro.status = CoroStatus::Ready;
            }
            CoroUpdate::SetPc(pc) => {
                coro.pc = pc;
                coro.status = CoroStatus::Ready;
            }
            CoroUpdate::Block(ref reason) => {
                coro.status = CoroStatus::Blocked(reason.clone());
                // PC unchanged — instruction will re-execute on unblock.
            }
            CoroUpdate::AdvancePcBlock(ref reason) => {
                coro.pc += 1;
                coro.status = CoroStatus::Blocked(reason.clone());
            }
            CoroUpdate::Halt => {
                coro.status = CoroStatus::Done;
            }
            CoroUpdate::AdvancePcWriteReg { reg, ref val } => {
                coro.regs[usize::from(reg)] = val.clone();
                coro.pc += 1;
                coro.status = CoroStatus::Ready;
            }
        }

        // Apply type update.
        if let Some((ep, update)) = pack.type_update {
            match update {
                TypeUpdate::Advance(lt) => self.sessions.update_type(&ep, lt),
                TypeUpdate::AdvanceWithOriginal(lt, orig) => {
                    self.sessions.update_type(&ep, lt);
                    self.sessions.update_original(&ep, orig);
                }
                TypeUpdate::Remove => self.sessions.remove_type(&ep),
            }
        }

        // Emit events.
        self.obs_trace.extend(pack.events);

        // Map to ExecOutcome.
        match &self.coroutines[coro_idx].status {
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
            | ObsEvent::Checked { role, .. } => {
                let _: StringId = self.role_symbols.intern(role);
            }
            ObsEvent::Transferred { role, .. } => {
                let _: StringId = self.role_symbols.intern(role);
            }
            _ => {}
        }
    }
}
