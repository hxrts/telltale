impl VM {
    fn recv_choose_payload(
        &mut self,
        ep: &Endpoint,
        role: &str,
        partner: &str,
    ) -> Result<(Edge, Value), Fault> {
        let edge = Edge::new(ep.sid, partner.to_string(), role.to_string());
        let session = self
            .sessions
            .get_mut(ep.sid)
            .ok_or_else(|| Fault::ChannelClosed {
                endpoint: ep.clone(),
            })?;
        let val = session
            .recv_verified(partner, role)
            .map_err(|message| Fault::VerificationFailed {
                edge: edge.clone(),
                message,
            })?
            .ok_or_else(|| Fault::ChannelClosed {
                endpoint: ep.clone(),
            })?;
        Ok((edge, val))
    }

    fn resolve_choose_step(
        &self,
        ep: &Endpoint,
        role: &str,
        label: &str,
        table: &[(String, PC)],
    ) -> Result<(LocalTypeR, PC), Fault> {
        let local_type = self
            .sessions
            .lookup_type(ep)
            .ok_or_else(|| Fault::TypeViolation {
                expected: telltale_types::ValType::Unit,
                actual: telltale_types::ValType::Unit,
                message: format!("{role}: no type registered"),
            })?;
        let _ = Self::expect_recv_type(local_type, role)?;
        let session = self
            .sessions
            .get(ep.sid)
            .ok_or_else(|| Fault::ChannelClosed {
                endpoint: ep.clone(),
            })?;
        let cached = session
            .lookup_branch_resolution(ep, label)
            .ok_or_else(|| Fault::UnknownLabel {
                label: label.to_string(),
            })?;
        if cached.direction != crate::session::BranchDirection::Recv {
            return Err(Fault::TypeViolation {
                expected: telltale_types::ValType::Unit,
                actual: telltale_types::ValType::Unit,
                message: format!("{role}: Choose expects Recv, got {local_type:?}"),
            });
        }
        let target_pc = table
            .iter()
            .find(|(l, _)| l == label)
            .map(|(_, pc)| *pc)
            .ok_or_else(|| Fault::UnknownLabel {
                label: label.to_string(),
            })?;
        Ok((cached.continuation.clone(), target_pc))
    }

    pub(crate) fn step_check(
        &mut self,
        coro_idx: usize,
        role: &str,
        _sid: SessionId,
        knowledge: u16,
        target: u16,
        dst: u16,
    ) -> Result<StepPack, Fault> {
        let know_val = self.coroutines[coro_idx]
            .regs
            .get(usize::from(knowledge))
            .ok_or(Fault::OutOfRegisters)?
            .clone();
        let (endpoint, fact) = Self::decode_fact(know_val).ok_or_else(|| Fault::Transfer {
            message: format!("{role}: check expects (endpoint, string) fact"),
        })?;
        let target_val = self.coroutines[coro_idx]
            .regs
            .get(usize::from(target))
            .ok_or(Fault::OutOfRegisters)?
            .clone();
        let target_role = match target_val {
            Value::Str(s) => s,
            _ => {
                return Err(Fault::Transfer {
                    message: format!("{role}: check expects target role string"),
                })
            }
        };
        let known_fact = self.coroutines[coro_idx]
            .knowledge_set
            .iter()
            .find(|k| k.endpoint == endpoint && k.fact == fact);
        let permitted =
            known_fact.is_some_and(|k| self.config.flow_policy.allows_knowledge(k, &target_role));
        Ok(StepPack {
            coro_update: CoroUpdate::AdvancePcWriteReg {
                reg: dst,
                val: Value::Bool(permitted),
            },
            type_update: None,
            events: vec![ObsEvent::Checked {
                tick: self.clock.tick,
                session: endpoint.sid,
                role: role.to_string(),
                target: target_role,
                permitted,
            }],
        })
    }

    /// Choose: external choice — receive a label and dispatch via branch table.
    pub(crate) fn step_choose(
        &mut self,
        coro_idx: usize,
        role: &str,
        chan: u16,
        table: &[(String, PC)],
        handler: &dyn EffectHandler,
    ) -> Result<StepPack, Fault> {
        let ep = self.endpoint_from_reg(coro_idx, chan)?;
        if !self.coroutines[coro_idx].owned_endpoints.contains(&ep) {
            return Err(Fault::ChannelClosed { endpoint: ep });
        }
        let sid = ep.sid;

        let partner = {
            let local_type = self
                .sessions
                .lookup_type(&ep)
                .ok_or_else(|| Fault::TypeViolation {
                    expected: telltale_types::ValType::Unit,
                    actual: telltale_types::ValType::Unit,
                    message: format!("{role}: no type registered"),
                })?;
            let (partner, _) = Self::expect_recv_type(local_type, role)?;
            partner.to_string()
        };

        let session = self.sessions.get(sid).ok_or_else(|| Fault::ChannelClosed {
            endpoint: ep.clone(),
        })?;
        if !session.has_message(&partner, role) {
            return Ok(StepPack {
                coro_update: CoroUpdate::Block(BlockReason::Recv {
                    edge: Edge::new(sid, partner.clone(), role.to_string()),
                    token: ProgressToken::for_endpoint(ep.clone()),
                }),
                type_update: None,
                events: vec![],
            });
        }

        let (edge, val) = self.recv_choose_payload(&ep, role, &partner)?;
        self.validate_payload(
            role,
            "choose",
            "<branch-label>",
            Some(&ValType::String),
            &val,
            false,
        )?;
        let label = decode_branch_label_payload(role, &val)?;
        let (continuation, target_pc) = self.resolve_choose_step(&ep, role, &label, table)?;

        handler
            .handle_recv(
                role,
                &partner,
                &label,
                &mut self.coroutines[coro_idx].regs,
                &val,
            )
            .map_err(|e| Fault::Invoke { message: e })?;

        let original = self.sessions.original_type(&ep).unwrap_or(&LocalTypeR::End);
        let (_resolved, type_update) = resolve_type_update(&continuation, original, &ep);

        Ok(StepPack {
            coro_update: CoroUpdate::SetPc(target_pc),
            type_update,
            events: vec![
                ObsEvent::Received {
                    tick: self.clock.tick,
                    edge,
                    session: sid,
                    from: partner.clone(),
                    to: role.to_string(),
                    label: label.clone(),
                },
                ObsEvent::Chose {
                    tick: self.clock.tick,
                    edge: Edge::new(sid, partner, role.to_string()),
                    label,
                },
            ],
        })
    }

    /// Offer: internal choice — send selected label.
    #[allow(clippy::too_many_lines)]
    pub(crate) fn step_offer(
        &mut self,
        coro_idx: usize,
        role: &str,
        chan: u16,
        label: &str,
        handler: &dyn EffectHandler,
    ) -> Result<StepPack, Fault> {
        let ep = self.endpoint_from_reg(coro_idx, chan)?;
        if !self.coroutines[coro_idx].owned_endpoints.contains(&ep) {
            return Err(Fault::ChannelClosed { endpoint: ep });
        }
        let sid = ep.sid;

        let local_type = self
            .sessions
            .lookup_type(&ep)
            .ok_or_else(|| Fault::TypeViolation {
                expected: telltale_types::ValType::Unit,
                actual: telltale_types::ValType::Unit,
                message: format!("{role}: no type registered"),
            })?;

        match local_type {
            LocalTypeR::Send { partner, .. } => {
                let partner = partner.clone();
                let cached = self
                    .sessions
                    .get(sid)
                    .and_then(|session| session.lookup_branch_resolution(&ep, label))
                    .ok_or_else(|| Fault::UnknownLabel {
                        label: label.to_string(),
                    })?;
                if cached.direction != crate::session::BranchDirection::Send {
                    return Err(Fault::TypeViolation {
                        expected: telltale_types::ValType::Unit,
                        actual: telltale_types::ValType::Unit,
                        message: format!("{role}: Offer expects Send, got {local_type:?}"),
                    });
                }
                let expected_type = cached.expected_type.clone();
                let continuation = cached.continuation.clone();

                let offer_payload = Value::Str(label.to_string());
                let fast_path = SendDecisionFastPathInput::new(
                    sid,
                    role,
                    &partner,
                    label,
                    Some(&offer_payload),
                );
                let decision = if let Some(decision) = handler.send_decision_fast_path(
                    fast_path,
                    &self.coroutines[coro_idx].regs,
                    Some(&offer_payload),
                ) {
                    decision.map_err(|e| Fault::Invoke { message: e })?
                } else {
                    handler
                        .send_decision(SendDecisionInput {
                            sid,
                            role,
                            partner: &partner,
                            label,
                            state: &self.coroutines[coro_idx].regs,
                            payload: Some(offer_payload),
                        })
                        .map_err(|e| Fault::Invoke { message: e })?
                };
                if let SendDecision::Deliver(payload) = &decision {
                    self.validate_payload(
                        role,
                        "offer",
                        label,
                        expected_type.as_ref(),
                        payload,
                        false,
                    )?;
                }
                let session = self
                    .sessions
                    .get_mut(sid)
                    .ok_or_else(|| Fault::ChannelClosed {
                        endpoint: ep.clone(),
                    })?;
                let enqueue = match decision {
                    SendDecision::Deliver(payload) => session
                        .send(role, &partner, payload)
                        .map_err(|e| Fault::Invoke { message: e })?,
                    SendDecision::Drop | SendDecision::Defer => EnqueueResult::Dropped,
                };
                match enqueue {
                    EnqueueResult::Ok => {}
                    EnqueueResult::WouldBlock => {
                        return Ok(StepPack {
                            coro_update: CoroUpdate::Block(BlockReason::Send {
                                edge: Edge::new(sid, role.to_string(), partner.clone()),
                            }),
                            type_update: None,
                            events: vec![],
                        });
                    }
                    EnqueueResult::Full => {
                        return Err(Fault::BufferFull {
                            endpoint: ep.clone(),
                        });
                    }
                    EnqueueResult::Dropped => {}
                }

                let original = self.sessions.original_type(&ep).unwrap_or(&LocalTypeR::End);
                let (_resolved, type_update) = resolve_type_update(&continuation, original, &ep);

                Ok(StepPack {
                    coro_update: CoroUpdate::AdvancePc,
                    type_update,
                    events: vec![
                        ObsEvent::Sent {
                            tick: self.clock.tick,
                            edge: Edge::new(sid, role.to_string(), partner.clone()),
                            session: sid,
                            from: role.to_string(),
                            to: partner.clone(),
                            label: label.to_string(),
                        },
                        ObsEvent::Offered {
                            tick: self.clock.tick,
                            edge: Edge::new(sid, role.to_string(), partner),
                            label: label.to_string(),
                        },
                    ],
                })
            }
            other => Err(Fault::TypeViolation {
                expected: telltale_types::ValType::Unit,
                actual: telltale_types::ValType::Unit,
                message: format!("{role}: Offer expects Send, got {other:?}"),
            }),
        }
    }

    /// Close: close session, remove type entry.
    pub(crate) fn step_close(&mut self, coro_idx: usize, session: u16) -> Result<StepPack, Fault> {
        let ep = self.endpoint_from_reg(coro_idx, session)?;
        if !self.coroutines[coro_idx].owned_endpoints.contains(&ep) {
            return Err(Fault::Close {
                message: "endpoint not owned".to_string(),
            });
        }
        let sid = ep.sid;
        self.sessions
            .close(sid)
            .map_err(|e| Fault::Close { message: e })?;
        self.apply_close_delta(sid)
            .map_err(|e| Fault::Close { message: e })?;
        self.monitor.remove_kind(sid);
        self.resource_states.remove(&sid);
        self.communication_consumption.prune_session(sid);
        let epoch = self.sessions.get(sid).map_or(0, |session| session.epoch);

        Ok(StepPack {
            coro_update: CoroUpdate::AdvancePc,
            type_update: Some((ep, TypeUpdate::Remove)),
            events: vec![
                ObsEvent::Closed {
                    tick: self.clock.tick,
                    session: sid,
                },
                ObsEvent::EpochAdvanced {
                    tick: self.clock.tick,
                    sid,
                    epoch,
                },
            ],
        })
    }
}
