fn step_join(coro: &mut Coroutine, sid: SessionId, tick: u64) -> Result<StepPack, Fault> {
    if coro.spec_state.is_none() {
        return Err(speculation_fault_join_requires_active());
    }
    coro.spec_state = None;
    Ok(StepPack {
        coro_update: CoroUpdate::AdvancePc,
        type_update: None,
        events: vec![ObsEvent::Joined { tick, session: sid }],
    })
}

fn step_abort(coro: &mut Coroutine, sid: SessionId, tick: u64) -> Result<StepPack, Fault> {
    if coro.spec_state.is_none() {
        return Err(speculation_fault_abort_requires_active());
    }
    // Deterministic V2 policy mirrors cooperative VM: clear speculation state
    // and emit one abort event without side effects on non-spec runtime fields.
    coro.spec_state = None;
    Ok(StepPack {
        coro_update: CoroUpdate::AdvancePc,
        type_update: None,
        events: vec![ObsEvent::Aborted { tick, session: sid }],
    })
}

fn step_transfer(
    coro: &mut Coroutine,
    role: &str,
    endpoint: u16,
    target: u16,
    _bundle: u16,
    tick: u64,
) -> Result<StepPack, Fault> {
    let request = decode_transfer_request(coro, role, endpoint, target)?;

    Ok(StepPack {
        coro_update: CoroUpdate::AdvancePc,
        type_update: None,
        events: vec![ObsEvent::Transferred {
            tick,
            session: request.endpoint.sid,
            role: role.to_string(),
            from: coro.id,
            to: request.target_id,
        }],
    })
}

fn step_tag(
    coro: &mut Coroutine,
    role: &str,
    fact_reg: u16,
    dst: u16,
    tick: u64,
) -> Result<StepPack, Fault> {
    let fact_val = coro
        .regs
        .get(usize::from(fact_reg))
        .ok_or(Fault::OutOfRegisters)?
        .clone();
    let (endpoint, fact) = decode_endpoint_fact(fact_val).ok_or_else(|| Fault::Transfer {
        message: format!("{role}: tag expects (endpoint, string) fact"),
    })?;
    coro.knowledge_set.push(crate::coroutine::KnowledgeFact {
        endpoint: endpoint.clone(),
        fact: fact.clone(),
    });
    Ok(StepPack {
        coro_update: CoroUpdate::AdvancePcWriteReg {
            reg: dst,
            val: Value::Bool(true),
        },
        type_update: None,
        events: vec![ObsEvent::Tagged {
            tick,
            session: endpoint.sid,
            role: role.to_string(),
            fact,
        }],
    })
}

fn step_check(
    coro: &mut Coroutine,
    config: &VMConfig,
    role: &str,
    knowledge: u16,
    target: u16,
    dst: u16,
    tick: u64,
) -> Result<StepPack, Fault> {
    let know_val = coro
        .regs
        .get(usize::from(knowledge))
        .ok_or(Fault::OutOfRegisters)?
        .clone();
    let (endpoint, fact) = decode_endpoint_fact(know_val).ok_or_else(|| Fault::Transfer {
        message: format!("{role}: check expects (endpoint, string) fact"),
    })?;
    let target_val = coro
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
    let known_fact = coro
        .knowledge_set
        .iter()
        .find(|k| k.endpoint == endpoint && k.fact == fact);
    let permitted =
        known_fact.is_some_and(|k| config.flow_policy.allows_knowledge(k, &target_role));
    Ok(StepPack {
        coro_update: CoroUpdate::AdvancePcWriteReg {
            reg: dst,
            val: Value::Bool(permitted),
        },
        type_update: None,
        events: vec![ObsEvent::Checked {
            tick,
            session: endpoint.sid,
            role: role.to_string(),
            target: target_role,
            permitted,
        }],
    })
}

#[allow(clippy::too_many_lines)]
fn step_choose(
    coro: &mut Coroutine,
    session: &mut SessionState,
    role: &str,
    chan: u16,
    table: &[(String, PC)],
    ctx: &ThreadedStepCtx<'_>,
) -> Result<StepPack, Fault> {
    let ep = endpoint_from_reg(coro, chan)?;
    if !coro.owned_endpoints.contains(&ep) {
        return Err(Fault::ChannelClosed {
            endpoint: ep.clone(),
        });
    }
    let sid = ep.sid;

    let local_type = session
        .local_types
        .get(&ep)
        .ok_or_else(|| Fault::TypeViolation {
            expected: telltale_types::ValType::Unit,
            actual: telltale_types::ValType::Unit,
            message: format!("{role}: no type registered"),
        })?
        .current
        .clone();

    let (partner, branches) = match &local_type {
        LocalTypeR::Recv {
            partner, branches, ..
        } => (partner.clone(), branches.clone()),
        other => {
            return Err(Fault::TypeViolation {
                expected: telltale_types::ValType::Unit,
                actual: telltale_types::ValType::Unit,
                message: format!("{role}: Choose expects Recv, got {other:?}"),
            })
        }
    };

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

    let edge = Edge::new(sid, partner.clone(), role.to_string());
    let val = session
        .recv_verified(&partner, role)
        .map_err(|message| Fault::VerificationFailed {
            edge: edge.clone(),
            message,
        })?
        .ok_or_else(|| Fault::ChannelClosed {
            endpoint: ep.clone(),
        })?;
    validate_payload(
        ctx.config,
        role,
        "choose",
        "<branch-label>",
        Some(&ValType::String),
        &val,
        false,
    )?;
    let label = match &val {
        Value::Str(l) => l.clone(),
        _ => unreachable!("validate_payload enforces string branch labels for choose"),
    };

    let (_lbl, _vt, continuation) = branches
        .iter()
        .find(|(l, _, _)| l.name == label)
        .ok_or_else(|| Fault::UnknownLabel {
            label: label.clone(),
        })?
        .clone();

    let target_pc = table
        .iter()
        .find(|(l, _)| *l == label)
        .map(|(_, pc)| *pc)
        .ok_or_else(|| Fault::UnknownLabel {
            label: label.clone(),
        })?;

    ctx.handler
        .handle_recv(role, &partner, &label, &mut coro.regs, &val)
        .map_err(|e| Fault::Invoke { message: e })?;

    let original = session
        .local_types
        .get(&ep)
        .map(|entry| &entry.original)
        .unwrap_or(&LocalTypeR::End);
    let (_resolved, type_update) = resolve_type_update(&continuation, original, &ep);

    Ok(StepPack {
        coro_update: CoroUpdate::SetPc(target_pc),
        type_update,
        events: vec![
            ObsEvent::Received {
                tick: ctx.tick,
                edge,
                session: sid,
                from: partner.clone(),
                to: role.to_string(),
                label: label.clone(),
            },
            ObsEvent::Chose {
                tick: ctx.tick,
                edge: Edge::new(sid, partner, role.to_string()),
                label,
            },
        ],
    })
}

#[allow(clippy::too_many_lines)]
fn step_offer(
    coro: &mut Coroutine,
    session: &mut SessionState,
    role: &str,
    chan: u16,
    label: &str,
    ctx: &ThreadedStepCtx<'_>,
) -> Result<StepPack, Fault> {
    let ep = endpoint_from_reg(coro, chan)?;
    if !coro.owned_endpoints.contains(&ep) {
        return Err(Fault::ChannelClosed {
            endpoint: ep.clone(),
        });
    }
    let sid = ep.sid;

    let local_type = session
        .local_types
        .get(&ep)
        .ok_or_else(|| Fault::TypeViolation {
            expected: telltale_types::ValType::Unit,
            actual: telltale_types::ValType::Unit,
            message: format!("{role}: no type registered"),
        })?
        .current
        .clone();

    match &local_type {
        LocalTypeR::Send {
            partner, branches, ..
        } => {
            let partner = partner.clone();
            let branches = branches.clone();

            let (_lbl, expected_type, continuation) = branches
                .iter()
                .find(|(l, _, _)| l.name == label)
                .ok_or_else(|| Fault::UnknownLabel {
                    label: label.to_string(),
                })?
                .clone();

            let offer_payload = Value::Str(label.to_string());
            let fast_path =
                SendDecisionFastPathInput::new(sid, role, &partner, label, Some(&offer_payload));
            let decision = if let Some(decision) =
                ctx.handler
                    .send_decision_fast_path(fast_path, &coro.regs, Some(&offer_payload))
            {
                decision.map_err(|e| Fault::Invoke { message: e })?
            } else {
                ctx.handler
                    .send_decision(SendDecisionInput {
                        sid,
                        role,
                        partner: &partner,
                        label,
                        state: &coro.regs,
                        payload: Some(offer_payload),
                    })
                    .map_err(|e| Fault::Invoke { message: e })?
            };
            if let SendDecision::Deliver(payload) = &decision {
                validate_payload(
                    ctx.config,
                    role,
                    "offer",
                    label,
                    expected_type.as_ref(),
                    payload,
                    false,
                )?;
            }
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

            let original = session
                .local_types
                .get(&ep)
                .map(|entry| &entry.original)
                .unwrap_or(&LocalTypeR::End);
            let (_resolved, type_update) = resolve_type_update(&continuation, original, &ep);

            Ok(StepPack {
                coro_update: CoroUpdate::AdvancePc,
                type_update,
                events: vec![
                    ObsEvent::Sent {
                        tick: ctx.tick,
                        edge: Edge::new(sid, role.to_string(), partner.clone()),
                        session: sid,
                        from: role.to_string(),
                        to: partner.clone(),
                        label: label.to_string(),
                    },
                    ObsEvent::Offered {
                        tick: ctx.tick,
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

fn step_close(
    session: &mut SessionState,
    ep: &Endpoint,
    sid: SessionId,
    tick: u64,
) -> Result<StepPack, Fault> {
    session.status = SessionStatus::Closed;
    session.buffers.clear();
    session.edge_traces.clear();
    session.epoch = session.epoch.saturating_add(1);

    Ok(StepPack {
        coro_update: CoroUpdate::AdvancePc,
        type_update: Some((ep.clone(), TypeUpdate::Remove)),
        events: vec![
            ObsEvent::Closed { tick, session: sid },
            ObsEvent::EpochAdvanced {
                tick,
                sid,
                epoch: session.epoch,
            },
        ],
    })
}

fn step_open(
    coro: &mut Coroutine,
    _role: &str,
    store: &ThreadedSessionStore,
    buffer_config: &BufferConfig,
    roles: &[String],
    local_types: &[(String, LocalTypeR)],
    handlers: &[((String, String), String)],
    dsts: &[(String, u16)],
    tick: u64,
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
    let sid = store.open(open_roles.clone(), buffer_config, &initial_types);
    let session = store.get(sid).ok_or_else(|| Fault::Close {
        message: "open session missing after allocation".to_string(),
    })?;
    {
        let mut session_guard = session.lock().expect("session lock poisoned");
        for ((sender, receiver), handler_id) in handlers {
            session_guard.edge_handlers.insert(
                Edge::new(sid, sender.clone(), receiver.clone()),
                handler_id.clone(),
            );
        }
    }

    for (_, _, reg) in &triples {
        if usize::from(*reg) >= coro.regs.len() {
            return Err(Fault::OutOfRegisters);
        }
    }
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

    Ok(StepPack {
        coro_update: CoroUpdate::AdvancePc,
        type_update: None,
        events: vec![ObsEvent::Opened {
            tick,
            session: sid,
            roles: if roles.is_empty() {
                open_roles
            } else {
                roles.to_vec()
            },
        }],
    })
}

