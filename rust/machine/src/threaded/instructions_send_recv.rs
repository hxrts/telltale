// Send and receive instructions for threaded mode.
struct SendPrepared {
    ep: Endpoint,
    sid: SessionId,
    partner: String,
    label: String,
    expected_type: Option<ValType>,
    continuation: LocalTypeR,
    original: LocalTypeR,
}

fn step_send_prepare(
    coro: &Coroutine,
    session: &SessionState,
    role: &str,
    chan: u16,
) -> Result<SendPrepared, Fault> {
    let ep = endpoint_from_reg(coro, chan)?;
    if !coro.owned_endpoints.contains(&ep) {
        return Err(Fault::ChannelClosed {
            endpoint: ep.clone(),
        });
    }
    let sid = ep.sid;
    let type_entry = session
        .local_types
        .get(&ep)
        .ok_or_else(|| Fault::TypeViolation {
            expected: telltale_types::ValType::Unit,
            actual: telltale_types::ValType::Unit,
            message: format!("{role}: no type registered"),
        })?;

    let (partner, label, expected_type, continuation) = match &type_entry.current {
        LocalTypeR::Send {
            partner, branches, ..
        } => {
            let (label, expected_type, continuation) =
                branches.first().ok_or_else(|| Fault::TypeViolation {
                    expected: telltale_types::ValType::Unit,
                    actual: telltale_types::ValType::Unit,
                    message: format!("{role}: send has no branches"),
                })?;
            (
                partner.clone(),
                label.name.clone(),
                expected_type.clone(),
                continuation.clone(),
            )
        }
        other => {
            return Err(Fault::TypeViolation {
                expected: telltale_types::ValType::Unit,
                actual: telltale_types::ValType::Unit,
                message: format!("{role}: expected Send, got {other:?}"),
            });
        }
    };

    Ok(SendPrepared {
        ep,
        sid,
        partner,
        label,
        expected_type,
        continuation,
        original: type_entry.original.clone(),
    })
}

#[allow(clippy::too_many_lines)]
fn step_send(
    coro: &mut Coroutine,
    session: &Arc<Mutex<SessionState>>,
    role: &str,
    chan: u16,
    val_reg: u16,
    ctx: &ThreadedStepCtx<'_>,
) -> Result<(StepPack, Vec<EffectObservation>), ThreadedExecFault> {
    let prepared = {
        let session_guard = session.lock().expect("threaded ProtocolMachine lock poisoned");
        step_send_prepare(coro, &session_guard, role, chan).map_err(ThreadedExecFault::new)?
    };

    let send_payload = coro
        .regs
        .get(usize::from(val_reg))
        .cloned()
        .ok_or_else(|| ThreadedExecFault::new(Fault::OutOfRegisters))?;
    let request = EffectRequest::send_decision(
        ctx.tick,
        prepared.sid,
        None,
        role,
        &prepared.partner,
        &prepared.label,
        &coro.regs,
        Some(send_payload),
    );
    let outcome = ctx.handler.handle_effect(request.clone());
    let observation = EffectObservation {
        request,
        outcome: outcome.clone(),
    };
    let decision = outcome
        .clone()
        .into_send_decision()
        .unwrap_or_else(EffectResult::failure)
        .expect_success(|| EffectFailure::contract_violation("send_decision returned blocked"))
        .map_err(|failure| {
            ThreadedExecFault::with_observation(Fault::Invoke { failure }, observation.clone())
        })?;

    if ctx.crashed_sites.contains(role)
        || ctx.crashed_sites.contains(&prepared.partner)
        || ctx.timed_out_sites.contains_key(role)
        || ctx.timed_out_sites.contains_key(&prepared.partner)
        || ctx
            .partitioned_edges
            .contains(&(role.to_string(), prepared.partner.clone()))
    {
        return Ok((
            StepPack {
                coro_update: CoroUpdate::Block(BlockReason::Send {
                    edge: Edge::new(prepared.sid, role.to_string(), prepared.partner.clone()),
                }),
                type_update: None,
                events: vec![],
            },
            vec![observation],
        ));
    }

    let maybe_corruption = ctx
        .corrupted_edges
        .get(&(role.to_string(), prepared.partner.clone()))
        .cloned();
    if let SendDecision::Deliver(payload) = &decision {
        validate_payload(
            ctx.config,
            role,
            "send",
            &prepared.label,
            prepared.expected_type.as_ref(),
            payload,
            true,
        )
        .map_err(|fault| ThreadedExecFault::with_observation(fault, observation.clone()))?;
    }
    let enqueue = match decision {
        SendDecision::Deliver(payload) => {
            let edge = Edge::new(prepared.sid, role.to_string(), prepared.partner.clone());
            let sequence_no = {
                let mut model = ctx
                    .communication_consumption
                    .lock()
                    .expect("threaded ProtocolMachine lock poisoned");
                model.set_mode(ctx.config.communication_replay_mode);
                model.allocate_send_sequence(&edge)
            };
            let payload = if let Some(corruption) = maybe_corruption {
                ThreadedProtocolMachine::apply_corruption(payload, corruption)
            } else {
                payload
            };
            let mut session_guard = session.lock().expect("threaded ProtocolMachine lock poisoned");
            session_guard
                .send_with_sequence(role, &prepared.partner, payload, sequence_no)
                .map_err(|e| {
                    ThreadedExecFault::with_observation(
                        Fault::Invoke {
                            failure: EffectFailure::invalid_input(e),
                        },
                        observation.clone(),
                    )
                })?
        }
        SendDecision::Drop | SendDecision::Defer => EnqueueResult::Dropped,
    };

    match enqueue {
        EnqueueResult::Ok => {}
        EnqueueResult::WouldBlock => {
            return Ok((
                StepPack {
                    coro_update: CoroUpdate::Block(BlockReason::Send {
                        edge: Edge::new(prepared.sid, role.to_string(), prepared.partner.clone()),
                    }),
                    type_update: None,
                    events: vec![],
                },
                vec![observation],
            ));
        }
        EnqueueResult::Full => {
            return Err(ThreadedExecFault::with_observation(
                Fault::BufferFull {
                    endpoint: prepared.ep.clone(),
                },
                observation,
            ));
        }
        EnqueueResult::Dropped => {}
    }

    let (_resolved, type_update) =
        resolve_type_update(&prepared.continuation, &prepared.original, &prepared.ep);

    Ok((
        StepPack {
            coro_update: CoroUpdate::AdvancePc,
            type_update,
            events: vec![ObsEvent::Sent {
                tick: ctx.tick,
                edge: Edge::new(prepared.sid, role.to_string(), prepared.partner.clone()),
                session: prepared.sid,
                from: role.to_string(),
                to: prepared.partner,
                label: prepared.label,
            }],
        },
        vec![observation],
    ))
}

struct RecvPrepared {
    ep: Endpoint,
    sid: SessionId,
    partner: String,
    label: String,
    expected_type: Option<ValType>,
    continuation: LocalTypeR,
    original: LocalTypeR,
}

fn step_recv_prepare(
    coro: &Coroutine,
    session: &SessionState,
    role: &str,
    chan: u16,
) -> Result<RecvPrepared, Fault> {
    let ep = endpoint_from_reg(coro, chan)?;
    if !coro.owned_endpoints.contains(&ep) {
        return Err(Fault::ChannelClosed {
            endpoint: ep.clone(),
        });
    }
    let sid = ep.sid;

    let type_entry = session
        .local_types
        .get(&ep)
        .ok_or_else(|| Fault::TypeViolation {
            expected: telltale_types::ValType::Unit,
            actual: telltale_types::ValType::Unit,
            message: format!("{role}: no type registered"),
        })?;

    let (partner, label, expected_type, continuation) = match &type_entry.current {
        LocalTypeR::Recv {
            partner, branches, ..
        } => {
            let (label, expected_type, continuation) =
                branches.first().ok_or_else(|| Fault::TypeViolation {
                    expected: telltale_types::ValType::Unit,
                    actual: telltale_types::ValType::Unit,
                    message: format!("{role}: recv has no branches"),
                })?;
            (
                partner.clone(),
                label.name.clone(),
                expected_type.clone(),
                continuation.clone(),
            )
        }
        other => {
            return Err(Fault::TypeViolation {
                expected: telltale_types::ValType::Unit,
                actual: telltale_types::ValType::Unit,
                message: format!("{role}: expected Recv, got {other:?}"),
            });
        }
    };

    Ok(RecvPrepared {
        ep,
        sid,
        partner,
        label,
        expected_type,
        continuation,
        original: type_entry.original.clone(),
    })
}

fn blocked_recv_pack(prepared: &RecvPrepared, role: &str) -> StepPack {
    StepPack {
        coro_update: CoroUpdate::Block(BlockReason::Recv {
            edge: Edge::new(prepared.sid, prepared.partner.clone(), role.to_string()),
            token: ProgressToken::for_endpoint(prepared.ep.clone()),
        }),
        type_update: None,
        events: vec![],
    }
}

fn consume_receive_replay_identity(
    edge: &Edge,
    prepared: &RecvPrepared,
    val: &Value,
    sequence_no: u64,
    ctx: &ThreadedStepCtx<'_>,
) -> Result<(), Fault> {
    let replay_label = crate::communication_replay::canonical_receive_label_context(
        &prepared.label,
        prepared.expected_type.as_ref(),
    );
    let identity = crate::communication_replay::CommunicationIdentitySeed::new(
        edge,
        CommunicationStepKind::Receive,
        replay_label,
    )
    .build(val, sequence_no);
    let consume = {
        let mut model = ctx
            .communication_consumption
            .lock()
            .expect("threaded ProtocolMachine lock poisoned");
        model.set_mode(ctx.config.communication_replay_mode);
        model.consume_receive(&identity)
    }
    .map_err(|err| {
        let tag = err.tag();
        let message = match err {
            CommunicationReplayError::SequenceMismatch { expected, actual } => {
                format!("{tag}: expected={expected}, actual={actual}")
            }
            CommunicationReplayError::DuplicateIdentity { .. } => tag.to_string(),
        };
        Fault::VerificationFailed {
            edge: edge.clone(),
            message,
        }
    })?;
    ctx.communication_consumption_artifacts
        .lock()
        .expect("threaded ProtocolMachine lock poisoned")
        .push(CommunicationConsumptionArtifact {
            tick: ctx.tick,
            identity,
            mode: consume.mode,
            pre_root: consume.pre_root,
            post_root: consume.post_root,
        });
    Ok(())
}

fn step_recv(
    coro: &mut Coroutine,
    session: &Arc<Mutex<SessionState>>,
    role: &str,
    chan: u16,
    dst_reg: u16,
    ctx: &ThreadedStepCtx<'_>,
) -> Result<(StepPack, Vec<EffectObservation>), ThreadedExecFault> {
    let (prepared, edge, val, sequence_no) = {
        let mut session_guard = session.lock().expect("threaded ProtocolMachine lock poisoned");
        let prepared =
            step_recv_prepare(coro, &session_guard, role, chan).map_err(ThreadedExecFault::new)?;
        if !session_guard.has_message(&prepared.partner, role) {
            return Ok((blocked_recv_pack(&prepared, role), Vec::new()));
        }

        let edge = Edge::new(prepared.sid, prepared.partner.clone(), role.to_string());
        let signed = session_guard
            .recv_verified_signed(&prepared.partner, role)
            .map_err(|message| {
                ThreadedExecFault::new(Fault::VerificationFailed {
                    edge: edge.clone(),
                    message,
                })
            })?
            .ok_or_else(|| Fault::ChannelClosed {
                endpoint: prepared.ep.clone(),
            })
            .map_err(ThreadedExecFault::new)?;
        (prepared, edge, signed.payload, signed.sequence_no)
    };

    // Deterministic ordering: signature verification (above), then replay-consumption.
    consume_receive_replay_identity(&edge, &prepared, &val, sequence_no, ctx)
        .map_err(ThreadedExecFault::new)?;

    validate_payload(
        ctx.config,
        role,
        "receive",
        &prepared.label,
        prepared.expected_type.as_ref(),
        &val,
        true,
    )
    .map_err(ThreadedExecFault::new)?;

    let request = EffectRequest::receive(
        ctx.tick,
        Some(prepared.sid),
        None,
        role,
        &prepared.partner,
        &prepared.label,
        &coro.regs,
        val.clone(),
    );
    let recv_outcome = ctx.handler.handle_effect(request.clone());
    let observation = EffectObservation {
        request,
        outcome: recv_outcome.clone(),
    };
    if let Some(EffectResponse::Receive { state }) = recv_outcome.response.clone() {
        coro.regs = state;
    }
    recv_outcome
        .clone()
        .into_unit("handle_recv")
        .unwrap_or_else(EffectResult::failure)
        .expect_success(|| EffectFailure::contract_violation("handle_recv returned blocked"))
        .map_err(|failure| {
            ThreadedExecFault::with_observation(Fault::Invoke { failure }, observation.clone())
        })?;

    let (_resolved, type_update) =
        resolve_type_update(&prepared.continuation, &prepared.original, &prepared.ep);

    Ok((
        StepPack {
            coro_update: CoroUpdate::AdvancePcWriteReg { reg: dst_reg, val },
            type_update,
            events: vec![ObsEvent::Received {
                tick: ctx.tick,
                edge,
                session: prepared.sid,
                from: prepared.partner,
                to: role.to_string(),
                label: prepared.label,
            }],
        },
        vec![observation],
    ))
}

fn step_halt(session: &mut SessionState, ep: &Endpoint, _tick: u64) -> Result<StepPack, Fault> {
    if let Some(lt) = session.local_types.get(ep) {
        if !matches!(lt.current, LocalTypeR::End) {
            // V1: permissive
        }
    }
    Ok(StepPack {
        coro_update: CoroUpdate::Halt,
        type_update: Some((ep.clone(), TypeUpdate::Remove)),
        events: vec![],
    })
}

fn step_spawn(target: PC, args: &[u16]) -> StepPack {
    StepPack {
        coro_update: CoroUpdate::AdvancePcSpawnChild {
            target,
            args: args.to_vec(),
        },
        type_update: None,
        events: vec![],
    }
}

fn step_invoke(
    coro: &mut Coroutine,
    session: &SessionState,
    role: &str,
    action: InvokeAction,
    handler: &dyn EffectHandler,
    tick: u64,
) -> Result<(StepPack, Vec<EffectObservation>), ThreadedExecFault> {
    let _action_repr = match action {
        InvokeAction::Named(name) => name,
        InvokeAction::Reg(reg) => format!(
            "{:?}",
            coro.regs
                .get(usize::from(reg))
                .cloned()
                .ok_or_else(|| ThreadedExecFault::new(Fault::OutOfRegisters))?
        ),
    };
    if !session.has_bound_handler() {
        return Err(ThreadedExecFault::new(Fault::Invoke {
            failure: EffectFailure::contract_violation("no handler bound"),
        }));
    }
    let coro_id = coro.id;
    let request = EffectRequest::invoke_step(
        tick,
        Some(session.sid),
        None,
        role,
        &coro.regs,
    );
    // Threaded step paths share the same canonical request admissibility rules.
    let step_outcome = handler.handle_effect(request.clone());
    let observation = EffectObservation {
        request,
        outcome: step_outcome.clone(),
    };
    if let Some(EffectResponse::InvokeStep { state }) = step_outcome.response.clone() {
        coro.regs = state;
    }
    step_outcome
        .clone()
        .into_unit("invoke_step")
        .unwrap_or_else(EffectResult::failure)
        .expect_success(|| EffectFailure::contract_violation("step returned blocked"))
        .map_err(|failure| {
            ThreadedExecFault::with_observation(Fault::Invoke { failure }, observation.clone())
        })?;

    Ok((
        StepPack {
            coro_update: CoroUpdate::AdvancePc,
            type_update: None,
            events: vec![ObsEvent::Invoked {
                tick,
                coro_id,
                role: role.to_string(),
            }],
        },
        vec![observation],
    ))
}
