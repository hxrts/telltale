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

    let (partner, branches) = match &type_entry.current {
        LocalTypeR::Send {
            partner, branches, ..
        } => (partner.clone(), branches.clone()),
        other => {
            return Err(Fault::TypeViolation {
                expected: telltale_types::ValType::Unit,
                actual: telltale_types::ValType::Unit,
                message: format!("{role}: expected Send, got {other:?}"),
            });
        }
    };

    let (label, expected_type, continuation) =
        branches.first().ok_or_else(|| Fault::TypeViolation {
            expected: telltale_types::ValType::Unit,
            actual: telltale_types::ValType::Unit,
            message: format!("{role}: send has no branches"),
        })?;

    Ok(SendPrepared {
        ep,
        sid,
        partner,
        label: label.name.clone(),
        expected_type: expected_type.clone(),
        continuation: continuation.clone(),
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
) -> Result<StepPack, Fault> {
    let prepared = {
        let session_guard = session.lock().expect("threaded VM lock poisoned");
        step_send_prepare(coro, &session_guard, role, chan)?
    };

    let send_payload = coro
        .regs
        .get(usize::from(val_reg))
        .cloned()
        .ok_or(Fault::OutOfRegisters)?;
    let fast_path = SendDecisionFastPathInput::new(
        prepared.sid,
        role,
        &prepared.partner,
        &prepared.label,
        Some(&send_payload),
    );
    let decision = if let Some(decision) =
        ctx.handler
            .send_decision_fast_path(fast_path, &coro.regs, Some(&send_payload))
    {
        decision.map_err(|e| Fault::Invoke { message: e })?
    } else {
        ctx.handler
            .send_decision(SendDecisionInput {
                sid: prepared.sid,
                role,
                partner: &prepared.partner,
                label: &prepared.label,
                state: &coro.regs,
                payload: Some(send_payload),
            })
            .map_err(|e| Fault::Invoke { message: e })?
    };

    if ctx.crashed_sites.contains(role)
        || ctx.crashed_sites.contains(&prepared.partner)
        || ctx.timed_out_sites.contains_key(role)
        || ctx.timed_out_sites.contains_key(&prepared.partner)
        || ctx
            .partitioned_edges
            .contains(&(role.to_string(), prepared.partner.clone()))
    {
        return Ok(StepPack {
            coro_update: CoroUpdate::Block(BlockReason::Send {
                edge: Edge::new(prepared.sid, role.to_string(), prepared.partner.clone()),
            }),
            type_update: None,
            events: vec![],
        });
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
        )?;
    }
    let enqueue = match decision {
        SendDecision::Deliver(payload) => {
            let edge = Edge::new(prepared.sid, role.to_string(), prepared.partner.clone());
            let sequence_no = if matches!(
                ctx.config.communication_replay_mode,
                crate::communication_replay::CommunicationReplayMode::Off
            ) {
                // Off mode preserves legacy behavior and avoids replay bookkeeping.
                0
            } else {
                let mut model = ctx
                    .communication_consumption
                    .lock()
                    .expect("threaded VM lock poisoned");
                model.set_mode(ctx.config.communication_replay_mode);
                model.allocate_send_sequence(&edge)
            };
            let payload = if let Some(corruption) = maybe_corruption {
                ThreadedVM::apply_corruption(payload, corruption)
            } else {
                payload
            };
            let mut session_guard = session.lock().expect("threaded VM lock poisoned");
            session_guard
                .send_with_sequence(role, &prepared.partner, payload, sequence_no)
                .map_err(|e| Fault::Invoke { message: e })?
        }
        SendDecision::Drop | SendDecision::Defer => EnqueueResult::Dropped,
    };

    match enqueue {
        EnqueueResult::Ok => {}
        EnqueueResult::WouldBlock => {
            return Ok(StepPack {
                coro_update: CoroUpdate::Block(BlockReason::Send {
                    edge: Edge::new(prepared.sid, role.to_string(), prepared.partner.clone()),
                }),
                type_update: None,
                events: vec![],
            });
        }
        EnqueueResult::Full => {
            return Err(Fault::BufferFull {
                endpoint: prepared.ep.clone(),
            });
        }
        EnqueueResult::Dropped => {}
    }

    let (_resolved, type_update) =
        resolve_type_update(&prepared.continuation, &prepared.original, &prepared.ep);

    Ok(StepPack {
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
    })
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

    let (partner, branches) = match &type_entry.current {
        LocalTypeR::Recv {
            partner, branches, ..
        } => (partner.clone(), branches.clone()),
        other => {
            return Err(Fault::TypeViolation {
                expected: telltale_types::ValType::Unit,
                actual: telltale_types::ValType::Unit,
                message: format!("{role}: expected Recv, got {other:?}"),
            });
        }
    };

    let (label, expected_type, continuation) =
        branches.first().ok_or_else(|| Fault::TypeViolation {
            expected: telltale_types::ValType::Unit,
            actual: telltale_types::ValType::Unit,
            message: format!("{role}: recv has no branches"),
        })?;

    Ok(RecvPrepared {
        ep,
        sid,
        partner,
        label: label.name.clone(),
        expected_type: expected_type.clone(),
        continuation: continuation.clone(),
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
    if matches!(
        ctx.config.communication_replay_mode,
        crate::communication_replay::CommunicationReplayMode::Off
    ) {
        return Ok(());
    }
    let replay_label = crate::communication_replay::canonical_receive_label_context(
        &prepared.label,
        prepared.expected_type.as_ref(),
    );
    let identity = CommunicationIdentity::from_payload(
        edge,
        CommunicationStepKind::Receive,
        replay_label,
        val,
        sequence_no,
    );
    let consume = {
        let mut model = ctx
            .communication_consumption
            .lock()
            .expect("threaded VM lock poisoned");
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
        .expect("threaded VM lock poisoned")
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
) -> Result<StepPack, Fault> {
    let (prepared, edge, val, sequence_no) = {
        let mut session_guard = session.lock().expect("threaded VM lock poisoned");
        let prepared = step_recv_prepare(coro, &session_guard, role, chan)?;
        if !session_guard.has_message(&prepared.partner, role) {
            return Ok(blocked_recv_pack(&prepared, role));
        }

        let edge = Edge::new(prepared.sid, prepared.partner.clone(), role.to_string());
        let signed = session_guard
            .recv_verified_signed(&prepared.partner, role)
            .map_err(|message| Fault::VerificationFailed {
                edge: edge.clone(),
                message,
            })?
            .ok_or_else(|| Fault::ChannelClosed {
                endpoint: prepared.ep.clone(),
            })?;
        (prepared, edge, signed.payload, signed.sequence_no)
    };

    // Deterministic ordering: signature verification (above), then replay-consumption.
    consume_receive_replay_identity(&edge, &prepared, &val, sequence_no, ctx)?;

    validate_payload(
        ctx.config,
        role,
        "receive",
        &prepared.label,
        prepared.expected_type.as_ref(),
        &val,
        true,
    )?;

    ctx.handler
        .handle_recv(
            role,
            &prepared.partner,
            &prepared.label,
            &mut coro.regs,
            &val,
        )
        .map_err(|e| Fault::Invoke { message: e })?;

    let (_resolved, type_update) =
        resolve_type_update(&prepared.continuation, &prepared.original, &prepared.ep);

    Ok(StepPack {
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
    })
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
    legacy_dst: Option<u16>,
    handler: &dyn EffectHandler,
    tick: u64,
) -> Result<StepPack, Fault> {
    let _action_repr = match action {
        InvokeAction::Named(name) => name,
        InvokeAction::Reg(reg) => format!(
            "{:?}",
            coro.regs
                .get(usize::from(reg))
                .cloned()
                .ok_or(Fault::OutOfRegisters)?
        ),
    };
    if let Some(dst) = legacy_dst {
        if usize::from(dst) >= coro.regs.len() {
            return Err(Fault::OutOfRegisters);
        }
    }
    if session.edge_handlers.is_empty() && session.default_handler.is_empty() {
        return Err(Fault::Invoke {
            message: "no handler bound".to_string(),
        });
    }
    let coro_id = coro.id;
    handler
        .step(role, &mut coro.regs)
        .map_err(|e| Fault::Invoke { message: e })?;

    Ok(StepPack {
        coro_update: CoroUpdate::AdvancePc,
        type_update: None,
        events: vec![ObsEvent::Invoked {
            tick,
            coro_id,
            role: role.to_string(),
        }],
    })
}

fn guard_active(config: &VMConfig, layer: &str) -> Result<(), Fault> {
    if config.guard_layers.is_empty() {
        return Ok(());
    }
    match config.guard_layers.iter().find(|cfg| cfg.id == layer) {
        None => Err(Fault::Acquire {
            layer: layer.to_string(),
            message: "unknown layer".into(),
        }),
        Some(cfg) if !cfg.active => Err(Fault::Acquire {
            layer: layer.to_string(),
            message: "inactive layer".into(),
        }),
        Some(_) => Ok(()),
    }
}

fn step_acquire(
    coro: &mut Coroutine,
    input: GuardAcquireStep<'_>,
    ctx: &ThreadedStepCtx<'_>,
) -> Result<StepPack, Fault> {
    guard_active(ctx.config, input.layer)?;
    {
        let mut resources = ctx
            .guard_resources
            .lock()
            .expect("threaded VM lock poisoned");
        resources
            .entry(input.layer.to_string())
            .or_insert(Value::Unit);
    }
    let decision = ctx
        .handler
        .handle_acquire(input.sid, input.role, input.layer, &coro.regs)
        .map_err(|e| Fault::Acquire {
            layer: input.layer.to_string(),
            message: e,
        })?;
    match decision {
        crate::effect::AcquireDecision::Grant(evidence) => {
            let mut resources = ctx
                .guard_resources
                .lock()
                .expect("threaded VM lock poisoned");
            resources.insert(input.layer.to_string(), evidence.clone());
            drop(resources);

            let mut scoped_states = ctx
                .resource_states
                .lock()
                .expect("threaded VM lock poisoned");
            let state = scoped_states.entry(input.sid).or_default();
            let _commitment = state.commit(&evidence);
            Ok(StepPack {
                coro_update: CoroUpdate::AdvancePcWriteReg {
                    reg: input.dst,
                    val: evidence,
                },
                type_update: None,
                events: vec![ObsEvent::Acquired {
                    tick: ctx.tick,
                    session: input.ep.sid,
                    role: input.role.to_string(),
                    layer: input.layer.to_string(),
                }],
            })
        }
        crate::effect::AcquireDecision::Block => Ok(StepPack {
            coro_update: CoroUpdate::Block(BlockReason::AcquireDenied {
                layer: input.layer.to_string(),
            }),
            type_update: None,
            events: vec![],
        }),
    }
}

fn step_release(
    coro: &mut Coroutine,
    input: GuardReleaseStep<'_>,
    ctx: &ThreadedStepCtx<'_>,
) -> Result<StepPack, Fault> {
    guard_active(ctx.config, input.layer)?;
    {
        let mut resources = ctx
            .guard_resources
            .lock()
            .expect("threaded VM lock poisoned");
        resources
            .entry(input.layer.to_string())
            .or_insert(Value::Unit);
    }
    let ev = coro
        .regs
        .get(usize::from(input.evidence))
        .ok_or(Fault::OutOfRegisters)?
        .clone();
    ctx.handler
        .handle_release(input.sid, input.role, input.layer, &ev, &coro.regs)
        .map_err(|e| Fault::Acquire {
            layer: input.layer.to_string(),
            message: e,
        })?;
    {
        let mut resources = ctx
            .guard_resources
            .lock()
            .expect("threaded VM lock poisoned");
        resources.insert(input.layer.to_string(), ev.clone());
    }

    if let Some(state) = ctx
        .resource_states
        .lock()
        .expect("threaded VM lock poisoned")
        .get_mut(&input.sid)
    {
        state.consume(&ev).map_err(|message| Fault::Acquire {
            layer: input.layer.to_string(),
            message,
        })?;
    }
    Ok(StepPack {
        coro_update: CoroUpdate::AdvancePc,
        type_update: None,
        events: vec![ObsEvent::Released {
            tick: ctx.tick,
            session: input.ep.sid,
            role: input.role.to_string(),
            layer: input.layer.to_string(),
        }],
    })
}

fn step_fork(
    coro: &mut Coroutine,
    role: &str,
    sid: SessionId,
    ghost: u16,
    config: &VMConfig,
    tick: u64,
) -> Result<StepPack, Fault> {
    if !config.speculation_enabled {
        return Err(speculation_fault_disabled());
    }
    let ghost_val = coro
        .regs
        .get(usize::from(ghost))
        .ok_or(Fault::OutOfRegisters)?
        .clone();
    let ghost_sid = match ghost_val {
        Value::Nat(v) => usize::try_from(v).map_err(|_| Fault::TypeViolation {
            expected: telltale_types::ValType::Nat,
            actual: telltale_types::ValType::Nat,
            message: format!("{role}: fork ghost id out of range"),
        })?,
        _ => {
            return Err(Fault::TypeViolation {
                expected: telltale_types::ValType::Nat,
                actual: telltale_types::ValType::Unit,
                message: format!("{role}: fork expects nat ghost id"),
            })
        }
    };
    coro.spec_state = Some(crate::coroutine::SpeculationState {
        ghost_sid,
        depth: 0,
    });
    Ok(StepPack {
        coro_update: CoroUpdate::AdvancePc,
        type_update: None,
        events: vec![ObsEvent::Forked {
            tick,
            session: sid,
            ghost: ghost_sid,
        }],
    })
}
