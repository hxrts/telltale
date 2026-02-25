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

fn step_recv(
    coro: &mut Coroutine,
    session: &Arc<Mutex<SessionState>>,
    role: &str,
    chan: u16,
    dst_reg: u16,
    ctx: &ThreadedStepCtx<'_>,
) -> Result<StepPack, Fault> {
    let (prepared, edge, val) = {
        let mut session_guard = session.lock().expect("session lock poisoned");
        let prepared = step_recv_prepare(coro, &session_guard, role, chan)?;
        if !session_guard.has_message(&prepared.partner, role) {
            return Ok(StepPack {
                coro_update: CoroUpdate::Block(BlockReason::Recv {
                    edge: Edge::new(prepared.sid, prepared.partner.clone(), role.to_string()),
                    token: ProgressToken::for_endpoint(prepared.ep.clone()),
                }),
                type_update: None,
                events: vec![],
            });
        }

        let edge = Edge::new(prepared.sid, prepared.partner.clone(), role.to_string());
        let val = session_guard
            .recv_verified(&prepared.partner, role)
            .map_err(|message| Fault::VerificationFailed {
                edge: edge.clone(),
                message,
            })?
            .ok_or_else(|| Fault::ChannelClosed {
                endpoint: prepared.ep.clone(),
            })?;
        (prepared, edge, val)
    };

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
    if session.edge_handlers.is_empty() {
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
            .expect("guard resources lock poisoned");
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
                .expect("guard resources lock poisoned");
            resources.insert(input.layer.to_string(), evidence.clone());
            drop(resources);

            let mut scoped_states = ctx
                .resource_states
                .lock()
                .expect("resource state lock poisoned");
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
            .expect("guard resources lock poisoned");
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
            .expect("guard resources lock poisoned");
        resources.insert(input.layer.to_string(), ev.clone());
    }

    if let Some(state) = ctx
        .resource_states
        .lock()
        .expect("resource state lock poisoned")
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
