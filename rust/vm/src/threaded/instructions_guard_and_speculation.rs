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
            });
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
