fn guard_active(config: &VMConfig, layer: &str) -> Result<(), Fault> {
    if config.guard_layers.is_empty() {
        return Ok(());
    }
    match config.guard_layers.iter().find(|cfg| cfg.id == layer) {
        None => Err(Fault::Acquire {
            layer: layer.to_string(),
            failure: EffectFailure::invalid_input("unknown layer"),
        }),
        Some(cfg) if !cfg.active => Err(Fault::Acquire {
            layer: layer.to_string(),
            failure: EffectFailure::unavailable("inactive layer"),
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
        .handle_effect(EffectRequest::acquire(
            ctx.tick,
            input.sid,
            None,
            input.role,
            input.layer,
            &coro.regs,
        ))
        .into_value("acquire")
        .unwrap_or_else(EffectResult::failure)
        .expect_success(|| EffectFailure::contract_violation("handle_acquire returned blocked"))
        .map_err(|failure| Fault::Acquire {
            layer: input.layer.to_string(),
            failure,
        })?;
    match decision {
        Value::Unit => {
            let mut resources = ctx
                .guard_resources
                .lock()
                .expect("threaded VM lock poisoned");
            resources.insert(input.layer.to_string(), Value::Unit);
            drop(resources);

            let mut scoped_states = ctx
                .resource_states
                .lock()
                .expect("threaded VM lock poisoned");
            let state = scoped_states.entry(input.sid).or_default();
            let _commitment = state.commit(&Value::Unit);
            Ok(StepPack {
                coro_update: CoroUpdate::AdvancePcWriteReg {
                    reg: input.dst,
                    val: Value::Unit,
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
        evidence => {
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
        .handle_effect(EffectRequest::release(
            ctx.tick,
            input.sid,
            None,
            input.role,
            input.layer,
            &ev,
            &coro.regs,
        ))
        .into_unit("handle_release")
        .unwrap_or_else(EffectResult::failure)
        .expect_success(|| EffectFailure::contract_violation("handle_release returned blocked"))
        .map_err(|failure| Fault::Acquire {
            layer: input.layer.to_string(),
            failure,
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
            failure: EffectFailure::invalid_evidence(message),
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
