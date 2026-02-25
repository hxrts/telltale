    let mut coro_guard = coro.lock().expect("coroutine lock poisoned");
    let pc = coro_guard.pc;
    let program = ctx
        .programs
        .get(coro_guard.program_id)
        .ok_or(Fault::PcOutOfBounds)?;
    if pc >= program.len() {
        return Err(Fault::PcOutOfBounds);
    }
    let instr = program[pc].clone();
    let role = coro_guard.role.clone();
    let sid = coro_guard.session_id;
    let ep = coro_guard
        .owned_endpoints
        .first()
        .cloned()
        .unwrap_or(Endpoint {
            sid,
            role: role.clone(),
        });

    monitor_precheck(ctx.step.config.monitor_mode, session, &ep, &role, &instr)?;
    if coro_guard.cost_budget < ctx.step.config.instruction_cost {
        return Err(Fault::OutOfCredits);
    }
    coro_guard.cost_budget -= ctx.step.config.instruction_cost;

    let pack = match instr {
        Instr::Send { chan, val } => {
            step_send(&mut coro_guard, session, &role, chan, val, &ctx.step)
        }
        Instr::Receive { chan, dst } => {
            step_recv(&mut coro_guard, session, &role, chan, dst, &ctx.step)
        }
        Instr::Halt => {
            let mut session_guard = session.lock().expect("session lock poisoned");
            step_halt(&mut session_guard, &ep, ctx.step.tick)
        }
        Instr::Jump { target } => Ok(StepPack {
            coro_update: CoroUpdate::SetPc(target),
            type_update: None,
            events: vec![],
        }),
        Instr::Yield => Ok(StepPack {
            coro_update: CoroUpdate::AdvancePc,
            type_update: None,
            events: vec![],
        }),
        Instr::Invoke { action, dst } => {
            let session_guard = session.lock().expect("session lock poisoned");
            step_invoke(
                &mut coro_guard,
                &session_guard,
                &role,
                action,
                dst,
                ctx.step.handler,
                ctx.step.tick,
            )
        }
        Instr::Acquire { layer, dst } => step_acquire(
            &mut coro_guard,
            GuardAcquireStep {
                ep: &ep,
                role: &role,
                sid,
                layer: &layer,
                dst,
            },
            &ctx.step,
        ),
        Instr::Release { layer, evidence } => step_release(
            &mut coro_guard,
            GuardReleaseStep {
                ep: &ep,
                role: &role,
                sid,
                layer: &layer,
                evidence,
            },
            &ctx.step,
        ),
        Instr::Fork { ghost } => step_fork(
            &mut coro_guard,
            &role,
            sid,
            ghost,
            ctx.step.config,
            ctx.step.tick,
        ),
        Instr::Join => step_join(&mut coro_guard, sid, ctx.step.tick),
        Instr::Abort => step_abort(&mut coro_guard, sid, ctx.step.tick),
        Instr::Transfer {
            endpoint,
            target,
            bundle,
        } => step_transfer(
            &mut coro_guard,
            &role,
            endpoint,
            target,
            bundle,
            ctx.step.tick,
        ),
        Instr::Tag { fact, dst } => step_tag(&mut coro_guard, &role, fact, dst, ctx.step.tick),
        Instr::Check {
            knowledge,
            target,
            dst,
        } => step_check(
            &mut coro_guard,
            ctx.step.config,
            &role,
            knowledge,
            target,
            dst,
            ctx.step.tick,
        ),
        Instr::Set { dst, val } => {
            let v = match val {
                crate::instr::ImmValue::Unit => Value::Unit,
                crate::instr::ImmValue::Nat(n) => Value::Nat(n),
                crate::instr::ImmValue::Bool(b) => Value::Bool(b),
                crate::instr::ImmValue::Str(s) => Value::Str(s),
            };
            Ok(StepPack {
                coro_update: CoroUpdate::AdvancePcWriteReg { reg: dst, val: v },
                type_update: None,
                events: vec![],
            })
        }
        Instr::Move { dst, src } => {
            let v = coro_guard.regs[usize::from(src)].clone();
            Ok(StepPack {
                coro_update: CoroUpdate::AdvancePcWriteReg { reg: dst, val: v },
                type_update: None,
                events: vec![],
            })
        }
        Instr::Choose { chan, ref table } => {
            let mut session_guard = session.lock().expect("session lock poisoned");
            step_choose(
                &mut coro_guard,
                &mut session_guard,
                &role,
                chan,
                table,
                &ctx.step,
            )
        }
        Instr::Offer { chan, ref label } => {
            let mut session_guard = session.lock().expect("session lock poisoned");
            step_offer(
                &mut coro_guard,
                &mut session_guard,
                &role,
                chan,
                label,
                &ctx.step,
            )
        }
        Instr::Spawn { target, ref args } => Ok(step_spawn(target, args)),
        Instr::Close {
            session: session_reg,
        } => {
            let mut session_guard = session.lock().expect("session lock poisoned");
            let close_ep = endpoint_from_reg(&coro_guard, session_reg)?;
            if !coro_guard.owned_endpoints.contains(&close_ep) {
                return Err(Fault::Close {
                    message: "endpoint not owned".to_string(),
                });
            }
            step_close(&mut session_guard, &close_ep, close_ep.sid, ctx.step.tick)
        }
        Instr::Open {
            ref roles,
            ref local_types,
            ref handlers,
            ref dsts,
        } => step_open(
            &mut coro_guard,
            &role,
            ctx.store,
            &ctx.step.config.buffer_config,
            roles,
            local_types,
            handlers,
            dsts,
            ctx.step.tick,
        ),
    }?;

    let output_hint = if pack.events.is_empty() {
        None
    } else {
        Some(
            ctx.step
                .handler
                .output_condition_hint(sid, role.as_str(), &coro_guard.regs)
                .unwrap_or(OutputConditionHint {
                    predicate_ref: "vm.observable_output".to_string(),
                    witness_ref: None,
                }),
        )
    };

    Ok((pack, output_hint))
}

fn monitor_precheck(
    mode: MonitorMode,
    session: &Arc<Mutex<SessionState>>,
    ep: &Endpoint,
    role: &str,
    instr: &Instr,
) -> Result<(), Fault> {
    if mode == MonitorMode::Off {
        return Ok(());
    }
    match instr {
        Instr::Send { .. } | Instr::Offer { .. } => {
            let session_guard = session.lock().expect("session lock poisoned");
            let local_type = session_guard
                .local_types
                .get(ep)
                .ok_or_else(|| Fault::TypeViolation {
                    expected: telltale_types::ValType::Unit,
                    actual: telltale_types::ValType::Unit,
                    message: format!("[monitor] {role}: no type registered"),
                })?
                .current
                .clone();
            if matches!(local_type, LocalTypeR::Send { .. }) {
                Ok(())
            } else {
                Err(Fault::TypeViolation {
                    expected: telltale_types::ValType::Unit,
                    actual: telltale_types::ValType::Unit,
                    message: format!("[monitor] {role}: expected Send state, got {local_type:?}"),
                })
            }
        }
        Instr::Receive { .. } => {
            let session_guard = session.lock().expect("session lock poisoned");
            let local_type = session_guard
                .local_types
                .get(ep)
                .ok_or_else(|| Fault::TypeViolation {
                    expected: telltale_types::ValType::Unit,
                    actual: telltale_types::ValType::Unit,
                    message: format!("[monitor] {role}: no type registered"),
                })?
                .current
                .clone();
            if matches!(local_type, LocalTypeR::Recv { .. }) {
                Ok(())
            } else {
                Err(Fault::TypeViolation {
                    expected: telltale_types::ValType::Unit,
                    actual: telltale_types::ValType::Unit,
                    message: format!("[monitor] {role}: expected Recv state, got {local_type:?}"),
                })
            }
        }
        Instr::Choose { table, .. } => {
            let mut labels = BTreeSet::new();
            if !table
                .iter()
                .map(|(label, _)| label)
                .all(|label| labels.insert(label.clone()))
            {
                return Err(Fault::Speculation {
                    message: "[monitor] structural precheck failed: duplicate choose labels"
                        .to_string(),
                });
            }
            let session_guard = session.lock().expect("session lock poisoned");
            let local_type = session_guard
                .local_types
                .get(ep)
                .ok_or_else(|| Fault::TypeViolation {
                    expected: telltale_types::ValType::Unit,
                    actual: telltale_types::ValType::Unit,
                    message: format!("[monitor] {role}: no type registered"),
                })?
                .current
                .clone();
            if matches!(local_type, LocalTypeR::Recv { .. }) {
                Ok(())
            } else {
                Err(Fault::TypeViolation {
                    expected: telltale_types::ValType::Unit,
                    actual: telltale_types::ValType::Unit,
                    message: format!("[monitor] {role}: expected Recv state, got {local_type:?}"),
                })
            }
        }
        Instr::Open { roles, dsts, .. } => {
            if roles.len() == dsts.len() {
                Ok(())
            } else {
                Err(Fault::Speculation {
                    message: "[monitor] structural precheck failed: open arity mismatch"
                        .to_string(),
                })
            }
        }
        _ => Ok(()),
    }
}

fn validate_payload(
    config: &VMConfig,
    role: &str,
    context: &str,
    label: &str,
    expected_type: Option<&ValType>,
    value: &Value,
    strict_requires_annotation: bool,
) -> Result<(), Fault> {
    if config.payload_validation_mode == crate::vm::PayloadValidationMode::Off {
        return Ok(());
    }

    let actual_type = runtime_value_val_type(value);
    let payload_bytes = runtime_value_wire_size_bytes(value);
    if payload_bytes > config.max_payload_bytes {
        return Err(Fault::TypeViolation {
            expected: expected_type.cloned().unwrap_or_else(|| actual_type.clone()),
            actual: actual_type,
            message: format!(
                "{role}: {context} payload '{label}' exceeds max_payload_bytes={} (actual={payload_bytes})",
                config.max_payload_bytes
            ),
        });
    }

    match expected_type {
        Some(expected) => {
            if runtime_value_matches_val_type(value, expected) {
                Ok(())
            } else {
                Err(Fault::TypeViolation {
                    expected: expected.clone(),
                    actual: actual_type,
                    message: format!(
                        "{role}: {context} payload '{label}' violated expected type {expected:?}"
                    ),
                })
            }
        }
        None
            if config.payload_validation_mode == crate::vm::PayloadValidationMode::StrictSchema
                && strict_requires_annotation =>
        {
            Err(Fault::TypeViolation {
                expected: ValType::Unit,
                actual: actual_type,
                message: format!(
                    "{role}: {context} payload '{label}' requires explicit ValType annotation in strict_schema mode"
                ),
            })
        }
        None => Ok(()),
    }
}

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
        let session_guard = session.lock().expect("session lock poisoned");
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
            let payload = if let Some(corruption) = maybe_corruption {
                ThreadedVM::apply_corruption(payload, corruption)
            } else {
                payload
            };
            let mut session_guard = session.lock().expect("session lock poisoned");
            session_guard
                .send(role, &prepared.partner, payload)
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
