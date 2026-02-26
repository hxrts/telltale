fn role_fingerprint(role: &str) -> u64 {
    const FNV_OFFSET: u64 = 0xcbf29ce484222325;
    const FNV_PRIME: u64 = 0x100000001b3;
    let mut hash = FNV_OFFSET;
    for byte in role.as_bytes() {
        hash ^= u64::from(*byte);
        hash = hash.wrapping_mul(FNV_PRIME);
    }
    hash
}

fn lock_with_contention<'a, T>(
    arc: &'a Arc<Mutex<T>>,
    metrics: &mut ContentionMetrics,
) -> std::sync::MutexGuard<'a, T> {
    match arc.try_lock() {
        Ok(guard) => guard,
        Err(TryLockError::Poisoned(poisoned)) => poisoned.into_inner(),
        Err(TryLockError::WouldBlock) => {
            metrics.lock_contention_events = metrics.lock_contention_events.saturating_add(1);
            metrics.mutex_lock_contention_events =
                metrics.mutex_lock_contention_events.saturating_add(1);
            arc.lock().expect("mutex lock poisoned after contention")
        }
    }
}

struct ThreadedStepCtx<'a> {
    config: &'a VMConfig,
    guard_resources: &'a Arc<Mutex<BTreeMap<String, Value>>>,
    resource_states: &'a Arc<Mutex<BTreeMap<SessionId, ResourceState>>>,
    communication_consumption: &'a Arc<Mutex<DefaultCommunicationConsumption>>,
    communication_consumption_artifacts: &'a Arc<Mutex<Vec<CommunicationConsumptionArtifact>>>,
    crashed_sites: &'a BTreeSet<String>,
    partitioned_edges: &'a BTreeSet<(String, String)>,
    corrupted_edges: &'a BTreeMap<(String, String), CorruptionType>,
    timed_out_sites: &'a BTreeMap<String, u64>,
    handler: &'a dyn EffectHandler,
    tick: u64,
}

struct ThreadedExecCtx<'a> {
    store: &'a ThreadedSessionStore,
    programs: &'a [Vec<Instr>],
    step: ThreadedStepCtx<'a>,
}

#[derive(Clone, Copy)]
struct GuardAcquireStep<'a> {
    ep: &'a Endpoint,
    role: &'a str,
    sid: SessionId,
    layer: &'a str,
    dst: u16,
}

#[derive(Clone, Copy)]
struct GuardReleaseStep<'a> {
    ep: &'a Endpoint,
    role: &'a str,
    sid: SessionId,
    layer: &'a str,
    evidence: u16,
}

#[allow(clippy::too_many_lines)]
fn exec_instr(
    coro: &Arc<Mutex<Coroutine>>,
    session: &Arc<Mutex<SessionState>>,
    ctx: &ThreadedExecCtx<'_>,
) -> Result<(StepPack, Option<OutputConditionHint>), Fault> {
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
            step_close(
                &mut session_guard,
                &close_ep,
                close_ep.sid,
                ctx.step.tick,
                &ctx.step,
            )
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
