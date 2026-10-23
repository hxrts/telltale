// Canonical nominal issuance belongs to the main owner before worker dispatch.
// Workers borrow only the original coroutine holder and actual session state.
impl ThreadedProtocolMachine {
    // A previously returned value needs no new callback observation. Settle its
    // original occurrence as well when publication capacity terminally refuses.
    fn settle_nominal_publication_failure(
        &mut self,
        coroutine: &Arc<Mutex<Coroutine>>,
        failure: &EffectFailure,
    ) -> Result<(), ProtocolMachineError> {
        let original = {
            let coro = coroutine
                .lock()
                .expect("threaded ProtocolMachine lock poisoned");
            coro.nominal_continuation.as_ref().and_then(|pending| {
                if pending.validation_failure.as_ref() == Some(failure) {
                    pending
                        .returned
                        .clone()
                        .map(|value| (pending.invocation, value))
                } else {
                    None
                }
            })
        };
        let Some((invocation, returned)) = original else {
            return Ok(());
        };
        if self.outstanding_effects.iter().any(|effect| {
            effect.effect_id == invocation
                && matches!(
                    effect.status,
                    OutstandingEffectStatus::Pending | OutstandingEffectStatus::Blocked
                )
        }) {
            self.complete_runtime_effect(
                invocation,
                OutstandingEffectStatus::Failed,
                json!({"status":"failure", "failure":failure, "retained_result":returned}),
            )?;
        }
        Ok(())
    }
}

fn validate_threaded_nominal_owner(
    coroutine: &Coroutine,
    session: &mut SessionState,
    call: &crate::nominal_command::NominalCommandCall,
    tick: u64,
    handler_identity: &str,
) -> Result<(), EffectFailure> {
    let pending = coroutine.nominal_continuation.as_ref().ok_or_else(|| {
        EffectFailure::contract_violation("no original pre-dispatch nominal occurrence")
    })?;
    pending.require_handler_identity(handler_identity)?;
    pending.validate_identity_at(coroutine.session_id, coroutine.id, coroutine.pc, call, tick)?;
    if !call.supported_agreement()
        || coroutine.role != call.role
        || !coroutine.owned_endpoints.contains(&Endpoint {
            sid: coroutine.session_id,
            role: call.role.clone(),
        })
        || call.result == 0
        || coroutine.regs.get(usize::from(call.result)).is_none()
        || !matches!(&pending.owner.capability().scope, OwnershipScope::Session)
        || !session.has_bound_handler()
    {
        return Err(EffectFailure::contract_violation(
            "nominal invocation lost its original role, endpoint or result destination",
        ));
    }
    SessionState::validate_mutating_owner(session, pending.owner.capability())
        .map_err(|error| EffectFailure::contract_violation(error.to_string()))
}

impl ThreadedProtocolMachine {
    fn prepare_nominal_pick(
        &mut self,
        pick: &Picked,
        handler_identity: &str,
        tick: u64,
    ) -> Result<(), Fault> {
        let mut coroutine = pick
            .coro
            .lock()
            .expect("threaded ProtocolMachine lock poisoned");
        let Some(Instr::Invoke {
            action: InvokeAction::NominalCommand(call),
        }) = self
            .programs
            .get(coroutine.program_id)
            .and_then(|program| program.get(coroutine.pc))
            .cloned()
        else {
            return Ok(());
        };
        let fail = |failure| Fault::Invoke { failure };
        {
            let resident = pick
                .session
                .lock()
                .expect("threaded ProtocolMachine lock poisoned");
            crate::operation_lifecycle::validate_enclosing_operation(
                &coroutine,
                &resident,
                &self.operation_instances,
                &self.progress_contracts,
                tick,
            )
            .map_err(crate::operation_lifecycle::transition_fault)?;
        }
        let required = self
            .programs
            .get(coroutine.program_id)
            .is_some_and(|program| {
                crate::operation_lifecycle::requires_operation_context(program, coroutine.pc)
            });
        if required
            && coroutine
                .operation_continuation
                .as_ref()
                .is_none_or(|original| original.resolved || original.invalidated)
        {
            return Err(fail(EffectFailure::contract_violation(
                "source child has no actual original enclosing continuation",
            )));
        }
        if coroutine.cost_budget < self.config.instruction_cost {
            return Err(Fault::OutOfCredits);
        }
        if coroutine.nominal_continuation.is_none() {
            self.issue_threaded_nominal_command(
                pick,
                &mut coroutine,
                &call,
                handler_identity,
                tick,
            )?;
        }
        self.validate_nominal_pick(&coroutine, &call, handler_identity)
            .map_err(fail)?;
        let mut session = pick
            .session
            .lock()
            .expect("threaded ProtocolMachine lock poisoned");
        validate_threaded_nominal_owner(&coroutine, &mut session, &call, tick, handler_identity)
            .map_err(fail)
    }

    fn admit_threaded_nominal_owner(
        &self,
        pick: &Picked,
        coroutine: &Coroutine,
        call: &crate::nominal_command::NominalCommandCall,
    ) -> Result<crate::owned::OwnedSession, Fault> {
        let fail = |failure| Fault::Invoke { failure };
        let sid = coroutine.session_id;
        let owner = coroutine.nominal_owner.clone().ok_or_else(|| {
            fail(EffectFailure::contract_violation(
                "nominal invocation requires its original issued owner",
            ))
        })?;
        if owner.session_id() != sid
            || !matches!(&owner.capability().scope, OwnershipScope::Session)
        {
            return Err(fail(EffectFailure::contract_violation(
                "nominal owner does not cover its original session",
            )));
        }
        {
            let mut session = pick
                .session
                .lock()
                .expect("threaded ProtocolMachine lock poisoned");
            if !session.has_bound_handler() {
                return Err(fail(EffectFailure::contract_violation("no handler bound")));
            }
            SessionState::validate_mutating_owner(&mut session, owner.capability())
                .map_err(|error| fail(EffectFailure::contract_violation(error.to_string())))?;
        }
        if !call.supported_agreement()
            || call.role != coroutine.role
            || call.result == 0
            || coroutine.regs.get(usize::from(call.result)).is_none()
            || !coroutine.owned_endpoints.contains(&Endpoint {
                sid,
                role: call.role.clone(),
            })
        {
            return Err(fail(EffectFailure::contract_violation(
                "invalid nominal role, endpoint or result destination",
            )));
        }
        Ok(owner)
    }

    fn issue_threaded_nominal_command(
        &mut self,
        pick: &Picked,
        coroutine: &mut Coroutine,
        call: &crate::nominal_command::NominalCommandCall,
        handler_identity: &str,
        tick: u64,
    ) -> Result<(), Fault> {
        use crate::nominal_command::{NominalCommandRequest, PendingNominalContinuation};
        let fail = |failure| Fault::Invoke { failure };
        let sid = coroutine.session_id;
        let owner = self.admit_threaded_nominal_owner(pick, coroutine, call)?;
        tick.checked_add(call.budget_ticks.get()).ok_or_else(|| {
            fail(EffectFailure::contract_violation(
                "selected original nominal progress endpoint overflowed",
            ))
        })?;
        if self.next_effect_id == u64::MAX {
            return Err(fail(EffectFailure::contract_violation(
                "nominal occurrence identifiers exhausted",
            )));
        }
        let request = EffectRequest::nominal_command(
            tick,
            NominalCommandRequest {
                invocation: self.next_effect_id,
                session: sid,
                coroutine: coroutine.id,
                declaration: call.declaration.clone(),
                role: call.role.clone(),
            },
            call.budget_ticks.get(),
        );
        self.ensure_effect_request_allowed(&request).map_err(fail)?;
        let invocation = self
            .issue_runtime_effect_with_budget(
                "nominal_command",
                Some(sid),
                handler_identity,
                serde_json::to_value(&request).expect("typed nominal request serializes"),
                Some(call.budget_ticks.get()),
            )
            .map_err(|failure| Fault::Invoke { failure })?;
        let effect = self
            .outstanding_effects
            .iter_mut()
            .find(|effect| effect.effect_id == invocation)
            .expect("original issued");
        effect.effect_interface = Some(call.declaration.interface.clone());
        effect.effect_operation = Some(call.declaration.operation.clone());
        let operation = self
            .operation_instances
            .iter_mut()
            .find(|operation| operation.operation_id == Self::effect_operation_id(invocation))
            .expect("original issued operation");
        operation.kind = call.enclosing_operation.clone();
        operation.agreement_profile = Some(call.agreement_profile.clone());
        operation.requires_proof = true;
        let child = self
            .outstanding_effects
            .iter()
            .find(|effect| effect.effect_id == invocation)
            .expect("original issued child");
        crate::operation_lifecycle::admit_source_child(
            coroutine,
            &mut self.operation_instances,
            child,
            call,
        )
        .map_err(crate::operation_lifecycle::transition_fault)?;
        coroutine.nominal_continuation = Some(PendingNominalContinuation {
            invocation,
            coroutine: coroutine.id,
            pc: coroutine.pc,
            call: call.clone(),
            owner,
            issued_at: tick,
            handler_identity: handler_identity.to_string(),
            validation_failure: None,
            returned: None,
        });
        Ok(())
    }

    fn validate_nominal_pick(
        &self,
        coroutine: &Coroutine,
        call: &crate::nominal_command::NominalCommandCall,
        handler_identity: &str,
    ) -> Result<(), EffectFailure> {
        let required = self
            .programs
            .get(coroutine.program_id)
            .is_some_and(|program| {
                crate::operation_lifecycle::requires_operation_context(program, coroutine.pc)
            });
        if required
            && coroutine
                .operation_continuation
                .as_ref()
                .is_none_or(|original| original.resolved || original.invalidated)
        {
            return Err(EffectFailure::contract_violation(
                "source commit has no actual original enclosing continuation",
            ));
        }
        let pending = coroutine
            .nominal_continuation
            .as_ref()
            .ok_or_else(|| EffectFailure::contract_violation("no original nominal continuation"))?;
        let effect = self
            .outstanding_effects
            .iter()
            .find(|effect| effect.effect_id == pending.invocation)
            .ok_or_else(|| {
                EffectFailure::contract_violation("original nominal occurrence is missing")
            })?;
        let operation = self
            .operation_instances
            .iter()
            .find(|operation| {
                operation.operation_id == Self::effect_operation_id(pending.invocation)
            })
            .ok_or_else(|| {
                EffectFailure::contract_violation("original nominal operation is missing")
            })?;
        if effect.session != Some(coroutine.session_id)
            || effect.owner_id.as_deref() != Some(pending.owner.capability().owner_id.as_str())
            || effect.ordering_key != pending.issued_at
            || effect.handler_identity != pending.handler_identity
            || effect.budget_ticks != Some(call.budget_ticks.get())
            || effect.handler_identity != handler_identity
            || !matches!(
                effect.status,
                OutstandingEffectStatus::Pending | OutstandingEffectStatus::Blocked
            )
            || operation.kind != call.enclosing_operation
            || operation.agreement_profile.as_ref() != Some(&call.agreement_profile)
            || operation.budget_ticks != Some(call.budget_ticks.get())
            || !operation.requires_proof
        {
            return Err(EffectFailure::contract_violation(
                "original nominal occurrence, handler or operation policy changed",
            ));
        }
        Ok(())
    }

    fn validate_nominal_commit(
        &self,
        coroutine: &Arc<Mutex<Coroutine>>,
        session: &Arc<Mutex<SessionState>>,
        handler_identity: &str,
    ) -> Result<(), Fault> {
        let coro = coroutine
            .lock()
            .expect("threaded ProtocolMachine lock poisoned");
        let pending = coro
            .nominal_continuation
            .as_ref()
            .ok_or_else(|| Fault::Invoke {
                failure: EffectFailure::contract_violation(
                    "original nominal continuation missing at commit",
                ),
            })?;
        self.validate_nominal_pick(&coro, &pending.call, handler_identity)
            .map_err(|failure| Fault::Invoke { failure })?;
        let mut session = session
            .lock()
            .expect("threaded ProtocolMachine lock poisoned");
        crate::operation_lifecycle::validate_enclosing_operation(
            &coro,
            &session,
            &self.operation_instances,
            &self.progress_contracts,
            self.clock.tick,
        )
        .map_err(crate::operation_lifecycle::transition_fault)?;
        validate_threaded_nominal_owner(
            &coro,
            &mut session,
            &pending.call,
            self.clock.tick,
            handler_identity,
        )
        .map_err(|failure| Fault::Invoke { failure })
    }

    fn commit_nominal_result(
        &mut self,
        coroutine: &Arc<Mutex<Coroutine>>,
        session: &Arc<Mutex<SessionState>>,
        handler_identity: &str,
    ) -> Result<(), Fault> {
        let mut coro = coroutine
            .lock()
            .expect("threaded ProtocolMachine lock poisoned");
        let pending = coro
            .nominal_continuation
            .as_ref()
            .expect("original validated at commit");
        pending
            .require_handler_identity(handler_identity)
            .map_err(|failure| Fault::Invoke { failure })?;
        let result = pending.returned.clone().ok_or_else(|| Fault::Invoke {
            failure: EffectFailure::contract_violation("nominal result is still pending"),
        })?;
        let invocation = pending.invocation;
        let destination = pending.call.result;
        let (pc, value) = match &result {
            Ok(value) => (pending.call.on_ok, value.value()),
            Err(error) => (pending.call.on_err, Value::Str(error.clone())),
        };
        if coro.regs.get(usize::from(destination)).is_none() {
            return Err(Fault::OutOfRegisters);
        }
        if let Ok(value) = &result {
            value
                .require_declaration(&pending.call.declaration)
                .map_err(|failure| Fault::Invoke { failure })?;
            if let crate::nominal_command::NominalCommandValue::Readiness(witness) = value {
                // Consume from the same original session only after all output/WAL gates.
                let selected = self
                    .sessions
                    .sessions
                    .read()
                    .map_err(|_| Fault::Invoke {
                        failure: EffectFailure::contract_violation(
                            "original session registry lock poisoned",
                        ),
                    })?
                    .get(&pending.owner.session_id())
                    .cloned()
                    .ok_or_else(|| Fault::Invoke {
                        failure: EffectFailure::contract_violation(
                            "original readiness session is missing",
                        ),
                    })?;
                if !Arc::ptr_eq(&selected, session) {
                    return Err(Fault::Invoke {
                        failure: EffectFailure::contract_violation(
                            "original readiness session residency changed",
                        ),
                    });
                }
                self.sessions
                    .with_owned_session_at(
                        pending.owner.session_id(),
                        Some(self.clock.tick),
                        |resident| {
                            resident.consume_readiness_witness(pending.owner.capability(), witness)
                        },
                    )
                    .map_err(|error| Fault::Invoke {
                        failure: EffectFailure::contract_violation(error.to_string()),
                    })?;
            }
        }
        self.complete_runtime_effect(
            invocation,
            OutstandingEffectStatus::Succeeded,
            json!({"status":"success","result":result}),
        )
        .map_err(|error| Fault::Invoke {
            failure: EffectFailure::contract_violation(error.to_string()),
        })?;
        coro.regs[usize::from(destination)] = value;
        coro.pc = pc;
        coro.status = CoroStatus::Ready;
        coro.nominal_continuation = None;
        Ok(())
    }
}

// The same selected Arc remains resident in Picked/main custody while foreign
// callbacks execute without either coroutine or session mutex held.
fn exec_nominal_instr(
    coroutine: &Arc<Mutex<Coroutine>>,
    session: &Arc<Mutex<SessionState>>,
    call: &crate::nominal_command::NominalCommandCall,
    ctx: &ThreadedStepCtx<'_>,
) -> Result<ThreadedExecSuccess, ThreadedExecFault> {
    let request = original_threaded_nominal_request(coroutine, session, call, ctx)?;
    let mut observations = Vec::new();
    let blocked = if let Some(request) = request {
        let (observation, blocked) =
            invoke_original_threaded_nominal(coroutine, session, call, ctx, request)?;
        observations.push(observation);
        blocked
    } else {
        false
    };
    finish_threaded_nominal_pack(coroutine, ctx, blocked, observations)
}

fn original_threaded_nominal_request(
    coroutine: &Arc<Mutex<Coroutine>>,
    session: &Arc<Mutex<SessionState>>,
    call: &crate::nominal_command::NominalCommandCall,
    ctx: &ThreadedStepCtx<'_>,
) -> Result<Option<EffectRequest>, ThreadedExecFault> {
    use crate::nominal_command::NominalCommandRequest;
    let fail = |failure| ThreadedExecFault::new(Fault::Invoke { failure });
    let identity = ctx.handler.handler_identity();
    let request = {
        let coro = coroutine
            .lock()
            .expect("threaded ProtocolMachine lock poisoned");
        let mut state = session
            .lock()
            .expect("threaded ProtocolMachine lock poisoned");
        validate_threaded_nominal_owner(&coro, &mut state, call, ctx.tick, &identity)
            .map_err(fail)?;
        let pending = coro
            .nominal_continuation
            .as_ref()
            .expect("original pre-issued occurrence");
        pending.returned.is_none().then(|| {
            EffectRequest::nominal_command(
                pending.issued_at,
                NominalCommandRequest {
                    invocation: pending.invocation,
                    session: coro.session_id,
                    coroutine: coro.id,
                    declaration: call.declaration.clone(),
                    role: call.role.clone(),
                },
                call.budget_ticks.get(),
            )
        })
    };
    Ok(request)
}

fn invoke_original_threaded_nominal(
    coroutine: &Arc<Mutex<Coroutine>>,
    session: &Arc<Mutex<SessionState>>,
    call: &crate::nominal_command::NominalCommandCall,
    ctx: &ThreadedStepCtx<'_>,
    request: EffectRequest,
) -> Result<(EffectObservation, bool), ThreadedExecFault> {
    use crate::effect::{EffectOutcomeStatus, EffectResponse};
    let outcome = ctx.handler.handle_effect(request.clone());
    let observation = EffectObservation {
        request: request.clone(),
        outcome: outcome.clone(),
    };
    let accepted = outcome.accepted_status(&request.body);
    let final_identity = ctx.handler.handler_identity();
    let mut coro = coroutine
        .lock()
        .expect("threaded ProtocolMachine lock poisoned");
    if matches!(&accepted, EffectOutcomeStatus::Success) {
        if let Some(EffectResponse::NominalCommand { reply }) = &outcome.response {
            coro.nominal_continuation
                .as_mut()
                .expect("original retained")
                .returned = Some(reply.result.clone());
        }
    }
    let validation = {
        let mut state = session
            .lock()
            .expect("threaded ProtocolMachine lock poisoned");
        validate_threaded_nominal_owner(&coro, &mut state, call, ctx.tick, &final_identity)
    };
    if let Err(validation) = validation {
        coro.nominal_continuation
            .as_mut()
            .expect("original retained")
            .validation_failure = Some(validation.clone());
        let primary = match accepted {
            EffectOutcomeStatus::Failure { failure } => failure,
            _ => validation,
        };
        return Err(ThreadedExecFault::with_observation(
            Fault::Invoke { failure: primary },
            observation,
        ));
    }
    let blocked = match accepted {
        EffectOutcomeStatus::Failure { failure } => {
            return Err(ThreadedExecFault::with_observation(
                Fault::Invoke { failure },
                observation,
            ))
        }
        EffectOutcomeStatus::Blocked if !call.declaration.may_block => {
            return Err(ThreadedExecFault::with_observation(
                Fault::Invoke {
                    failure: EffectFailure::contract_violation(
                        "immediate nominal command returned Blocked",
                    ),
                },
                observation,
            ))
        }
        EffectOutcomeStatus::Blocked => true,
        EffectOutcomeStatus::Success => false,
    };
    Ok((observation, blocked))
}

fn finish_threaded_nominal_pack(
    coroutine: &Arc<Mutex<Coroutine>>,
    ctx: &ThreadedStepCtx<'_>,
    blocked: bool,
    observations: Vec<EffectObservation>,
) -> Result<ThreadedExecSuccess, ThreadedExecFault> {
    let (pack, sid, role, registers) = {
        let coro = coroutine
            .lock()
            .expect("threaded ProtocolMachine lock poisoned");
        let pack = if blocked {
            StepPack {
                coro_update: CoroUpdate::SetPc(coro.pc),
                type_update: None,
                events: vec![],
            }
        } else {
            StepPack {
                coro_update: CoroUpdate::CompleteNominal,
                type_update: None,
                events: vec![ObsEvent::Invoked {
                    tick: ctx.tick,
                    coro_id: coro.id,
                    role: coro.role.clone(),
                }],
            }
        };
        (pack, coro.session_id, coro.role.clone(), coro.regs.clone())
    };
    if !blocked && !ctx.nominal_publication_admitted {
        let failure =
            EffectFailure::contract_violation("canonical effect occurrence identifiers exhausted");
        coroutine
            .lock()
            .expect("threaded ProtocolMachine lock poisoned")
            .nominal_continuation
            .as_mut()
            .expect("validated original retained")
            .validation_failure = Some(failure.clone());
        return Err(ThreadedExecFault {
            fault: Fault::Invoke { failure },
            effect_observations: observations,
        });
    }
    let output_observation = if pack.events.is_empty() {
        None
    } else {
        let request = EffectRequest::output_condition_hint(ctx.tick, sid, None, &role, &registers);
        let outcome = ctx.handler.handle_effect(request.clone());
        let hint = outcome
            .clone()
            .into_output_condition_hint()
            .ok()
            .flatten()
            .unwrap_or(OutputConditionHint {
                predicate_ref: "protocol_machine.observable_output".to_string(),
                witness_ref: None,
            });
        Some(OutputHintObservation {
            request,
            outcome,
            hint: Some(hint),
        })
    };
    Ok(ThreadedExecSuccess {
        pack,
        effect_observations: observations,
        output_observation,
    })
}
