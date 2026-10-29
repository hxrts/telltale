// Actual nominal command invocation and original coroutine continuation.
impl ProtocolMachine {
    pub(crate) fn bind_nominal_owner(&mut self, owner: &crate::owned::OwnedSession) {
        for coroutine in self
            .coroutines
            .iter_mut()
            .filter(|coroutine| coroutine.session_id == owner.session_id())
        {
            coroutine.nominal_owner = Some(owner.clone());
        }
    }

    fn validate_nominal_continuation(&self, coro_idx: usize) -> Result<(), EffectFailure> {
        let coroutine = &self.coroutines[coro_idx];
        let pending = coroutine
            .nominal_continuation
            .as_ref()
            .ok_or_else(|| EffectFailure::contract_violation("no original nominal continuation"))?;
        pending.validate(
            &self.sessions,
            coroutine.session_id,
            coroutine.id,
            coroutine.pc,
            &pending.call,
            self.clock.tick,
        )?;
        let original = self
            .outstanding_effects
            .as_slice()
            .iter()
            .find(|effect| effect.effect_id == pending.invocation)
            .ok_or_else(|| {
                EffectFailure::contract_violation("original nominal effect is missing")
            })?;
        if original.session != Some(coroutine.session_id)
            || original.owner_id.as_deref() != Some(pending.owner.capability().owner_id.as_str())
            || original.budget_ticks != Some(pending.call.budget_ticks.get())
            || original.ordering_key != pending.issued_at
            || original.handler_identity != pending.handler_identity
            || !matches!(
                original.status,
                OutstandingEffectStatus::Pending | OutstandingEffectStatus::Blocked
            )
        {
            return Err(EffectFailure::contract_violation(
                "nominal continuation is terminal, invalidated or mismatched",
            ));
        }
        let operation = self
            .operation_instances
            .as_slice()
            .iter()
            .find(|operation| {
                operation.operation_id == Self::effect_operation_id(pending.invocation)
            })
            .ok_or_else(|| {
                EffectFailure::contract_violation("original nominal operation is missing")
            })?;
        if operation.kind != pending.call.enclosing_operation
            || operation.agreement_profile.as_ref() != Some(&pending.call.agreement_profile)
            || operation.budget_ticks != Some(pending.call.budget_ticks.get())
            || !operation.requires_proof
        {
            return Err(EffectFailure::contract_violation(
                "original nominal operation policy changed",
            ));
        }
        Ok(())
    }

    fn step_nominal_command(
        &mut self,
        coro_idx: usize,
        role: &str,
        call: &crate::nominal_command::NominalCommandCall,
        handler: &dyn EffectHandler,
    ) -> Result<StepPack, Fault> {
        self.validate_source_operation_context(coro_idx)?;
        let owner = self.nominal_invocation_owner(coro_idx, role, call)?;
        if self.coroutines[coro_idx].nominal_continuation.is_none() {
            self.issue_original_nominal_command(coro_idx, role, call, owner, handler)?;
        }
        self.poll_original_nominal_command(coro_idx, role, call, handler)
    }

    fn nominal_invocation_owner(
        &self,
        coro_idx: usize,
        role: &str,
        call: &crate::nominal_command::NominalCommandCall,
    ) -> Result<crate::owned::OwnedSession, Fault> {
        let fail = |failure| Fault::Invoke { failure };
        let coroutine = &self.coroutines[coro_idx];
        let sid = coroutine.session_id;
        let endpoint = Endpoint {
            sid,
            role: role.to_string(),
        };
        if !call.supported_agreement()
            || self
                .sessions
                .default_handler_for_session(sid)
                .map_or(true, String::is_empty)
            || coroutine.role != role
            || call.role != role
            || !coroutine.owned_endpoints.contains(&endpoint)
            || call.result == 0
            || coroutine.regs.get(usize::from(call.result)).is_none()
        {
            return Err(fail(EffectFailure::contract_violation(
                "nominal invocation requires its original role/endpoint and result register",
            )));
        }
        let owner = coroutine.nominal_owner.clone().ok_or_else(|| fail(EffectFailure::contract_violation("nominal invocation requires an issued opaque owner; checkpoint metadata cannot recreate it")))?;
        if owner.session_id() != sid
            || !matches!(&owner.capability().scope, OwnershipScope::Session)
        {
            return Err(fail(EffectFailure::contract_violation(
                "nominal invocation owner does not cover this session",
            )));
        }
        self.sessions
            .validate_ownership_capability(owner.capability())
            .map_err(|error| fail(EffectFailure::contract_violation(error.to_string())))?;
        Ok(owner)
    }

    fn issue_original_nominal_command(
        &mut self,
        coro_idx: usize,
        role: &str,
        call: &crate::nominal_command::NominalCommandCall,
        owner: crate::owned::OwnedSession,
        handler: &dyn EffectHandler,
    ) -> Result<(), Fault> {
        use crate::nominal_command::{NominalCommandRequest, PendingNominalContinuation};
        let fail = |failure| Fault::Invoke { failure };
        let sid = self.coroutines[coro_idx].session_id;
        self.clock
            .tick
            .checked_add(call.budget_ticks.get())
            .ok_or_else(|| {
                fail(EffectFailure::contract_violation(
                    "selected original nominal progress endpoint overflowed",
                ))
            })?;
        if self.next_effect_id == u64::MAX {
            return Err(fail(EffectFailure::contract_violation(
                "nominal occurrence identifiers exhausted",
            )));
        }
        let coro_id = self.coroutines[coro_idx].id;
        let pc = self.coroutines[coro_idx].pc;
        let request = EffectRequest::nominal_command(
            self.clock.tick,
            NominalCommandRequest {
                invocation: self.next_effect_id,
                session: sid,
                coroutine: coro_id,
                declaration: call.declaration.clone(),
                role: role.to_string(),
            },
            call.budget_ticks.get(),
        );
        self.ensure_effect_request_allowed(&request).map_err(fail)?;
        let invocation = self
            .issue_runtime_effect_with_budget(
                "nominal_command",
                Some(sid),
                &handler.handler_identity(),
                serde_json::to_value(&request).expect("typed nominal request serializes"),
                Some(call.budget_ticks.get()),
            )
            .map_err(|failure| Fault::Invoke { failure })?;
        if let Some(effect) = self
            .outstanding_effects
            .as_mut_slice()
            .iter_mut()
            .find(|effect| effect.effect_id == invocation)
        {
            effect.effect_interface = Some(call.declaration.interface.clone());
            effect.effect_operation = Some(call.declaration.operation.clone());
        }
        if let Some(operation) = self
            .operation_instances
            .as_mut_slice()
            .iter_mut()
            .find(|operation| operation.operation_id == Self::effect_operation_id(invocation))
        {
            operation.kind = call.enclosing_operation.clone();
            operation.agreement_profile = Some(call.agreement_profile.clone());
            operation.requires_proof = true;
        }
        let child = self
            .outstanding_effects
            .as_slice()
            .iter()
            .find(|effect| effect.effect_id == invocation)
            .expect("original issued child");
        crate::operation_lifecycle::admit_source_child(
            &mut self.coroutines[coro_idx],
            self.operation_instances.as_mut_slice(),
            child,
            call,
        )
        .map_err(crate::operation_lifecycle::transition_fault)?;
        self.coroutines[coro_idx].nominal_continuation = Some(PendingNominalContinuation {
            invocation,
            coroutine: coro_id,
            pc,
            call: call.clone(),
            owner,
            issued_at: self.clock.tick,
            handler_identity: handler.handler_identity(),
            validation_failure: None,
            returned: None,
        });
        Ok(())
    }

    fn accept_nominal_callback_status(
        &mut self,
        coro_idx: usize,
        call: &crate::nominal_command::NominalCommandCall,
        request: &EffectRequest,
        outcome: crate::effect::EffectOutcome,
        invocation: u64,
    ) -> Result<Option<StepPack>, Fault> {
        use crate::effect::{EffectOutcomeStatus, EffectResponse};
        let fail = |failure| Fault::Invoke { failure };
        match outcome.accepted_status(&request.body) {
            EffectOutcomeStatus::Failure { failure } => {
                self.complete_runtime_effect(
                    invocation,
                    OutstandingEffectStatus::Failed,
                    json!({"status":"failure", "failure":failure}),
                )
                .map_err(|error| fail(EffectFailure::contract_violation(error.to_string())))?;
                return Err(fail(failure));
            }
            EffectOutcomeStatus::Blocked if !call.declaration.may_block => {
                let failure =
                    EffectFailure::contract_violation("immediate nominal command returned blocked");
                self.complete_runtime_effect(
                    invocation,
                    OutstandingEffectStatus::Failed,
                    json!({"status":"failure", "failure":failure}),
                )
                .map_err(|error| fail(EffectFailure::contract_violation(error.to_string())))?;
                return Err(fail(failure));
            }
            EffectOutcomeStatus::Blocked => {
                let was_pending = self.outstanding_effects.as_slice().iter().any(|effect| {
                    effect.effect_id == invocation
                        && effect.status == OutstandingEffectStatus::Pending
                });
                if was_pending {
                    self.complete_runtime_effect(
                        invocation,
                        OutstandingEffectStatus::Blocked,
                        json!({"status":"blocked"}),
                    )
                    .map_err(|error| fail(EffectFailure::contract_violation(error.to_string())))?;
                }
                // Canonical scheduling retries the same occurrence without advancing PC or resetting its progress owner.
                return Ok(Some(StepPack {
                    coro_update: CoroUpdate::SetPc(self.coroutines[coro_idx].pc),
                    type_update: None,
                    events: vec![],
                }));
            }
            EffectOutcomeStatus::Success => {
                let Some(EffectResponse::NominalCommand { reply }) = outcome.response else {
                    unreachable!("accepted exact nominal response");
                };
                self.coroutines[coro_idx]
                    .nominal_continuation
                    .as_mut()
                    .expect("original retained")
                    .returned = Some(reply.result);
            }
        }
        Ok(None)
    }

    fn validate_nominal_callback_result(
        &mut self,
        coro_idx: usize,
        request: &EffectRequest,
        outcome: &crate::effect::EffectOutcome,
        invocation: u64,
        handler: &dyn EffectHandler,
    ) -> Result<(), Fault> {
        use crate::effect::{EffectOutcomeStatus, EffectResponse};
        let fail = |failure| Fault::Invoke { failure };
        // Retain the actual typed result before any independent admission refusal.
        // This does not complete the occurrence or authorize its continuation.
        if matches!(
            outcome.accepted_status(&request.body),
            EffectOutcomeStatus::Success
        ) {
            if let Some(EffectResponse::NominalCommand { reply }) = &outcome.response {
                self.coroutines[coro_idx]
                    .nominal_continuation
                    .as_mut()
                    .expect("original retained")
                    .returned = Some(reply.result.clone());
            }
        }
        // Revalidate semantic handler identity as well as the actual issued owner.
        let validation = self.validate_nominal_continuation(coro_idx).and_then(|()| {
            self.coroutines[coro_idx]
                .nominal_continuation
                .as_ref()
                .expect("original retained")
                .require_handler_identity(&handler.handler_identity())
        });
        if let Err(validation) = validation {
            // Failure is primary even if the callback independently changed its admission.
            self.coroutines[coro_idx]
                .nominal_continuation
                .as_mut()
                .expect("original retained")
                .validation_failure = Some(validation.clone());
            let (primary, independent_validation) = match outcome.accepted_status(&request.body) {
                EffectOutcomeStatus::Failure { failure } => (failure, Some(validation)),
                _ => (validation, None),
            };
            self.complete_runtime_effect(invocation, OutstandingEffectStatus::Failed,
                json!({"status":"failure", "failure":primary, "independent_validation":independent_validation}))
                .expect("the actual callback cannot remove its private pre-issued canonical occurrence");
            return Err(fail(primary));
        }
        Ok(())
    }

    fn poll_original_nominal_command(
        &mut self,
        coro_idx: usize,
        role: &str,
        call: &crate::nominal_command::NominalCommandCall,
        handler: &dyn EffectHandler,
    ) -> Result<StepPack, Fault> {
        use crate::nominal_command::NominalCommandRequest;
        let fail = |failure| Fault::Invoke { failure };
        let sid = self.coroutines[coro_idx].session_id;
        let original = self.coroutines[coro_idx]
            .nominal_continuation
            .as_ref()
            .expect("original retained");
        if &original.call != call {
            return Err(fail(EffectFailure::contract_violation(
                "nominal instruction changed while its original continuation was live",
            )));
        }
        self.validate_nominal_continuation(coro_idx).map_err(fail)?;
        original
            .require_handler_identity(&handler.handler_identity())
            .map_err(fail)?;
        let original_handler = self
            .outstanding_effects
            .as_slice()
            .iter()
            .find(|effect| effect.effect_id == original.invocation)
            .expect("validated original occurrence");
        if original_handler.handler_identity != handler.handler_identity() {
            return Err(fail(EffectFailure::contract_violation(
                "nominal retry changed the original handler identity",
            )));
        }
        if original.returned.is_none() {
            let invocation = original.invocation;
            let original_handler_identity = original.handler_identity.clone();
            let request = EffectRequest::nominal_command(
                original.issued_at,
                NominalCommandRequest {
                    invocation,
                    session: sid,
                    coroutine: original.coroutine,
                    declaration: call.declaration.clone(),
                    role: role.to_string(),
                },
                call.budget_ticks.get(),
            );
            let outcome = handler.handle_effect(request.clone());
            self.record_effect_exchange(&request, &outcome, &original_handler_identity, invocation)
                .map_err(|failure| Fault::Invoke { failure })?;
            self.validate_nominal_callback_result(
                coro_idx, &request, &outcome, invocation, handler,
            )?;
            if let Some(blocked) =
                self.accept_nominal_callback_status(coro_idx, call, &request, outcome, invocation)?
            {
                return Ok(blocked);
            }
        }
        if let Err(failure) = crate::commit_common::require_effect_capacity(self.next_effect_id, 3)
        {
            let original = self.coroutines[coro_idx]
                .nominal_continuation
                .as_mut()
                .expect("validated original retained");
            original.validation_failure = Some(failure.clone());
            let invocation = original.invocation;
            let returned = original.returned.clone();
            self.complete_runtime_effect(
                invocation,
                OutstandingEffectStatus::Failed,
                json!({"status":"failure", "failure":failure, "retained_result":returned}),
            )
            .expect("publication refusal settles the same validated original occurrence");
            return Err(fail(failure));
        }
        Ok(StepPack {
            coro_update: CoroUpdate::CompleteNominal,
            type_update: None,
            events: vec![ObsEvent::Invoked {
                tick: self.clock.tick,
                coro_id: self.coroutines[coro_idx].id,
                role: role.to_string(),
            }],
        })
    }

    fn commit_nominal_result(
        &mut self,
        coro_idx: usize,
        handler_identity: &str,
    ) -> Result<(), Fault> {
        self.validate_nominal_continuation(coro_idx)
            .map_err(|failure| Fault::Invoke { failure })?;
        let pending = self.coroutines[coro_idx]
            .nominal_continuation
            .as_ref()
            .expect("original retained");
        pending
            .require_handler_identity(handler_identity)
            .map_err(|failure| Fault::Invoke { failure })?;
        let result = pending.returned.clone().ok_or_else(|| Fault::Invoke {
            failure: EffectFailure::contract_violation("nominal result is still pending"),
        })?;
        let invocation = pending.invocation;
        let destination = usize::from(pending.call.result);
        if self.coroutines[coro_idx].regs.get(destination).is_none() {
            return Err(Fault::OutOfRegisters);
        }
        let (pc, value) = match &result {
            Ok(value) => (pending.call.on_ok, value.value()),
            Err(error) => (pending.call.on_err, Value::Str(error.clone())),
        };
        if let Ok(value) = &result {
            value
                .require_declaration(&pending.call.declaration)
                .map_err(|failure| Fault::Invoke { failure })?;
            if let crate::nominal_command::NominalCommandValue::Readiness(witness) = value {
                // Consume from the same original session only after all output/WAL gates.
                self.sessions
                    .with_owned_session_at(
                        pending.owner.session_id(),
                        Some(self.clock.tick),
                        |session| {
                            session.consume_readiness_witness(pending.owner.capability(), witness)
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
            json!({"status":"success", "result":result}),
        )
        .map_err(|error| Fault::Invoke {
            failure: EffectFailure::contract_violation(error.to_string()),
        })?;
        let coroutine = &mut self.coroutines[coro_idx];
        coroutine.regs[destination] = value;
        coroutine.pc = pc;
        coroutine.status = CoroStatus::Ready;
        coroutine.nominal_continuation = None;
        Ok(())
    }
}
