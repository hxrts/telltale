/// ProtocolMachine-level effect handler.
///
/// This is the interface between a guest runtime and the surrounding host
/// runtime. Each choreography can bind a different handler at session open
/// time.
///
/// Host-contract rules:
/// - Methods on this trait are synchronous. Async I/O, transport polling,
///   storage flushes, and background retries must happen outside handler
///   execution and feed their results back through canonical ingress.
/// - Implementations must treat the provided `state` as session-local scratch
///   for the current request only. They must not rely on unrelated session
///   state or mutate ProtocolMachine session metadata through side channels.
/// - Host-managed session-local mutation should flow through an explicit
///   ownership capability such as `OwnedSession`, not through ad hoc access to
///   the session store while handlers are executing.
#[doc(alias = "ExternalHandler")]
pub trait EffectHandler: Send + Sync {
    /// Stable identifier for effect-trace attribution.
    fn handler_identity(&self) -> String {
        crate::session::DEFAULT_HANDLER_ID.to_string()
    }

    /// Canonical typed effect boundary for guest-runtime execution.
    ///
    /// Runtime code must route host-facing effect work through this method so
    /// the request/outcome contract remains explicit and replay-visible.
    ///
    /// The default implementation preserves compatibility for existing
    /// helper-method-based handlers by translating each typed request into the
    /// corresponding helper method. New code should prefer overriding
    /// `handle_effect` directly.
    #[allow(clippy::too_many_lines)]
    fn handle_effect(&self, request: EffectRequest) -> EffectOutcome {
        if let Err(failure) = request.metadata.validate() {
            return EffectOutcome::failure(failure);
        }

        match request.body {
            EffectRequestBody::SendDecision {
                role,
                partner,
                label,
                state,
                payload,
            } => {
                let Some(sid) = request.session else {
                    return EffectOutcome::failure(EffectFailure::contract_violation(
                        "send_decision request is missing session",
                    ));
                };
                match self.send_decision(SendDecisionInput {
                    sid,
                    role: &role,
                    partner: &partner,
                    label: &label,
                    state: &state,
                    payload,
                }) {
                    EffectResult::Success(decision) => {
                        EffectOutcome::success(EffectResponse::SendDecision { decision })
                    }
                    EffectResult::Blocked => EffectOutcome::blocked(),
                    EffectResult::Failure(failure) => EffectOutcome::failure(failure),
                }
            }
            EffectRequestBody::Receive {
                role,
                partner,
                label,
                state,
                payload,
            } => {
                let mut state = state;
                match self.handle_recv(&role, &partner, &label, &mut state, &payload) {
                    EffectResult::Success(()) => {
                        EffectOutcome::success(EffectResponse::Receive { state })
                    }
                    EffectResult::Blocked => EffectOutcome::blocked(),
                    EffectResult::Failure(failure) => EffectOutcome::failure(failure),
                }
            }
            EffectRequestBody::Choose {
                role,
                partner,
                labels,
                state,
            } => match self.handle_choose(&role, &partner, &labels, &state) {
                EffectResult::Success(label) => {
                    EffectOutcome::success(EffectResponse::Choose { label })
                }
                EffectResult::Blocked => EffectOutcome::blocked(),
                EffectResult::Failure(failure) => EffectOutcome::failure(failure),
            },
            EffectRequestBody::InvokeStep { role, state } => {
                let mut state = state;
                match self.step(&role, &mut state) {
                    EffectResult::Success(()) => {
                        EffectOutcome::success(EffectResponse::InvokeStep { state })
                    }
                    EffectResult::Blocked => EffectOutcome::blocked(),
                    EffectResult::Failure(failure) => EffectOutcome::failure(failure),
                }
            }
            EffectRequestBody::Acquire { role, layer, state } => {
                let Some(sid) = request.session else {
                    return EffectOutcome::failure(EffectFailure::contract_violation(
                        "acquire request is missing session",
                    ));
                };
                match self.handle_acquire(sid, &role, &layer, &state) {
                    EffectResult::Success(evidence) => {
                        EffectOutcome::success(EffectResponse::Acquire { evidence })
                    }
                    EffectResult::Blocked => EffectOutcome::blocked(),
                    EffectResult::Failure(failure) => EffectOutcome::failure(failure),
                }
            }
            EffectRequestBody::Release {
                role,
                layer,
                evidence,
                state,
            } => {
                let Some(sid) = request.session else {
                    return EffectOutcome::failure(EffectFailure::contract_violation(
                        "release request is missing session",
                    ));
                };
                match self.handle_release(sid, &role, &layer, &evidence, &state) {
                    EffectResult::Success(()) => EffectOutcome::success(EffectResponse::Release),
                    EffectResult::Blocked => EffectOutcome::blocked(),
                    EffectResult::Failure(failure) => EffectOutcome::failure(failure),
                }
            }
            EffectRequestBody::TopologyEvents { tick } => match self.topology_events(tick) {
                EffectResult::Success(events) => {
                    EffectOutcome::success(EffectResponse::TopologyEvents { events })
                }
                EffectResult::Blocked => EffectOutcome::blocked(),
                EffectResult::Failure(failure) => EffectOutcome::failure(failure),
            },
            EffectRequestBody::OutputConditionHint { role, state } => {
                let Some(sid) = request.session else {
                    return EffectOutcome::failure(EffectFailure::contract_violation(
                        "output_condition_hint request is missing session",
                    ));
                };
                let hint = self.output_condition_hint(sid, &role, &state);
                EffectOutcome::success(EffectResponse::OutputConditionHint { hint })
            }
        }
    }

    /// Compute the payload for a send instruction.
    ///
    /// Helper hook used by the default `send_decision` implementation and by
    /// custom runners that want direct payload computation.
    ///
    /// # Arguments
    /// * `role` - The sending role
    /// * `partner` - The receiving role
    /// * `label` - The message label
    /// * `state` - The coroutine's register file (for reading state)
    ///
    /// Returns a typed outcome for the request.
    fn handle_send(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        state: &[Value],
    ) -> EffectResult<Value>;

    /// Decide how to handle a send, optionally with a precomputed payload.
    ///
    /// Middleware can override this to model loss/delay/corruption. The default
    /// behavior computes a payload via `handle_send` unless one is provided.
    ///
    /// Returns a typed outcome for the request.
    fn send_decision(&self, input: SendDecisionInput<'_>) -> EffectResult<SendDecision> {
        if let Some(payload) = input.payload {
            EffectResult::success(SendDecision::Deliver(payload))
        } else {
            self.handle_send(input.role, input.partner, input.label, input.state)
                .map_success(SendDecision::Deliver)
        }
    }

    /// Process a received value.
    ///
    /// # Arguments
    /// * `role` - The receiving role
    /// * `partner` - The sending role
    /// * `label` - The message label
    /// * `state` - The coroutine's register file (mutable for state updates)
    /// * `payload` - The received value
    ///
    /// Returns a typed outcome for the request.
    fn handle_recv(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        state: &mut Vec<Value>,
        payload: &Value,
    ) -> EffectResult<()>;

    /// Choose which branch to take for internal choice (select).
    ///
    /// Branch-selection helper for custom runners.
    ///
    /// The canonical ProtocolMachine resolves branch labels from received payloads and does
    /// not call this method in default dispatch paths.
    ///
    /// # Arguments
    /// * `role` - The choosing role
    /// * `partner` - The partner role
    /// * `labels` - The available branch labels
    /// * `state` - The coroutine's register file (for reading state)
    ///
    /// Returns a typed outcome for the request.
    fn handle_choose(
        &self,
        role: &str,
        partner: &str,
        labels: &[String],
        state: &[Value],
    ) -> EffectResult<String>;

    /// Perform an integration step after a protocol round.
    ///
    /// Called after all sends/receives for a tick are complete.
    ///
    /// Returns a typed outcome for the request.
    fn step(&self, role: &str, state: &mut Vec<Value>) -> EffectResult<()>;

    /// Attempt to acquire a guard layer.
    ///
    /// Returning `EffectResult::Blocked` causes the coroutine to block.
    /// `Success(evidence)` grants the acquire and binds the evidence value.
    fn handle_acquire(
        &self,
        _sid: SessionId,
        _role: &str,
        _layer: &str,
        _state: &[Value],
    ) -> EffectResult<Value> {
        EffectResult::success(Value::Unit)
    }

    /// Release a guard layer using previously acquired evidence.
    fn handle_release(
        &self,
        _sid: SessionId,
        _role: &str,
        _layer: &str,
        _evidence: &Value,
        _state: &[Value],
    ) -> EffectResult<()> {
        EffectResult::success(())
    }

    /// Topology perturbations injected by the environment for this scheduler tick.
    ///
    /// The ProtocolMachine ingests these before selecting coroutines for the round. This is
    /// a canonical ingress surface for external events; implementations should
    /// stage async discoveries before this method is called rather than doing
    /// async work from inside request handling.
    ///
    /// Returns a typed outcome for the request.
    fn topology_events(&self, _tick: u64) -> EffectResult<Vec<TopologyPerturbation>> {
        EffectResult::success(Vec::new())
    }

    /// Optional output-condition metadata for commit gating.
    ///
    /// The ProtocolMachine calls this only when a step emits observable events. Returning `None`
    /// delegates to ProtocolMachine-default metadata.
    fn output_condition_hint(
        &self,
        _sid: SessionId,
        _role: &str,
        _state: &[Value],
    ) -> Option<OutputConditionHint> {
        None
    }
}

impl<T: EffectHandler + ?Sized> EffectHandler for &T {
    fn handler_identity(&self) -> String {
        (**self).handler_identity()
    }

    fn handle_effect(&self, request: EffectRequest) -> EffectOutcome {
        (**self).handle_effect(request)
    }

    fn handle_send(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        state: &[Value],
    ) -> EffectResult<Value> {
        (**self).handle_send(role, partner, label, state)
    }

    fn send_decision(&self, input: SendDecisionInput<'_>) -> EffectResult<SendDecision> {
        (**self).send_decision(input)
    }

    fn handle_recv(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        state: &mut Vec<Value>,
        payload: &Value,
    ) -> EffectResult<()> {
        (**self).handle_recv(role, partner, label, state, payload)
    }

    fn handle_choose(
        &self,
        role: &str,
        partner: &str,
        labels: &[String],
        state: &[Value],
    ) -> EffectResult<String> {
        (**self).handle_choose(role, partner, labels, state)
    }

    fn step(&self, role: &str, state: &mut Vec<Value>) -> EffectResult<()> {
        (**self).step(role, state)
    }

    fn handle_acquire(
        &self,
        sid: SessionId,
        role: &str,
        layer: &str,
        state: &[Value],
    ) -> EffectResult<Value> {
        (**self).handle_acquire(sid, role, layer, state)
    }

    fn handle_release(
        &self,
        sid: SessionId,
        role: &str,
        layer: &str,
        evidence: &Value,
        state: &[Value],
    ) -> EffectResult<()> {
        (**self).handle_release(sid, role, layer, evidence, state)
    }

    fn topology_events(&self, tick: u64) -> EffectResult<Vec<TopologyPerturbation>> {
        (**self).topology_events(tick)
    }

    fn output_condition_hint(
        &self,
        sid: SessionId,
        role: &str,
        state: &[Value],
    ) -> Option<OutputConditionHint> {
        (**self).output_condition_hint(sid, role, state)
    }
}
