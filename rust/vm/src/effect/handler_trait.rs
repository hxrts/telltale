/// VM-level effect handler.
///
/// This is the interface between the VM and the host application. Each
/// choreography can bind a different handler at session open time.
///
/// Host-contract rules:
/// - Methods on this trait are synchronous. Async I/O, transport polling,
///   storage flushes, and background retries must happen outside callback
///   execution and feed their results back through canonical ingress.
/// - Implementations must treat the provided `state` as session-local scratch
///   for the current callback only. They must not rely on unrelated session
///   state or mutate VM session metadata through side channels.
/// - Host-managed session-local mutation should flow through an explicit
///   ownership capability such as `OwnedSession`, not through ad hoc access to
///   the session store while callbacks are executing.
pub trait EffectHandler: Send + Sync {
    /// Stable identifier for effect-trace attribution.
    fn handler_identity(&self) -> String {
        crate::session::DEFAULT_HANDLER_ID.to_string()
    }

    /// Compute the payload for a send instruction.
    ///
    /// Compatibility hook:
    /// Canonical VM send paths pass an explicit payload into `send_decision`.
    /// This method remains for adapters and custom runners.
    ///
    /// # Arguments
    /// * `role` - The sending role
    /// * `partner` - The receiving role
    /// * `label` - The message label
    /// * `state` - The coroutine's register file (for reading state)
    ///
    /// Returns a typed outcome for the callback.
    fn handle_send(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        state: &[Value],
    ) -> EffectResult<Value>;

    /// Optional fast-path hook for send decision dispatch.
    ///
    /// Returning `Some(result)` bypasses `send_decision`.
    /// Returning `None` keeps canonical behavior unchanged.
    fn send_decision_fast_path(
        &self,
        _fast_path: SendDecisionFastPathInput<'_>,
        _state: &[Value],
        _payload: Option<&Value>,
    ) -> Option<EffectResult<SendDecision>> {
        None
    }

    /// Decide how to handle a send, optionally with a precomputed payload.
    ///
    /// Middleware can override this to model loss/delay/corruption. The default
    /// behavior computes a payload via `handle_send` unless one is provided.
    ///
    /// Returns a typed outcome for the callback.
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
    /// Returns a typed outcome for the callback.
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
    /// Compatibility hook:
    /// The canonical VM currently resolves branch labels from received payloads and
    /// does not call this method in default dispatch paths.
    ///
    /// Custom runners may still use this as an explicit branch-selection hook.
    ///
    /// # Arguments
    /// * `role` - The choosing role
    /// * `partner` - The partner role
    /// * `labels` - The available branch labels
    /// * `state` - The coroutine's register file (for reading state)
    ///
    /// Returns a typed outcome for the callback.
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
    /// Returns a typed outcome for the callback.
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
    /// The VM ingests these before selecting coroutines for the round. This is
    /// a canonical ingress surface for external events; implementations should
    /// stage async discoveries before this method is called rather than doing
    /// async work from inside the callback.
    ///
    /// Returns a typed outcome for the callback.
    fn topology_events(&self, _tick: u64) -> EffectResult<Vec<TopologyPerturbation>> {
        EffectResult::success(Vec::new())
    }

    /// Optional output-condition metadata for commit gating.
    ///
    /// The VM calls this only when a step emits observable events. Returning `None`
    /// delegates to VM-default metadata.
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

    fn send_decision_fast_path(
        &self,
        fast_path: SendDecisionFastPathInput<'_>,
        state: &[Value],
        payload: Option<&Value>,
    ) -> Option<EffectResult<SendDecision>> {
        (**self).send_decision_fast_path(fast_path, state, payload)
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
