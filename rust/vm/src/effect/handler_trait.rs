/// VM-level effect handler.
///
/// This is the interface between the VM and the host application. Each
/// choreography can bind a different handler at session open time.
pub trait EffectHandler: Send + Sync {
    /// Stable identifier for effect-trace attribution.
    fn handler_identity(&self) -> String {
        "default_handler".to_string()
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
    /// # Errors
    /// Returns an error string if the handler fails.
    fn handle_send(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        state: &[Value],
    ) -> Result<Value, String>;

    /// Optional fast-path hook for send decision dispatch.
    ///
    /// Returning `Some(result)` bypasses `send_decision`.
    /// Returning `None` keeps canonical behavior unchanged.
    fn send_decision_fast_path(
        &self,
        _fast_path: SendDecisionFastPathInput<'_>,
        _state: &[Value],
        _payload: Option<&Value>,
    ) -> Option<Result<SendDecision, String>> {
        None
    }

    /// Decide how to handle a send, optionally with a precomputed payload.
    ///
    /// Middleware can override this to model loss/delay/corruption. The default
    /// behavior computes a payload via `handle_send` unless one is provided.
    ///
    /// # Errors
    ///
    /// Returns an error string if the handler fails.
    fn send_decision(&self, input: SendDecisionInput<'_>) -> Result<SendDecision, String> {
        if let Some(payload) = input.payload {
            Ok(SendDecision::Deliver(payload))
        } else {
            self.handle_send(input.role, input.partner, input.label, input.state)
                .map(SendDecision::Deliver)
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
    /// # Errors
    /// Returns an error string if the handler fails.
    fn handle_recv(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        state: &mut Vec<Value>,
        payload: &Value,
    ) -> Result<(), String>;

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
    /// # Errors
    /// Returns an error string if the handler fails.
    fn handle_choose(
        &self,
        role: &str,
        partner: &str,
        labels: &[String],
        state: &[Value],
    ) -> Result<String, String>;

    /// Perform an integration step after a protocol round.
    ///
    /// Called after all sends/receives for a tick are complete.
    ///
    /// # Errors
    /// Returns an error string if the handler fails.
    fn step(&self, role: &str, state: &mut Vec<Value>) -> Result<(), String>;

    /// Attempt to acquire a guard layer.
    ///
    /// Returning `AcquireDecision::Block` causes the coroutine to block.
    ///
    /// # Errors
    ///
    /// Returns an error string if acquisition fails.
    fn handle_acquire(
        &self,
        _sid: SessionId,
        _role: &str,
        _layer: &str,
        _state: &[Value],
    ) -> Result<AcquireDecision, String> {
        Ok(AcquireDecision::Grant(Value::Unit))
    }

    /// Release a guard layer using previously acquired evidence.
    ///
    /// # Errors
    ///
    /// Returns an error string if release fails.
    fn handle_release(
        &self,
        _sid: SessionId,
        _role: &str,
        _layer: &str,
        _evidence: &Value,
        _state: &[Value],
    ) -> Result<(), String> {
        Ok(())
    }

    /// Topology perturbations injected by the environment for this scheduler tick.
    ///
    /// The VM ingests these before selecting coroutines for the round.
    ///
    /// # Errors
    ///
    /// Returns an error string if topology retrieval fails.
    fn topology_events(&self, _tick: u64) -> Result<Vec<TopologyPerturbation>, String> {
        Ok(Vec::new())
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
    ) -> Result<Value, String> {
        (**self).handle_send(role, partner, label, state)
    }

    fn send_decision(&self, input: SendDecisionInput<'_>) -> Result<SendDecision, String> {
        (**self).send_decision(input)
    }

    fn send_decision_fast_path(
        &self,
        fast_path: SendDecisionFastPathInput<'_>,
        state: &[Value],
        payload: Option<&Value>,
    ) -> Option<Result<SendDecision, String>> {
        (**self).send_decision_fast_path(fast_path, state, payload)
    }

    fn handle_recv(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        state: &mut Vec<Value>,
        payload: &Value,
    ) -> Result<(), String> {
        (**self).handle_recv(role, partner, label, state, payload)
    }

    fn handle_choose(
        &self,
        role: &str,
        partner: &str,
        labels: &[String],
        state: &[Value],
    ) -> Result<String, String> {
        (**self).handle_choose(role, partner, labels, state)
    }

    fn step(&self, role: &str, state: &mut Vec<Value>) -> Result<(), String> {
        (**self).step(role, state)
    }

    fn handle_acquire(
        &self,
        sid: SessionId,
        role: &str,
        layer: &str,
        state: &[Value],
    ) -> Result<AcquireDecision, String> {
        (**self).handle_acquire(sid, role, layer, state)
    }

    fn handle_release(
        &self,
        sid: SessionId,
        role: &str,
        layer: &str,
        evidence: &Value,
        state: &[Value],
    ) -> Result<(), String> {
        (**self).handle_release(sid, role, layer, evidence, state)
    }

    fn topology_events(&self, tick: u64) -> Result<Vec<TopologyPerturbation>, String> {
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

