impl EffectHandler for RecordingEffectHandler<'_> {
    fn handler_identity(&self) -> String {
        self.inner.handler_identity()
    }

    fn handle_effect(&self, request: EffectRequest) -> EffectOutcome {
        let outcome = self.inner.handle_effect(request.clone());
        self.tape
            .record_exchange(request, outcome.clone(), &self.inner.handler_identity(), None);
        outcome
    }

    fn handle_send(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        state: &[Value],
    ) -> EffectResult<Value> {
        self.inner.handle_send(role, partner, label, state)
    }

    fn send_decision(&self, input: SendDecisionInput<'_>) -> EffectResult<SendDecision> {
        self.handle_effect(EffectRequest::send_decision(
            0,
            input.sid,
            None,
            input.role,
            input.partner,
            input.label,
            input.state,
            input.payload,
        ))
        .into_send_decision()
        .unwrap_or_else(EffectResult::failure)
    }

    fn handle_recv(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        state: &mut Vec<Value>,
        payload: &Value,
    ) -> EffectResult<()> {
        let outcome = self
            .handle_effect(EffectRequest::receive(
                0,
                None,
                None,
                role,
                partner,
                label,
                state,
                payload.clone(),
            ))
            .into_unit("handle_recv")
            .unwrap_or_else(EffectResult::failure);
        if let EffectResult::Success(()) = &outcome {
            if let Some(EffectResponse::Receive { state: new_state }) = self
                .tape
                .exchanges()
                .last()
                .and_then(|exchange| exchange.outcome.response.clone())
            {
                *state = new_state;
            }
        }
        outcome
    }

    fn handle_choose(
        &self,
        role: &str,
        partner: &str,
        labels: &[String],
        state: &[Value],
    ) -> EffectResult<String> {
        self.handle_effect(EffectRequest::choose(
            0,
            None,
            None,
            role,
            partner,
            labels,
            state,
        ))
        .into_label()
        .unwrap_or_else(EffectResult::failure)
    }

    fn step(&self, role: &str, state: &mut Vec<Value>) -> EffectResult<()> {
        let outcome = self
            .handle_effect(EffectRequest::invoke_step(0, None, None, role, state))
            .into_unit("invoke_step")
            .unwrap_or_else(EffectResult::failure);
        if let EffectResult::Success(()) = &outcome {
            if let Some(EffectResponse::InvokeStep { state: new_state }) = self
                .tape
                .exchanges()
                .last()
                .and_then(|exchange| exchange.outcome.response.clone())
            {
                *state = new_state;
            }
        }
        outcome
    }

    fn handle_acquire(
        &self,
        sid: SessionId,
        role: &str,
        layer: &str,
        state: &[Value],
    ) -> EffectResult<Value> {
        self.handle_effect(EffectRequest::acquire(0, sid, None, role, layer, state))
            .into_value("acquire")
            .unwrap_or_else(EffectResult::failure)
    }

    fn handle_release(
        &self,
        sid: SessionId,
        role: &str,
        layer: &str,
        evidence: &Value,
        state: &[Value],
    ) -> EffectResult<()> {
        self.handle_effect(EffectRequest::release(0, sid, None, role, layer, evidence, state))
            .into_unit("handle_release")
            .unwrap_or_else(EffectResult::failure)
    }

    fn topology_events(&self, tick: u64) -> EffectResult<Vec<TopologyPerturbation>> {
        self.handle_effect(EffectRequest::topology_events(tick))
            .into_topology()
            .unwrap_or_else(EffectResult::failure)
    }

    fn output_condition_hint(
        &self,
        sid: SessionId,
        role: &str,
        state: &[Value],
    ) -> Option<OutputConditionHint> {
        self.handle_effect(EffectRequest::output_condition_hint(0, sid, None, role, state))
            .into_output_condition_hint()
            .ok()
            .flatten()
    }
}
