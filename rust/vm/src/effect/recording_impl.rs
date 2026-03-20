impl EffectHandler for RecordingEffectHandler<'_> {
    fn handler_identity(&self) -> String {
        self.inner.handler_identity()
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
        let payload_hint = input.payload.clone();
        let decision = self.inner.send_decision(input.clone());
        self.tape.record(
            "send_decision",
            json!({
                "sid": input.sid,
                "role": input.role,
                "partner": input.partner,
                "label": input.label,
                "payload_hint": payload_hint,
            }),
            encode_effect_result(&decision),
            &self.inner.handler_identity(),
            None,
        );
        decision
    }

    fn send_decision_fast_path(
        &self,
        fast_path: SendDecisionFastPathInput<'_>,
        state: &[Value],
        payload: Option<&Value>,
    ) -> Option<EffectResult<SendDecision>> {
        self.inner
            .send_decision_fast_path(fast_path, state, payload)
    }

    fn handle_recv(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        state: &mut Vec<Value>,
        payload: &Value,
    ) -> EffectResult<()> {
        let outcome = self.inner.handle_recv(role, partner, label, state, payload);
        self.tape.record(
            "handle_recv",
            json!({
                "role": role,
                "partner": partner,
                "label": label,
                "payload": payload,
            }),
            encode_effect_result(&outcome),
            &self.inner.handler_identity(),
            None,
        );
        outcome
    }

    fn handle_choose(
        &self,
        role: &str,
        partner: &str,
        labels: &[String],
        state: &[Value],
    ) -> EffectResult<String> {
        let chosen = self.inner.handle_choose(role, partner, labels, state);
        self.tape.record(
            "handle_choose",
            json!({
                "role": role,
                "partner": partner,
                "labels": labels,
            }),
            encode_effect_result(&chosen),
            &self.inner.handler_identity(),
            None,
        );
        chosen
    }

    fn step(&self, role: &str, state: &mut Vec<Value>) -> EffectResult<()> {
        let outcome = self.inner.step(role, state);
        self.tape.record(
            "invoke_step",
            json!({
                "role": role,
            }),
            encode_effect_result(&outcome),
            &self.inner.handler_identity(),
            None,
        );
        outcome
    }

    fn handle_acquire(
        &self,
        sid: SessionId,
        role: &str,
        layer: &str,
        state: &[Value],
    ) -> EffectResult<Value> {
        let decision = self.inner.handle_acquire(sid, role, layer, state);
        self.tape.record(
            "handle_acquire",
            json!({
                "sid": sid,
                "role": role,
                "layer": layer,
            }),
            encode_effect_result(&decision),
            &self.inner.handler_identity(),
            None,
        );
        decision
    }

    fn handle_release(
        &self,
        sid: SessionId,
        role: &str,
        layer: &str,
        evidence: &Value,
        state: &[Value],
    ) -> EffectResult<()> {
        let outcome = self.inner.handle_release(sid, role, layer, evidence, state);
        self.tape.record(
            "handle_release",
            json!({
                "sid": sid,
                "role": role,
                "layer": layer,
                "evidence": evidence,
            }),
            encode_effect_result(&outcome),
            &self.inner.handler_identity(),
            None,
        );
        outcome
    }

    fn topology_events(&self, tick: u64) -> EffectResult<Vec<TopologyPerturbation>> {
        let outcome = self.inner.topology_events(tick);
        self.tape.record(
            "topology_events",
            json!({
                "tick": tick,
            }),
            encode_effect_result(&outcome),
            &self.inner.handler_identity(),
            None,
        );
        outcome
    }

    fn output_condition_hint(
        &self,
        sid: SessionId,
        role: &str,
        state: &[Value],
    ) -> Option<OutputConditionHint> {
        self.inner.output_condition_hint(sid, role, state)
    }
}
