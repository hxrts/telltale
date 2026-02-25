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
    ) -> Result<Value, String> {
        self.inner.handle_send(role, partner, label, state)
    }

    fn send_decision(&self, input: SendDecisionInput<'_>) -> Result<SendDecision, String> {
        let payload_hint = input.payload.clone();
        let decision = self.inner.send_decision(input.clone())?;
        let outputs = match &decision {
            SendDecision::Deliver(value) => json!({
                "decision": "deliver",
                "payload": value,
            }),
            SendDecision::Drop => json!({
                "decision": "drop",
            }),
            SendDecision::Defer => json!({
                "decision": "defer",
            }),
        };
        self.tape.record(
            "send_decision",
            json!({
                "sid": input.sid,
                "role": input.role,
                "partner": input.partner,
                "label": input.label,
                "payload_hint": payload_hint,
            }),
            outputs,
            &self.inner.handler_identity(),
            None,
        );
        Ok(decision)
    }

    fn send_decision_fast_path(
        &self,
        fast_path: SendDecisionFastPathInput<'_>,
        state: &[Value],
        payload: Option<&Value>,
    ) -> Option<Result<SendDecision, String>> {
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
    ) -> Result<(), String> {
        self.inner
            .handle_recv(role, partner, label, state, payload)?;
        self.tape.record(
            "handle_recv",
            json!({
                "role": role,
                "partner": partner,
                "label": label,
                "payload": payload,
            }),
            json!({"ok": true}),
            &self.inner.handler_identity(),
            None,
        );
        Ok(())
    }

    fn handle_choose(
        &self,
        role: &str,
        partner: &str,
        labels: &[String],
        state: &[Value],
    ) -> Result<String, String> {
        let chosen = self.inner.handle_choose(role, partner, labels, state)?;
        self.tape.record(
            "handle_choose",
            json!({
                "role": role,
                "partner": partner,
                "labels": labels,
            }),
            json!({
                "label": chosen,
            }),
            &self.inner.handler_identity(),
            None,
        );
        Ok(chosen)
    }

    fn step(&self, role: &str, state: &mut Vec<Value>) -> Result<(), String> {
        self.inner.step(role, state)?;
        self.tape.record(
            "invoke_step",
            json!({
                "role": role,
            }),
            json!({"ok": true}),
            &self.inner.handler_identity(),
            None,
        );
        Ok(())
    }

    fn handle_acquire(
        &self,
        sid: SessionId,
        role: &str,
        layer: &str,
        state: &[Value],
    ) -> Result<AcquireDecision, String> {
        let decision = self.inner.handle_acquire(sid, role, layer, state)?;
        let outputs = match &decision {
            AcquireDecision::Grant(evidence) => json!({
                "decision": "grant",
                "evidence": evidence,
            }),
            AcquireDecision::Block => json!({
                "decision": "block",
            }),
        };
        self.tape.record(
            "handle_acquire",
            json!({
                "sid": sid,
                "role": role,
                "layer": layer,
            }),
            outputs,
            &self.inner.handler_identity(),
            None,
        );
        Ok(decision)
    }

    fn handle_release(
        &self,
        sid: SessionId,
        role: &str,
        layer: &str,
        evidence: &Value,
        state: &[Value],
    ) -> Result<(), String> {
        self.inner
            .handle_release(sid, role, layer, evidence, state)?;
        self.tape.record(
            "handle_release",
            json!({
                "sid": sid,
                "role": role,
                "layer": layer,
                "evidence": evidence,
            }),
            json!({"ok": true}),
            &self.inner.handler_identity(),
            None,
        );
        Ok(())
    }

    fn topology_events(&self, tick: u64) -> Result<Vec<TopologyPerturbation>, String> {
        let events = self.inner.topology_events(tick)?;
        for event in &events {
            self.tape.record(
                "topology_event",
                json!({
                    "tick": tick,
                }),
                json!({
                    "applied": true,
                    "topology": event,
                }),
                &self.inner.handler_identity(),
                Some(event.clone()),
            );
        }
        Ok(events)
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

