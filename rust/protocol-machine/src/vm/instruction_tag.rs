impl VM {
    pub(crate) fn step_tag(
        &mut self,
        coro_idx: usize,
        role: &str,
        _sid: SessionId,
        fact_reg: u16,
        dst: u16,
    ) -> Result<StepPack, Fault> {
        let fact_val = self.coroutines[coro_idx]
            .regs
            .get(usize::from(fact_reg))
            .ok_or(Fault::OutOfRegisters)?
            .clone();
        let (endpoint, fact) = Self::decode_fact(fact_val).ok_or_else(|| Fault::Transfer {
            message: format!("{role}: tag expects (endpoint, string) fact"),
        })?;
        self.coroutines[coro_idx]
            .knowledge_set
            .push(crate::coroutine::KnowledgeFact {
                endpoint: endpoint.clone(),
                fact: fact.clone(),
            });
        Ok(StepPack {
            coro_update: CoroUpdate::AdvancePcWriteReg {
                reg: dst,
                val: Value::Bool(true),
            },
            type_update: None,
            events: vec![ObsEvent::Tagged {
                tick: self.clock.tick,
                session: endpoint.sid,
                role: role.to_string(),
                fact,
            }],
        })
    }
}
