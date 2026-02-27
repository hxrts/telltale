/// Thread-safe effect-trace tape used by recording/replay handlers.
#[derive(Debug, Default)]
pub struct EffectTraceTape {
    next_effect_id: AtomicU64,
    entries: Mutex<Vec<EffectTraceEntry>>,
}

impl EffectTraceTape {
    /// Create an empty tape.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a tape from pre-recorded entries.
    #[must_use]
    pub fn from_entries(entries: Vec<EffectTraceEntry>) -> Self {
        let next_effect_id = entries
            .last()
            .map_or(0, |entry| entry.effect_id.saturating_add(1));
        Self {
            next_effect_id: AtomicU64::new(next_effect_id),
            entries: Mutex::new(entries),
        }
    }

    /// Record one effect entry.
    ///
    /// # Panics
    ///
    /// Panics if the internal mutex is poisoned.
    pub fn record(
        &self,
        effect_kind: &str,
        inputs: JsonValue,
        outputs: JsonValue,
        handler_identity: &str,
        topology: Option<TopologyPerturbation>,
    ) {
        let effect_id = self.next_effect_id.fetch_add(1, Ordering::Relaxed);
        let entry = EffectTraceEntry {
            effect_id,
            effect_kind: effect_kind.to_string(),
            inputs,
            outputs,
            handler_identity: handler_identity.to_string(),
            ordering_key: effect_id,
            topology,
        };
        self.entries
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .push(entry);
    }

    /// Clone all recorded entries.
    ///
    /// # Panics
    ///
    /// Panics if the internal mutex is poisoned.
    #[must_use]
    pub fn entries(&self) -> Vec<EffectTraceEntry> {
        self.entries
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .clone()
    }
}

/// A handler wrapper that records effect outcomes for replay.
pub struct RecordingEffectHandler<'a> {
    inner: &'a dyn EffectHandler,
    tape: EffectTraceTape,
}

impl<'a> RecordingEffectHandler<'a> {
    /// Wrap a base handler and begin recording effect outcomes.
    #[must_use]
    pub fn new(inner: &'a dyn EffectHandler) -> Self {
        Self {
            inner,
            tape: EffectTraceTape::new(),
        }
    }

    /// Clone the recorded effect trace.
    #[must_use]
    pub fn effect_trace(&self) -> Vec<EffectTraceEntry> {
        self.tape.entries()
    }
}

/// A replay-mode handler that serves recorded effect outcomes in order.
pub struct ReplayEffectHandler<'a> {
    entries: Arc<[EffectTraceEntry]>,
    cursor: Mutex<usize>,
    fallback: Option<&'a dyn EffectHandler>,
}

impl<'a> ReplayEffectHandler<'a> {
    /// Build a replay handler without fallback behavior.
    #[must_use]
    pub fn new<E>(entries: E) -> Self
    where
        E: Into<Arc<[EffectTraceEntry]>>,
    {
        Self {
            entries: entries.into(),
            cursor: Mutex::new(0),
            fallback: None,
        }
    }

    /// Build a replay handler with fallback behavior for unsupported entries.
    #[must_use]
    pub fn with_fallback<E>(entries: E, fallback: &'a dyn EffectHandler) -> Self
    where
        E: Into<Arc<[EffectTraceEntry]>>,
    {
        Self {
            entries: entries.into(),
            cursor: Mutex::new(0),
            fallback: Some(fallback),
        }
    }

    /// Number of unconsumed entries.
    ///
    /// # Panics
    ///
    /// Panics if the internal mutex is poisoned.
    #[must_use]
    pub fn remaining(&self) -> usize {
        let cursor = *self
            .cursor
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        self.entries.len().saturating_sub(cursor)
    }

    fn next_entry(&self, expected_kind: &str) -> Result<EffectTraceEntry, String> {
        let mut cursor = self
            .cursor
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let idx = *cursor;
        let Some(entry) = self.entries.get(idx) else {
            return Err(format!(
                "replay trace exhausted at index {idx}, expected {expected_kind}"
            ));
        };
        if entry.effect_kind != expected_kind {
            return Err(format!(
                "replay trace kind mismatch at index {idx}: expected {expected_kind}, got {}",
                entry.effect_kind
            ));
        }
        *cursor = cursor.saturating_add(1);
        Ok(entry.clone())
    }

    fn peek_entry_kind(&self) -> Option<String> {
        let cursor = *self
            .cursor
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        self.entries
            .get(cursor)
            .map(|entry| entry.effect_kind.clone())
    }

    fn parse_send_decision(
        outputs: &JsonValue,
        explicit_payload: Option<Value>,
    ) -> Option<SendDecision> {
        let decision = outputs.get("decision").and_then(JsonValue::as_str)?;
        match decision {
            "deliver" => {
                let payload = outputs
                    .get("payload")
                    .and_then(|value| serde_json::from_value(value.clone()).ok())
                    .or(explicit_payload)
                    .unwrap_or(Value::Unit);
                Some(SendDecision::Deliver(payload))
            }
            "drop" => Some(SendDecision::Drop),
            "defer" => Some(SendDecision::Defer),
            _ => None,
        }
    }

    fn parse_acquire_decision(outputs: &JsonValue) -> Option<AcquireDecision> {
        let decision = outputs.get("decision").and_then(JsonValue::as_str)?;
        match decision {
            "grant" => {
                let evidence = outputs
                    .get("evidence")
                    .and_then(|value| serde_json::from_value(value.clone()).ok())
                    .unwrap_or(Value::Unit);
                Some(AcquireDecision::Grant(evidence))
            }
            "block" => Some(AcquireDecision::Block),
            _ => None,
        }
    }
}
