//! Effect handler trait for the VM.
//!
//! The host (simulator, application, etc.) implements this trait to provide
//! material-specific behavior: computing payloads for sends, processing
//! received values, and performing integration steps.
//!
//! This is intentionally **not** the same as `telltale_choreography::ChoreoHandler`:
//! the VM handler is synchronous, session-local, and operates on bytecode state,
//! while `ChoreoHandler` is an async, typed transport abstraction for generated
//! choreography code.

use crate::coroutine::Value;
use crate::output_condition::OutputConditionHint;
use crate::session::SessionId;
use serde::{Deserialize, Serialize};
use serde_json::json;
use serde_json::Value as JsonValue;
use std::collections::BTreeSet;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Mutex;

/// Topology perturbation event carried in effect traces.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum TopologyPerturbation {
    /// Crash event for one site/participant.
    Crash {
        /// Crashed site identifier.
        site: String,
    },
    /// Partition event between two participants.
    Partition {
        /// Source endpoint/site.
        from: String,
        /// Destination endpoint/site.
        to: String,
    },
    /// Heal event for a previously partitioned pair.
    Heal {
        /// Source endpoint/site.
        from: String,
        /// Destination endpoint/site.
        to: String,
    },
}

impl TopologyPerturbation {
    /// Apply this perturbation to runtime topology state.
    pub fn apply_to(
        &self,
        crashed_sites: &mut BTreeSet<String>,
        partitioned_edges: &mut BTreeSet<(String, String)>,
    ) {
        match self {
            Self::Crash { site } => {
                crashed_sites.insert(site.clone());
            }
            Self::Partition { from, to } => {
                partitioned_edges.insert((from.clone(), to.clone()));
                partitioned_edges.insert((to.clone(), from.clone()));
            }
            Self::Heal { from, to } => {
                partitioned_edges.remove(&(from.clone(), to.clone()));
                partitioned_edges.remove(&(to.clone(), from.clone()));
            }
        }
    }
}

/// Effect-trace entry for replay and determinism checks.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct EffectTraceEntry {
    /// Monotonic effect identifier within one runtime.
    pub effect_id: u64,
    /// Effect kind tag (send_decision, handle_recv, invoke_step, ...).
    pub effect_kind: String,
    /// Serialized effect input payload.
    pub inputs: JsonValue,
    /// Serialized effect output payload.
    pub outputs: JsonValue,
    /// Stable identity of the handler implementation.
    pub handler_identity: String,
    /// Deterministic ordering key used in replay comparisons.
    pub ordering_key: u64,
    /// Optional topology perturbation payload.
    pub topology: Option<TopologyPerturbation>,
}

/// Decision returned by [`EffectHandler::send_decision`].
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum SendDecision {
    /// Deliver the payload immediately (enqueue to buffer).
    Deliver(Value),
    /// Drop the message (sender still advances).
    Drop,
    /// Defer delivery (message handled by middleware).
    Defer,
}

/// Decision returned by [`EffectHandler::handle_acquire`].
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum AcquireDecision {
    /// Acquire succeeded and produced evidence.
    Grant(Value),
    /// Acquire denied and should block.
    Block,
}

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
            .expect("effect trace tape lock poisoned")
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
            .expect("effect trace tape lock poisoned")
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
    entries: Vec<EffectTraceEntry>,
    cursor: Mutex<usize>,
    fallback: Option<&'a dyn EffectHandler>,
}

impl<'a> ReplayEffectHandler<'a> {
    /// Build a replay handler without fallback behavior.
    #[must_use]
    pub fn new(entries: Vec<EffectTraceEntry>) -> Self {
        Self {
            entries,
            cursor: Mutex::new(0),
            fallback: None,
        }
    }

    /// Build a replay handler with fallback behavior for unsupported entries.
    #[must_use]
    pub fn with_fallback(entries: Vec<EffectTraceEntry>, fallback: &'a dyn EffectHandler) -> Self {
        Self {
            entries,
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
        let cursor = *self.cursor.lock().expect("replay cursor lock poisoned");
        self.entries.len().saturating_sub(cursor)
    }

    fn next_entry(&self, expected_kind: &str) -> Result<EffectTraceEntry, String> {
        let mut cursor = self.cursor.lock().expect("replay cursor lock poisoned");
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
        let cursor = *self.cursor.lock().expect("replay cursor lock poisoned");
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

    /// Decide how to handle a send, optionally with a precomputed payload.
    ///
    /// Middleware can override this to model loss/delay/corruption. The default
    /// behavior computes a payload via `handle_send` unless one is provided.
    ///
    /// # Errors
    ///
    /// Returns an error string if the handler fails.
    #[allow(clippy::too_many_arguments)]
    fn send_decision(
        &self,
        _sid: SessionId,
        role: &str,
        partner: &str,
        label: &str,
        state: &[Value],
        payload: Option<Value>,
    ) -> Result<SendDecision, String> {
        if let Some(payload) = payload {
            Ok(SendDecision::Deliver(payload))
        } else {
            self.handle_send(role, partner, label, state)
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
    /// Called when executing a multi-branch Send (internal choice). The handler
    /// receives the available labels and returns the chosen one. Matches the Lean
    /// `stepChoose` semantics where the handler/process decides which label to select.
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

    fn send_decision(
        &self,
        sid: SessionId,
        role: &str,
        partner: &str,
        label: &str,
        state: &[Value],
        payload: Option<Value>,
    ) -> Result<SendDecision, String> {
        (**self).send_decision(sid, role, partner, label, state, payload)
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

    fn send_decision(
        &self,
        sid: SessionId,
        role: &str,
        partner: &str,
        label: &str,
        state: &[Value],
        payload: Option<Value>,
    ) -> Result<SendDecision, String> {
        let decision =
            self.inner
                .send_decision(sid, role, partner, label, state, payload.clone())?;
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
                "sid": sid,
                "role": role,
                "partner": partner,
                "label": label,
                "payload_hint": payload,
            }),
            outputs,
            &self.inner.handler_identity(),
            None,
        );
        Ok(decision)
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

impl EffectHandler for ReplayEffectHandler<'_> {
    fn handler_identity(&self) -> String {
        "replay_handler".to_string()
    }

    fn handle_send(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        state: &[Value],
    ) -> Result<Value, String> {
        if let Some(fallback) = self.fallback {
            fallback.handle_send(role, partner, label, state)
        } else {
            Ok(Value::Unit)
        }
    }

    fn send_decision(
        &self,
        sid: SessionId,
        role: &str,
        partner: &str,
        label: &str,
        state: &[Value],
        payload: Option<Value>,
    ) -> Result<SendDecision, String> {
        let entry = self.next_entry("send_decision")?;
        if let Some(decision) = Self::parse_send_decision(&entry.outputs, payload.clone()) {
            return Ok(decision);
        }
        if let Some(committed) = entry.outputs.get("committed").and_then(JsonValue::as_bool) {
            if committed {
                return Ok(SendDecision::Deliver(payload.unwrap_or(Value::Unit)));
            }
        }
        if let Some(fallback) = self.fallback {
            return fallback.send_decision(sid, role, partner, label, state, payload);
        }
        Err("replay send_decision missing decision payload".to_string())
    }

    fn handle_recv(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        state: &mut Vec<Value>,
        payload: &Value,
    ) -> Result<(), String> {
        self.next_entry("handle_recv")?;
        if let Some(fallback) = self.fallback {
            return fallback.handle_recv(role, partner, label, state, payload);
        }
        Ok(())
    }

    fn handle_choose(
        &self,
        role: &str,
        partner: &str,
        labels: &[String],
        state: &[Value],
    ) -> Result<String, String> {
        let entry = self.next_entry("handle_choose")?;
        if let Some(chosen) = entry.outputs.get("label").and_then(JsonValue::as_str) {
            return Ok(chosen.to_string());
        }
        if let Some(fallback) = self.fallback {
            return fallback.handle_choose(role, partner, labels, state);
        }
        Err("replay handle_choose missing chosen label".to_string())
    }

    fn step(&self, role: &str, state: &mut Vec<Value>) -> Result<(), String> {
        self.next_entry("invoke_step")?;
        if let Some(fallback) = self.fallback {
            return fallback.step(role, state);
        }
        Ok(())
    }

    fn handle_acquire(
        &self,
        sid: SessionId,
        role: &str,
        layer: &str,
        state: &[Value],
    ) -> Result<AcquireDecision, String> {
        let entry = self.next_entry("handle_acquire")?;
        if let Some(decision) = Self::parse_acquire_decision(&entry.outputs) {
            return Ok(decision);
        }
        if let Some(granted) = entry.outputs.get("granted").and_then(JsonValue::as_bool) {
            if granted {
                return Ok(AcquireDecision::Grant(Value::Unit));
            }
        }
        if let Some(fallback) = self.fallback {
            return fallback.handle_acquire(sid, role, layer, state);
        }
        Err("replay handle_acquire missing acquire decision".to_string())
    }

    fn handle_release(
        &self,
        sid: SessionId,
        role: &str,
        layer: &str,
        evidence: &Value,
        state: &[Value],
    ) -> Result<(), String> {
        self.next_entry("handle_release")?;
        if let Some(fallback) = self.fallback {
            return fallback.handle_release(sid, role, layer, evidence, state);
        }
        Ok(())
    }

    fn topology_events(&self, _tick: u64) -> Result<Vec<TopologyPerturbation>, String> {
        let mut events = Vec::new();
        while self.peek_entry_kind().as_deref() == Some("topology_event") {
            let entry = self.next_entry("topology_event")?;
            if let Some(topology) = entry.topology {
                events.push(topology);
                continue;
            }
            if let Some(raw) = entry.outputs.get("topology") {
                if let Ok(topology) = serde_json::from_value::<TopologyPerturbation>(raw.clone()) {
                    events.push(topology);
                }
            }
        }
        Ok(events)
    }

    fn output_condition_hint(
        &self,
        sid: SessionId,
        role: &str,
        state: &[Value],
    ) -> Option<OutputConditionHint> {
        self.fallback
            .and_then(|fallback| fallback.output_condition_hint(sid, role, state))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};

    struct AlternatingHandler {
        counter: AtomicUsize,
    }

    impl AlternatingHandler {
        fn new() -> Self {
            Self {
                counter: AtomicUsize::new(0),
            }
        }
    }

    impl EffectHandler for AlternatingHandler {
        fn handle_send(
            &self,
            _role: &str,
            _partner: &str,
            _label: &str,
            _state: &[Value],
        ) -> Result<Value, String> {
            Ok(Value::Int(1))
        }

        fn send_decision(
            &self,
            _sid: SessionId,
            _role: &str,
            _partner: &str,
            _label: &str,
            _state: &[Value],
            payload: Option<Value>,
        ) -> Result<SendDecision, String> {
            let idx = self.counter.fetch_add(1, Ordering::Relaxed);
            if idx.is_multiple_of(2) {
                Ok(SendDecision::Deliver(
                    payload.unwrap_or(Value::Int(idx as i64)),
                ))
            } else {
                Ok(SendDecision::Drop)
            }
        }

        fn handle_recv(
            &self,
            _role: &str,
            _partner: &str,
            _label: &str,
            _state: &mut Vec<Value>,
            _payload: &Value,
        ) -> Result<(), String> {
            Ok(())
        }

        fn handle_choose(
            &self,
            _role: &str,
            _partner: &str,
            labels: &[String],
            _state: &[Value],
        ) -> Result<String, String> {
            labels
                .first()
                .cloned()
                .ok_or_else(|| "no labels".to_string())
        }

        fn step(&self, _role: &str, _state: &mut Vec<Value>) -> Result<(), String> {
            Ok(())
        }
    }

    #[test]
    fn recording_and_replay_send_decisions_roundtrip() {
        let base = AlternatingHandler::new();
        let recorder = RecordingEffectHandler::new(&base);

        let first = recorder
            .send_decision(0, "A", "B", "m", &[], Some(Value::Int(7)))
            .expect("first decision");
        let second = recorder
            .send_decision(0, "A", "B", "m", &[], Some(Value::Int(8)))
            .expect("second decision");
        assert!(matches!(first, SendDecision::Deliver(_)));
        assert!(matches!(second, SendDecision::Drop));

        let replay = ReplayEffectHandler::new(recorder.effect_trace());
        let replay_first = replay
            .send_decision(0, "A", "B", "m", &[], Some(Value::Int(0)))
            .expect("replay first decision");
        let replay_second = replay
            .send_decision(0, "A", "B", "m", &[], Some(Value::Int(0)))
            .expect("replay second decision");
        assert!(matches!(replay_first, SendDecision::Deliver(_)));
        assert!(matches!(replay_second, SendDecision::Drop));
        assert_eq!(replay.remaining(), 0);
    }

    #[test]
    fn recording_and_replay_topology_events_roundtrip() {
        struct TopologyOnce {
            emitted: AtomicUsize,
        }

        impl EffectHandler for TopologyOnce {
            fn handle_send(
                &self,
                _role: &str,
                _partner: &str,
                _label: &str,
                _state: &[Value],
            ) -> Result<Value, String> {
                Ok(Value::Unit)
            }

            fn handle_recv(
                &self,
                _role: &str,
                _partner: &str,
                _label: &str,
                _state: &mut Vec<Value>,
                _payload: &Value,
            ) -> Result<(), String> {
                Ok(())
            }

            fn handle_choose(
                &self,
                _role: &str,
                _partner: &str,
                labels: &[String],
                _state: &[Value],
            ) -> Result<String, String> {
                labels
                    .first()
                    .cloned()
                    .ok_or_else(|| "no labels".to_string())
            }

            fn step(&self, _role: &str, _state: &mut Vec<Value>) -> Result<(), String> {
                Ok(())
            }

            fn topology_events(&self, _tick: u64) -> Result<Vec<TopologyPerturbation>, String> {
                let idx = self.emitted.fetch_add(1, Ordering::Relaxed);
                if idx == 0 {
                    Ok(vec![TopologyPerturbation::Crash {
                        site: "node-a".to_string(),
                    }])
                } else {
                    Ok(Vec::new())
                }
            }
        }

        let base = TopologyOnce {
            emitted: AtomicUsize::new(0),
        };
        let recorder = RecordingEffectHandler::new(&base);
        let first = recorder.topology_events(1).expect("record topology");
        let second = recorder.topology_events(2).expect("record topology");
        assert_eq!(first.len(), 1);
        assert!(second.is_empty());

        let replay = ReplayEffectHandler::new(recorder.effect_trace());
        let replay_first = replay.topology_events(1).expect("replay topology");
        let replay_second = replay.topology_events(2).expect("replay topology");
        assert_eq!(replay_first.len(), 1);
        assert!(replay_second.is_empty());
        assert_eq!(replay.remaining(), 0);
    }
}
