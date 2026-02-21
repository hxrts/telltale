//! Effect handler trait for the VM.
//!
//! The host (simulator, application, etc.) implements this trait to provide
//! material-specific behavior: computing payloads for sends, processing
//! received values, and performing integration steps.
//!
//! Normative integration contract:
//! - `topology_events` is queried once per scheduler round before pick/dispatch.
//! - `send_decision` is the canonical send hook for `Send` and `Offer`.
//! - `handle_recv` is the canonical receive hook for `Receive` and `Choose`.
//! - `step` is called only from the `Invoke` instruction.
//! - `output_condition_hint` is queried only for eventful commits.
//! - `handle_send` and `handle_choose` are compatibility hooks.
//!
//! This is intentionally **not** the same as `telltale_choreography::ChoreoHandler`:
//! the VM handler is synchronous, session-local, and operates on bytecode state,
//! while `ChoreoHandler` is an async, typed transport abstraction for generated
//! choreography code.
//!
//! Integration guide: [`Effect Handlers and Session Types`](../../../docs/10_effect_session_bridge.md).

use crate::coroutine::Value;
use crate::output_condition::OutputConditionHint;
use crate::session::SessionId;
use serde::{Deserialize, Serialize};
use serde_json::json;
use serde_json::Value as JsonValue;
use std::collections::BTreeSet;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Mutex;
use std::time::Duration;

/// Message corruption flavor for topology perturbations.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum CorruptionType {
    /// Flip bits in payload bytes.
    BitFlip,
    /// Truncate payload bytes.
    Truncation,
    /// Replace payload with unit/default value.
    PayloadErase,
}

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
    /// Corruption event for one directed link.
    Corrupt {
        /// Source endpoint/site.
        from: String,
        /// Destination endpoint/site.
        to: String,
        /// Corruption strategy.
        corruption: CorruptionType,
    },
    /// Timeout event for one site.
    Timeout {
        /// Timed-out site identifier.
        site: String,
        /// Timeout duration.
        duration: Duration,
    },
}

impl TopologyPerturbation {
    /// Deterministic ordering key for batches received in the same tick.
    #[must_use]
    pub fn ordering_key(&self) -> (u8, String, String, u128) {
        match self {
            Self::Crash { site } => (0, site.clone(), String::new(), 0),
            Self::Partition { from, to } => (1, from.clone(), to.clone(), 0),
            Self::Heal { from, to } => (2, from.clone(), to.clone(), 0),
            Self::Corrupt {
                from,
                to,
                corruption,
            } => {
                let corruption_rank = match corruption {
                    CorruptionType::BitFlip => 0,
                    CorruptionType::Truncation => 1,
                    CorruptionType::PayloadErase => 2,
                };
                (3, from.clone(), to.clone(), corruption_rank)
            }
            Self::Timeout { site, duration } => {
                (4, site.clone(), String::new(), duration.as_nanos())
            }
        }
    }

    /// Return crashed site if this is a crash event.
    #[must_use]
    pub fn crashed_site(&self) -> Option<&str> {
        match self {
            Self::Crash { site } => Some(site.as_str()),
            _ => None,
        }
    }

    /// Return partition endpoints if this is a partition event.
    #[must_use]
    pub fn partition_pair(&self) -> Option<(&str, &str)> {
        match self {
            Self::Partition { from, to } => Some((from.as_str(), to.as_str())),
            _ => None,
        }
    }

    /// Return healed endpoints if this is a heal event.
    #[must_use]
    pub fn healed_pair(&self) -> Option<(&str, &str)> {
        match self {
            Self::Heal { from, to } => Some((from.as_str(), to.as_str())),
            _ => None,
        }
    }

    /// Return corruption edge/policy if this is a corruption event.
    #[must_use]
    pub fn corruption_edge(&self) -> Option<(&str, &str, CorruptionType)> {
        match self {
            Self::Corrupt {
                from,
                to,
                corruption,
            } => Some((from.as_str(), to.as_str(), corruption.clone())),
            _ => None,
        }
    }

    /// Return timeout site/duration if this is a timeout event.
    #[must_use]
    pub fn timeout_site(&self) -> Option<(&str, Duration)> {
        match self {
            Self::Timeout { site, duration } => Some((site.as_str(), *duration)),
            _ => None,
        }
    }

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
            Self::Corrupt { .. } | Self::Timeout { .. } => {}
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

/// Structured input for [`EffectHandler::send_decision`].
#[derive(Debug, Clone)]
pub struct SendDecisionInput<'a> {
    /// Session context for the send.
    pub sid: SessionId,
    /// Sending role.
    pub role: &'a str,
    /// Receiving role.
    pub partner: &'a str,
    /// Message label.
    pub label: &'a str,
    /// Current register state.
    pub state: &'a [Value],
    /// Optional precomputed payload.
    pub payload: Option<Value>,
}

/// Coarse payload shape for optional send fast-path dispatch.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum SendPayloadKind {
    /// `Value::Unit`.
    Unit,
    /// `Value::Nat`.
    Nat,
    /// `Value::Bool`.
    Bool,
    /// `Value::Str`.
    Str,
    /// `Value::Prod`.
    Prod,
    /// `Value::Endpoint`.
    Endpoint,
}

impl SendPayloadKind {
    /// Classify one runtime value into a payload kind.
    #[must_use]
    pub fn from_value(value: &Value) -> Self {
        match value {
            Value::Unit => Self::Unit,
            Value::Nat(_) => Self::Nat,
            Value::Bool(_) => Self::Bool,
            Value::Str(_) => Self::Str,
            Value::Prod(_, _) => Self::Prod,
            Value::Endpoint(_) => Self::Endpoint,
        }
    }
}

/// Optional metadata for fast send-decision lookup paths.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SendDecisionFastPathInput<'a> {
    /// Deterministic key for per-host cache lookup.
    pub key: u64,
    /// Session context for the send.
    pub sid: SessionId,
    /// Sending role.
    pub role: &'a str,
    /// Receiving role.
    pub partner: &'a str,
    /// Message label.
    pub label: &'a str,
    /// Optional payload kind hint.
    pub payload_kind: Option<SendPayloadKind>,
}

impl<'a> SendDecisionFastPathInput<'a> {
    /// Build fast-path metadata for one send decision.
    #[must_use]
    pub fn new(
        sid: SessionId,
        role: &'a str,
        partner: &'a str,
        label: &'a str,
        payload: Option<&Value>,
    ) -> Self {
        let payload_kind = payload.map(SendPayloadKind::from_value);
        Self {
            key: send_fast_path_key(sid, role, partner, label, payload_kind),
            sid,
            role,
            partner,
            label,
            payload_kind,
        }
    }
}

/// Classify a stringly-typed effect error into a structured category.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum EffectErrorCategory {
    /// Timeout/deadline failure.
    Timeout,
    /// Transport/runtime unavailable.
    Unavailable,
    /// Invalid host input or payload contract.
    InvalidInput,
    /// Replay/determinism contract failure.
    Determinism,
    /// Topology ingress or topology mutation failure.
    Topology,
    /// Host contract assertion or identity violation.
    ContractViolation,
    /// Unclassified failure.
    Unknown,
}

/// Structured view of host effect errors.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct EffectError {
    /// Typed category inferred from message content.
    pub category: EffectErrorCategory,
    /// Original host error string.
    pub message: String,
}

impl EffectError {
    /// Build a structured error from a raw host message.
    #[must_use]
    pub fn classify(message: impl Into<String>) -> Self {
        let message = message.into();
        Self {
            category: classify_effect_error(&message),
            message,
        }
    }
}

impl core::fmt::Display for EffectError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{:?}: {}", self.category, self.message)
    }
}

impl std::error::Error for EffectError {}

impl From<EffectError> for String {
    fn from(value: EffectError) -> Self {
        value.message
    }
}

/// Classify a raw error message into a coarse effect category.
#[must_use]
pub fn classify_effect_error(message: &str) -> EffectErrorCategory {
    let lower = message.to_ascii_lowercase();
    if lower.contains("timeout") || lower.contains("timed out") || lower.contains("deadline") {
        return EffectErrorCategory::Timeout;
    }
    if lower.contains("topology")
        || lower.contains("partition")
        || lower.contains("crash")
        || lower.contains("corrupt")
        || lower.contains("heal")
    {
        return EffectErrorCategory::Topology;
    }
    if lower.contains("determinism")
        || lower.contains("replay")
        || lower.contains("mismatch")
        || lower.contains("nondetermin")
        || lower.contains("ordering")
    {
        return EffectErrorCategory::Determinism;
    }
    if lower.contains("contract") || lower.contains("assert") || lower.contains("identity") {
        return EffectErrorCategory::ContractViolation;
    }
    if lower.contains("unavailable")
        || lower.contains("disconnect")
        || lower.contains("closed")
        || lower.contains("missing")
        || lower.contains("not found")
        || lower.contains("exhausted")
    {
        return EffectErrorCategory::Unavailable;
    }
    if lower.contains("invalid")
        || lower.contains("unknown label")
        || lower.contains("malformed")
        || lower.contains("type")
        || lower.contains("register")
    {
        return EffectErrorCategory::InvalidInput;
    }
    EffectErrorCategory::Unknown
}

/// Build a typed error wrapper from a raw host error message.
#[must_use]
pub fn classify_effect_error_owned(message: impl Into<String>) -> EffectError {
    EffectError::classify(message)
}

/// Deterministic key for optional send fast-path caches.
#[must_use]
pub fn send_fast_path_key(
    sid: SessionId,
    role: &str,
    partner: &str,
    label: &str,
    payload_kind: Option<SendPayloadKind>,
) -> u64 {
    const FNV_OFFSET: u64 = 14_695_981_039_346_656_037;
    const FNV_PRIME: u64 = 1_099_511_628_211;
    fn mix(mut hash: u64, bytes: &[u8]) -> u64 {
        for byte in bytes {
            hash ^= u64::from(*byte);
            hash = hash.wrapping_mul(FNV_PRIME);
        }
        hash
    }
    let mut hash = FNV_OFFSET;
    hash = mix(hash, &sid.to_le_bytes());
    hash = mix(hash, role.as_bytes());
    hash = mix(hash, &[0x1f]);
    hash = mix(hash, partner.as_bytes());
    hash = mix(hash, &[0x1f]);
    hash = mix(hash, label.as_bytes());
    if let Some(kind) = payload_kind {
        let tag = match kind {
            SendPayloadKind::Unit => 0_u8,
            SendPayloadKind::Nat => 1_u8,
            SendPayloadKind::Bool => 2_u8,
            SendPayloadKind::Str => 3_u8,
            SendPayloadKind::Prod => 4_u8,
            SendPayloadKind::Endpoint => 5_u8,
        };
        hash = mix(hash, &[tag]);
    }
    hash
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

    fn send_decision(&self, input: SendDecisionInput<'_>) -> Result<SendDecision, String> {
        let entry = self.next_entry("send_decision")?;
        if let Some(decision) = Self::parse_send_decision(&entry.outputs, input.payload.clone()) {
            return Ok(decision);
        }
        if let Some(committed) = entry.outputs.get("committed").and_then(JsonValue::as_bool) {
            if committed {
                return Ok(SendDecision::Deliver(input.payload.unwrap_or(Value::Unit)));
            }
        }
        if let Some(fallback) = self.fallback {
            return fallback.send_decision(input);
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
            Ok(Value::Nat(1))
        }

        #[allow(clippy::as_conversions, clippy::cast_possible_wrap)]
        fn send_decision(&self, input: SendDecisionInput<'_>) -> Result<SendDecision, String> {
            let idx = self.counter.fetch_add(1, Ordering::Relaxed);
            if idx % 2 == 0 {
                Ok(SendDecision::Deliver(
                    input.payload.unwrap_or(Value::Nat(idx as u64)),
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
            .send_decision(SendDecisionInput {
                sid: 0,
                role: "A",
                partner: "B",
                label: "m",
                state: &[],
                payload: Some(Value::Nat(7)),
            })
            .expect("first decision");
        let second = recorder
            .send_decision(SendDecisionInput {
                sid: 0,
                role: "A",
                partner: "B",
                label: "m",
                state: &[],
                payload: Some(Value::Nat(8)),
            })
            .expect("second decision");
        assert!(matches!(first, SendDecision::Deliver(_)));
        assert!(matches!(second, SendDecision::Drop));

        let replay = ReplayEffectHandler::new(recorder.effect_trace());
        let replay_first = replay
            .send_decision(SendDecisionInput {
                sid: 0,
                role: "A",
                partner: "B",
                label: "m",
                state: &[],
                payload: Some(Value::Nat(0)),
            })
            .expect("replay first decision");
        let replay_second = replay
            .send_decision(SendDecisionInput {
                sid: 0,
                role: "A",
                partner: "B",
                label: "m",
                state: &[],
                payload: Some(Value::Nat(0)),
            })
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

    #[test]
    fn classify_effect_error_categories_from_strings() {
        assert_eq!(
            classify_effect_error("timed out waiting for recv"),
            EffectErrorCategory::Timeout
        );
        assert_eq!(
            classify_effect_error("topology partition mismatch"),
            EffectErrorCategory::Topology
        );
        assert_eq!(
            classify_effect_error("replay trace kind mismatch"),
            EffectErrorCategory::Determinism
        );
        assert_eq!(
            classify_effect_error("handler identity contract violated"),
            EffectErrorCategory::ContractViolation
        );
        assert_eq!(
            classify_effect_error("channel unavailable"),
            EffectErrorCategory::Unavailable
        );
        assert_eq!(
            classify_effect_error("invalid payload type"),
            EffectErrorCategory::InvalidInput
        );
    }

    #[test]
    fn send_fast_path_key_is_deterministic_for_same_inputs() {
        let left = send_fast_path_key(7, "A", "B", "msg", Some(SendPayloadKind::Nat));
        let right = send_fast_path_key(7, "A", "B", "msg", Some(SendPayloadKind::Nat));
        assert_eq!(left, right);
        assert_ne!(
            left,
            send_fast_path_key(7, "A", "B", "msg2", Some(SendPayloadKind::Nat))
        );
    }
}
