/// Corruption policy for topology perturbations.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq, PartialOrd, Ord)]
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
