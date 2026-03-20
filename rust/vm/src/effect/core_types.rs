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
            } => Some((from.as_str(), to.as_str(), *corruption)),
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
    /// Optional nominal interface classification for this effect.
    #[serde(default)]
    pub effect_interface: Option<String>,
    /// Optional nominal operation classification for this effect.
    #[serde(default)]
    pub effect_operation: Option<String>,
    /// Deterministic ordering key used in replay comparisons.
    pub ordering_key: u64,
    /// Optional topology perturbation payload.
    pub topology: Option<TopologyPerturbation>,
}

/// Infer a nominal interface/operation pair from one runtime effect kind.
#[must_use]
pub fn infer_effect_interface_and_operation(
    effect_kind: &str,
) -> (Option<String>, Option<String>) {
    match effect_kind {
        "send_decision" => (Some("Transport".to_string()), Some("sendDecision".to_string())),
        "handle_recv" => (Some("Transport".to_string()), Some("handleRecv".to_string())),
        "handle_choose" => (Some("Transport".to_string()), Some("handleChoose".to_string())),
        "invoke_step" => (Some("Runtime".to_string()), Some("invoke".to_string())),
        "handle_acquire" => (Some("Guard".to_string()), Some("acquire".to_string())),
        "handle_release" => (Some("Guard".to_string()), Some("release".to_string())),
        "topology_events" | "topology_event" => {
            (Some("Runtime".to_string()), Some("topologyEvents".to_string()))
        }
        _ => (None, None),
    }
}

/// Decision returned by [`EffectHandler::send_decision`].
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
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

/// Typed failure kinds at the VM effect boundary.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum EffectFailureKind {
    /// The requested action was denied by host policy or readiness rules.
    Denied,
    /// The requested action timed out.
    Timeout,
    /// The requested action was explicitly cancelled.
    Cancelled,
    /// The caller's authority token is stale.
    StaleAuthority,
    /// The supplied evidence or witness is invalid.
    InvalidEvidence,
    /// Transport/runtime unavailable.
    Unavailable,
    /// Invalid host input or payload contract.
    InvalidInput,
    /// Replay/determinism contract failure.
    Determinism,
    /// Topology ingress or topology mutation failure.
    TopologyDisruption,
    /// Host contract assertion or identity violation.
    ContractViolation,
    /// Unclassified failure.
    Unknown,
}

/// Structured failure at the host effect boundary.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct EffectFailure {
    /// Typed failure kind.
    pub kind: EffectFailureKind,
    /// Human-readable failure detail.
    pub message: String,
}

impl EffectFailure {
    /// Build one failure value.
    #[must_use]
    pub fn new(kind: EffectFailureKind, message: impl Into<String>) -> Self {
        Self {
            kind,
            message: message.into(),
        }
    }

    /// Convenience constructor for denied outcomes.
    #[must_use]
    pub fn denied(message: impl Into<String>) -> Self {
        Self::new(EffectFailureKind::Denied, message)
    }

    /// Convenience constructor for timeout outcomes.
    #[must_use]
    pub fn timeout(message: impl Into<String>) -> Self {
        Self::new(EffectFailureKind::Timeout, message)
    }

    /// Convenience constructor for cancelled outcomes.
    #[must_use]
    pub fn cancelled(message: impl Into<String>) -> Self {
        Self::new(EffectFailureKind::Cancelled, message)
    }

    /// Convenience constructor for stale-authority failures.
    #[must_use]
    pub fn stale_authority(message: impl Into<String>) -> Self {
        Self::new(EffectFailureKind::StaleAuthority, message)
    }

    /// Convenience constructor for invalid-evidence failures.
    #[must_use]
    pub fn invalid_evidence(message: impl Into<String>) -> Self {
        Self::new(EffectFailureKind::InvalidEvidence, message)
    }

    /// Convenience constructor for unavailable failures.
    #[must_use]
    pub fn unavailable(message: impl Into<String>) -> Self {
        Self::new(EffectFailureKind::Unavailable, message)
    }

    /// Convenience constructor for invalid-input failures.
    #[must_use]
    pub fn invalid_input(message: impl Into<String>) -> Self {
        Self::new(EffectFailureKind::InvalidInput, message)
    }

    /// Convenience constructor for determinism failures.
    #[must_use]
    pub fn determinism(message: impl Into<String>) -> Self {
        Self::new(EffectFailureKind::Determinism, message)
    }

    /// Convenience constructor for topology failures.
    #[must_use]
    pub fn topology_disruption(message: impl Into<String>) -> Self {
        Self::new(EffectFailureKind::TopologyDisruption, message)
    }

    /// Convenience constructor for contract-violation failures.
    #[must_use]
    pub fn contract_violation(message: impl Into<String>) -> Self {
        Self::new(EffectFailureKind::ContractViolation, message)
    }
}

impl core::fmt::Display for EffectFailure {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{:?}: {}", self.kind, self.message)
    }
}

impl std::error::Error for EffectFailure {}

/// Typed outcome for one VM effect callback.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum EffectResult<T> {
    /// Callback completed successfully and produced a value.
    Success(T),
    /// Callback requested a clean block rather than a hard failure.
    Blocked,
    /// Callback failed with a typed failure.
    Failure(EffectFailure),
}

impl<T> EffectResult<T> {
    /// Construct a successful effect outcome.
    #[must_use]
    pub fn success(value: T) -> Self {
        Self::Success(value)
    }

    /// Construct a blocked effect outcome.
    #[must_use]
    pub fn blocked() -> Self {
        Self::Blocked
    }

    /// Construct a failed effect outcome.
    #[must_use]
    pub fn failure(failure: EffectFailure) -> Self {
        Self::Failure(failure)
    }

    /// Map the success payload while preserving blocked/failure outcomes.
    #[must_use]
    pub fn map_success<U>(self, f: impl FnOnce(T) -> U) -> EffectResult<U> {
        match self {
            Self::Success(value) => EffectResult::Success(f(value)),
            Self::Blocked => EffectResult::Blocked,
            Self::Failure(failure) => EffectResult::Failure(failure),
        }
    }

    /// Extract the success payload or convert `Blocked` into a failure.
    ///
    /// # Errors
    ///
    /// Returns the typed failure directly, or a supplied contract-violation
    /// failure when blocking is not valid for the current callback.
    pub fn expect_success(
        self,
        blocked_failure: impl FnOnce() -> EffectFailure,
    ) -> Result<T, EffectFailure> {
        match self {
            Self::Success(value) => Ok(value),
            Self::Blocked => Err(blocked_failure()),
            Self::Failure(failure) => Err(failure),
        }
    }
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
