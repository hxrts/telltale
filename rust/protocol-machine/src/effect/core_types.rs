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

/// Authority class attached to one effect operation.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum EffectAuthorityClass {
    /// The outcome may authorize parity-critical semantic progression.
    Authoritative,
    /// The outcome performs guest-runtime command work but does not itself
    /// justify authoritative semantic truth.
    Command,
    /// The outcome is observational only and must not be treated as
    /// authoritative semantic truth.
    Observe,
}

/// Admission policy for one effect operation.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum EffectAdmissibility {
    /// Always admissible once the handler is bound.
    Always,
    /// Requires declaration in a choreography `uses` surface.
    DeclaredUseOnly,
    /// Reserved for guest-runtime internal handling.
    InternalOnly,
}

/// Totality contract for one effect operation.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum EffectTotality {
    /// Operation must complete without blocking.
    Immediate,
    /// Operation may block and later resume.
    MayBlock,
}

/// Timeout contract attached to one effect operation.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum EffectTimeoutPolicy {
    /// No dedicated timeout contract beyond the enclosing operation budget.
    None,
    /// Reuse the enclosing operation budget.
    InheritOperationBudget,
    /// Must carry a dedicated timeout budget in ticks.
    Required {
        /// Timeout budget in ticks when known.
        budget_ticks: Option<u64>,
    },
}

/// Reentrancy policy for one effect operation.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum EffectReentrancyPolicy {
    /// Reentrancy is permitted.
    Allow,
    /// Reject a second live request for the same operation instance.
    RejectSameOperation,
    /// Reject a second live request for the same session/fragment scope.
    RejectSameFragment,
}

/// Handler-domain classification for one effect operation.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum EffectHandlerDomain {
    /// Guest-runtime internal handler responsibility.
    Internal,
    /// Host-runtime external handler responsibility.
    External,
}

/// Runtime metadata for one effect interface operation.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct EffectInterfaceMetadata {
    /// Nominal effect interface name.
    pub interface_name: String,
    /// Nominal effect operation name.
    pub operation_name: String,
    /// Authority class for this operation.
    pub authority_class: EffectAuthorityClass,
    /// Admission policy for this operation.
    pub admissibility: EffectAdmissibility,
    /// Totality contract for this operation.
    pub totality: EffectTotality,
    /// Timeout contract for this operation.
    pub timeout_policy: EffectTimeoutPolicy,
    /// Reentrancy policy for this operation.
    pub reentrancy_policy: EffectReentrancyPolicy,
    /// Handler domain expected to interpret this operation.
    pub handler_domain: EffectHandlerDomain,
}

impl EffectInterfaceMetadata {
    /// Validate one metadata combination.
    ///
    /// # Errors
    ///
    /// Returns a contract error when the metadata encodes an illegal
    /// combination.
    pub fn validate(&self) -> Result<(), EffectFailure> {
        if matches!(self.admissibility, EffectAdmissibility::InternalOnly)
            && !matches!(self.handler_domain, EffectHandlerDomain::Internal)
        {
            return Err(EffectFailure::contract_violation(format!(
                "effect {}.{} is internal-only but is marked for external handling",
                self.interface_name, self.operation_name
            )));
        }

        if matches!(self.authority_class, EffectAuthorityClass::Observe)
            && !matches!(self.totality, EffectTotality::Immediate)
        {
            return Err(EffectFailure::contract_violation(format!(
                "observational effect {}.{} may not use blocking totality",
                self.interface_name, self.operation_name
            )));
        }

        if matches!(self.authority_class, EffectAuthorityClass::Observe)
            && matches!(self.timeout_policy, EffectTimeoutPolicy::Required { .. })
        {
            return Err(EffectFailure::contract_violation(format!(
                "observational effect {}.{} may not require a dedicated timeout budget",
                self.interface_name, self.operation_name
            )));
        }

        if matches!(self.totality, EffectTotality::Immediate)
            && matches!(self.timeout_policy, EffectTimeoutPolicy::Required { .. })
        {
            return Err(EffectFailure::contract_violation(format!(
                "immediate effect {}.{} may not require a dedicated timeout budget",
                self.interface_name, self.operation_name
            )));
        }

        Ok(())
    }

    /// Default runtime metadata for one built-in effect kind.
    #[must_use]
    pub fn for_effect_kind(effect_kind: &str) -> Self {
        let (interface_name, operation_name) = infer_effect_interface_and_operation(effect_kind);
        match effect_kind {
            "send_decision" => Self {
                interface_name: interface_name.unwrap_or_else(|| "Transport".to_string()),
                operation_name: operation_name.unwrap_or_else(|| "sendDecision".to_string()),
                authority_class: EffectAuthorityClass::Command,
                admissibility: EffectAdmissibility::DeclaredUseOnly,
                totality: EffectTotality::Immediate,
                timeout_policy: EffectTimeoutPolicy::None,
                reentrancy_policy: EffectReentrancyPolicy::Allow,
                handler_domain: EffectHandlerDomain::External,
            },
            "handle_recv" => Self {
                interface_name: interface_name.unwrap_or_else(|| "Transport".to_string()),
                operation_name: operation_name.unwrap_or_else(|| "handleRecv".to_string()),
                authority_class: EffectAuthorityClass::Command,
                admissibility: EffectAdmissibility::DeclaredUseOnly,
                totality: EffectTotality::Immediate,
                timeout_policy: EffectTimeoutPolicy::None,
                reentrancy_policy: EffectReentrancyPolicy::Allow,
                handler_domain: EffectHandlerDomain::External,
            },
            "handle_choose" => Self {
                interface_name: interface_name.unwrap_or_else(|| "Transport".to_string()),
                operation_name: operation_name.unwrap_or_else(|| "handleChoose".to_string()),
                authority_class: EffectAuthorityClass::Command,
                admissibility: EffectAdmissibility::DeclaredUseOnly,
                totality: EffectTotality::Immediate,
                timeout_policy: EffectTimeoutPolicy::None,
                reentrancy_policy: EffectReentrancyPolicy::Allow,
                handler_domain: EffectHandlerDomain::External,
            },
            "invoke_step" => Self {
                interface_name: interface_name.unwrap_or_else(|| "Runtime".to_string()),
                operation_name: operation_name.unwrap_or_else(|| "invoke".to_string()),
                authority_class: EffectAuthorityClass::Command,
                admissibility: EffectAdmissibility::DeclaredUseOnly,
                totality: EffectTotality::Immediate,
                timeout_policy: EffectTimeoutPolicy::InheritOperationBudget,
                reentrancy_policy: EffectReentrancyPolicy::RejectSameOperation,
                handler_domain: EffectHandlerDomain::External,
            },
            "handle_acquire" => Self {
                interface_name: interface_name.unwrap_or_else(|| "Guard".to_string()),
                operation_name: operation_name.unwrap_or_else(|| "acquire".to_string()),
                authority_class: EffectAuthorityClass::Authoritative,
                admissibility: EffectAdmissibility::DeclaredUseOnly,
                totality: EffectTotality::MayBlock,
                timeout_policy: EffectTimeoutPolicy::InheritOperationBudget,
                reentrancy_policy: EffectReentrancyPolicy::RejectSameFragment,
                handler_domain: EffectHandlerDomain::External,
            },
            "handle_release" => Self {
                interface_name: interface_name.unwrap_or_else(|| "Guard".to_string()),
                operation_name: operation_name.unwrap_or_else(|| "release".to_string()),
                authority_class: EffectAuthorityClass::Authoritative,
                admissibility: EffectAdmissibility::DeclaredUseOnly,
                totality: EffectTotality::Immediate,
                timeout_policy: EffectTimeoutPolicy::None,
                reentrancy_policy: EffectReentrancyPolicy::RejectSameFragment,
                handler_domain: EffectHandlerDomain::External,
            },
            "topology_events" | "topology_event" => Self {
                interface_name: interface_name.unwrap_or_else(|| "Runtime".to_string()),
                operation_name: operation_name.unwrap_or_else(|| "topologyEvents".to_string()),
                authority_class: EffectAuthorityClass::Authoritative,
                admissibility: EffectAdmissibility::InternalOnly,
                totality: EffectTotality::Immediate,
                timeout_policy: EffectTimeoutPolicy::None,
                reentrancy_policy: EffectReentrancyPolicy::Allow,
                handler_domain: EffectHandlerDomain::Internal,
            },
            "output_condition_hint" => Self {
                interface_name: "Runtime".to_string(),
                operation_name: "outputConditionHint".to_string(),
                authority_class: EffectAuthorityClass::Authoritative,
                admissibility: EffectAdmissibility::DeclaredUseOnly,
                totality: EffectTotality::Immediate,
                timeout_policy: EffectTimeoutPolicy::None,
                reentrancy_policy: EffectReentrancyPolicy::Allow,
                handler_domain: EffectHandlerDomain::External,
            },
            _ => Self {
                interface_name: interface_name.unwrap_or_else(|| "Runtime".to_string()),
                operation_name: operation_name.unwrap_or_else(|| effect_kind.to_string()),
                authority_class: EffectAuthorityClass::Command,
                admissibility: EffectAdmissibility::DeclaredUseOnly,
                totality: EffectTotality::Immediate,
                timeout_policy: EffectTimeoutPolicy::None,
                reentrancy_policy: EffectReentrancyPolicy::Allow,
                handler_domain: EffectHandlerDomain::External,
            },
        }
    }
}

/// One typed runtime effect request.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct EffectRequest {
    /// Optional runtime effect id when known.
    #[serde(default)]
    pub effect_id: Option<u64>,
    /// Scheduler tick at which the request was issued.
    pub tick: u64,
    /// Optional session scope.
    #[serde(default)]
    pub session: Option<SessionId>,
    /// Optional operation identity when known.
    #[serde(default)]
    pub operation_id: Option<String>,
    /// Interface metadata for the request.
    pub metadata: EffectInterfaceMetadata,
    /// Typed request payload.
    pub body: EffectRequestBody,
}

#[allow(missing_docs)]
impl EffectRequest {
    #[must_use]
    fn new(
        tick: u64,
        session: Option<SessionId>,
        operation_id: Option<String>,
        effect_kind: &str,
        body: EffectRequestBody,
    ) -> Self {
        Self {
            effect_id: None,
            tick,
            session,
            operation_id,
            metadata: EffectInterfaceMetadata::for_effect_kind(effect_kind),
            body,
        }
    }

    #[must_use]
    pub fn send_decision(
        tick: u64,
        sid: SessionId,
        operation_id: Option<String>,
        role: impl Into<String>,
        partner: impl Into<String>,
        label: impl Into<String>,
        state: &[Value],
        payload: Option<Value>,
    ) -> Self {
        Self::new(
            tick,
            Some(sid),
            operation_id,
            "send_decision",
            EffectRequestBody::SendDecision {
                role: role.into(),
                partner: partner.into(),
                label: label.into(),
                state: state.to_vec(),
                payload,
            },
        )
    }

    #[must_use]
    pub fn receive(
        tick: u64,
        session: Option<SessionId>,
        operation_id: Option<String>,
        role: impl Into<String>,
        partner: impl Into<String>,
        label: impl Into<String>,
        state: &[Value],
        payload: Value,
    ) -> Self {
        Self::new(
            tick,
            session,
            operation_id,
            "handle_recv",
            EffectRequestBody::Receive {
                role: role.into(),
                partner: partner.into(),
                label: label.into(),
                state: state.to_vec(),
                payload,
            },
        )
    }

    #[must_use]
    pub fn choose(
        tick: u64,
        session: Option<SessionId>,
        operation_id: Option<String>,
        role: impl Into<String>,
        partner: impl Into<String>,
        labels: &[String],
        state: &[Value],
    ) -> Self {
        Self::new(
            tick,
            session,
            operation_id,
            "handle_choose",
            EffectRequestBody::Choose {
                role: role.into(),
                partner: partner.into(),
                labels: labels.to_vec(),
                state: state.to_vec(),
            },
        )
    }

    #[must_use]
    pub fn invoke_step(
        tick: u64,
        session: Option<SessionId>,
        operation_id: Option<String>,
        role: impl Into<String>,
        state: &[Value],
    ) -> Self {
        Self::new(
            tick,
            session,
            operation_id,
            "invoke_step",
            EffectRequestBody::InvokeStep {
                role: role.into(),
                state: state.to_vec(),
            },
        )
    }

    #[must_use]
    pub fn acquire(
        tick: u64,
        sid: SessionId,
        operation_id: Option<String>,
        role: impl Into<String>,
        layer: impl Into<String>,
        state: &[Value],
    ) -> Self {
        Self::new(
            tick,
            Some(sid),
            operation_id,
            "handle_acquire",
            EffectRequestBody::Acquire {
                role: role.into(),
                layer: layer.into(),
                state: state.to_vec(),
            },
        )
    }

    #[must_use]
    pub fn release(
        tick: u64,
        sid: SessionId,
        operation_id: Option<String>,
        role: impl Into<String>,
        layer: impl Into<String>,
        evidence: &Value,
        state: &[Value],
    ) -> Self {
        Self::new(
            tick,
            Some(sid),
            operation_id,
            "handle_release",
            EffectRequestBody::Release {
                role: role.into(),
                layer: layer.into(),
                evidence: evidence.clone(),
                state: state.to_vec(),
            },
        )
    }

    #[must_use]
    pub fn topology_events(tick: u64) -> Self {
        Self::new(
            tick,
            None,
            None,
            "topology_events",
            EffectRequestBody::TopologyEvents { tick },
        )
    }

    #[must_use]
    pub fn output_condition_hint(
        tick: u64,
        sid: SessionId,
        operation_id: Option<String>,
        role: impl Into<String>,
        state: &[Value],
    ) -> Self {
        Self::new(
            tick,
            Some(sid),
            operation_id,
            "output_condition_hint",
            EffectRequestBody::OutputConditionHint {
                role: role.into(),
                state: state.to_vec(),
            },
        )
    }
}

/// Typed request payload families.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[serde(tag = "kind", rename_all = "snake_case")]
#[allow(missing_docs)]
pub enum EffectRequestBody {
    SendDecision {
        role: String,
        partner: String,
        label: String,
        state: Vec<Value>,
        payload: Option<Value>,
    },
    Receive {
        role: String,
        partner: String,
        label: String,
        state: Vec<Value>,
        payload: Value,
    },
    Choose {
        role: String,
        partner: String,
        labels: Vec<String>,
        state: Vec<Value>,
    },
    InvokeStep {
        role: String,
        state: Vec<Value>,
    },
    Acquire {
        role: String,
        layer: String,
        state: Vec<Value>,
    },
    Release {
        role: String,
        layer: String,
        evidence: Value,
        state: Vec<Value>,
    },
    TopologyEvents {
        tick: u64,
    },
    OutputConditionHint {
        role: String,
        state: Vec<Value>,
    },
}

/// Status for one typed effect outcome.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(tag = "status", rename_all = "snake_case")]
#[allow(missing_docs)]
pub enum EffectOutcomeStatus {
    Success,
    Blocked,
    Failure { failure: EffectFailure },
}

/// Typed response payload families.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[serde(tag = "kind", rename_all = "snake_case")]
#[allow(missing_docs)]
pub enum EffectResponse {
    SendDecision { decision: SendDecision },
    Receive { state: Vec<Value> },
    Choose { label: String },
    InvokeStep { state: Vec<Value> },
    Acquire { evidence: Value },
    Release,
    TopologyEvents { events: Vec<TopologyPerturbation> },
    OutputConditionHint { hint: Option<OutputConditionHint> },
}

/// One typed runtime effect outcome.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct EffectOutcome {
    /// Status for this outcome.
    pub status: EffectOutcomeStatus,
    /// Typed response payload when status is success.
    #[serde(default)]
    pub response: Option<EffectResponse>,
}

impl EffectOutcome {
    /// Construct a successful typed effect outcome.
    #[must_use]
    pub fn success(response: EffectResponse) -> Self {
        Self {
            status: EffectOutcomeStatus::Success,
            response: Some(response),
        }
    }

    /// Construct a blocked typed effect outcome.
    #[must_use]
    pub fn blocked() -> Self {
        Self {
            status: EffectOutcomeStatus::Blocked,
            response: None,
        }
    }

    /// Construct a failed typed effect outcome.
    #[must_use]
    pub fn failure(failure: EffectFailure) -> Self {
        Self {
            status: EffectOutcomeStatus::Failure { failure },
            response: None,
        }
    }

    fn success_response(self) -> Result<EffectResponse, EffectFailure> {
        match self.status {
            EffectOutcomeStatus::Success => self.response.ok_or_else(|| {
                EffectFailure::contract_violation("successful effect outcome is missing response")
            }),
            EffectOutcomeStatus::Blocked => Err(EffectFailure::contract_violation(
                "effect outcome blocked where success was required",
            )),
            EffectOutcomeStatus::Failure { failure } => Err(failure),
        }
    }

    /// Convert this outcome into a typed `EffectResult<SendDecision>`.
    ///
    /// # Errors
    ///
    /// Returns [`EffectFailure`] when the outcome is a success with the wrong
    /// response kind or a malformed successful payload.
    pub fn into_send_decision(self) -> Result<EffectResult<SendDecision>, EffectFailure> {
        match self.status {
            EffectOutcomeStatus::Blocked => Ok(EffectResult::Blocked),
            EffectOutcomeStatus::Failure { failure } => Ok(EffectResult::Failure(failure)),
            EffectOutcomeStatus::Success => match self.success_response()? {
                EffectResponse::SendDecision { decision } => Ok(EffectResult::Success(decision)),
                other => Err(EffectFailure::contract_violation(format!(
                    "effect outcome kind mismatch: expected send_decision, got {:?}",
                    other
                ))),
            },
        }
    }

    /// Convert this outcome into a typed `EffectResult<()>` for receive/release.
    ///
    /// # Errors
    ///
    /// Returns [`EffectFailure`] when the outcome is a success with the wrong
    /// response kind or a malformed successful payload.
    pub fn into_unit(self, expected_kind: &str) -> Result<EffectResult<()>, EffectFailure> {
        match self.status {
            EffectOutcomeStatus::Blocked => Ok(EffectResult::Blocked),
            EffectOutcomeStatus::Failure { failure } => Ok(EffectResult::Failure(failure)),
            EffectOutcomeStatus::Success => match self.success_response()? {
                EffectResponse::Receive { .. } | EffectResponse::Release => {
                    Ok(EffectResult::Success(()))
                }
                EffectResponse::InvokeStep { .. } if expected_kind == "invoke_step" => {
                    Ok(EffectResult::Success(()))
                }
                other => Err(EffectFailure::contract_violation(format!(
                    "effect outcome kind mismatch: expected {expected_kind}, got {:?}",
                    other
                ))),
            },
        }
    }

    /// Convert this outcome into a typed `EffectResult<String>`.
    ///
    /// # Errors
    ///
    /// Returns [`EffectFailure`] when the outcome is a success with the wrong
    /// response kind or a malformed successful payload.
    pub fn into_label(self) -> Result<EffectResult<String>, EffectFailure> {
        match self.status {
            EffectOutcomeStatus::Blocked => Ok(EffectResult::Blocked),
            EffectOutcomeStatus::Failure { failure } => Ok(EffectResult::Failure(failure)),
            EffectOutcomeStatus::Success => match self.success_response()? {
                EffectResponse::Choose { label } => Ok(EffectResult::Success(label)),
                other => Err(EffectFailure::contract_violation(format!(
                    "effect outcome kind mismatch: expected choose label, got {:?}",
                    other
                ))),
            },
        }
    }

    /// Convert this outcome into a typed `EffectResult<Value>`.
    ///
    /// # Errors
    ///
    /// Returns [`EffectFailure`] when the outcome is a success with the wrong
    /// response kind or a malformed successful payload.
    pub fn into_value(self, expected_kind: &str) -> Result<EffectResult<Value>, EffectFailure> {
        match self.status {
            EffectOutcomeStatus::Blocked => Ok(EffectResult::Blocked),
            EffectOutcomeStatus::Failure { failure } => Ok(EffectResult::Failure(failure)),
            EffectOutcomeStatus::Success => match self.success_response()? {
                EffectResponse::Acquire { evidence } if expected_kind == "acquire" => {
                    Ok(EffectResult::Success(evidence))
                }
                other => Err(EffectFailure::contract_violation(format!(
                    "effect outcome kind mismatch: expected {expected_kind}, got {:?}",
                    other
                ))),
            },
        }
    }

    /// Convert this outcome into a typed `EffectResult<Vec<TopologyPerturbation>>`.
    ///
    /// # Errors
    ///
    /// Returns [`EffectFailure`] when the outcome is a success with the wrong
    /// response kind or a malformed successful payload.
    pub fn into_topology(self) -> Result<EffectResult<Vec<TopologyPerturbation>>, EffectFailure> {
        match self.status {
            EffectOutcomeStatus::Blocked => Ok(EffectResult::Blocked),
            EffectOutcomeStatus::Failure { failure } => Ok(EffectResult::Failure(failure)),
            EffectOutcomeStatus::Success => match self.success_response()? {
                EffectResponse::TopologyEvents { events } => Ok(EffectResult::Success(events)),
                other => Err(EffectFailure::contract_violation(format!(
                    "effect outcome kind mismatch: expected topology events, got {:?}",
                    other
                ))),
            },
        }
    }

    /// Convert this outcome into an output-condition hint.
    ///
    /// # Errors
    ///
    /// Returns [`EffectFailure`] when the outcome blocks, fails, or carries the
    /// wrong response kind.
    pub fn into_output_condition_hint(self) -> Result<Option<OutputConditionHint>, EffectFailure> {
        match self.status {
            EffectOutcomeStatus::Blocked => Err(EffectFailure::contract_violation(
                "output_condition_hint may not block",
            )),
            EffectOutcomeStatus::Failure { failure } => Err(failure),
            EffectOutcomeStatus::Success => match self.success_response()? {
                EffectResponse::OutputConditionHint { hint } => Ok(hint),
                other => Err(EffectFailure::contract_violation(format!(
                    "effect outcome kind mismatch: expected output_condition_hint, got {:?}",
                    other
                ))),
            },
        }
    }
}

/// Replay/export record for one effect request/outcome exchange.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct EffectExchangeRecord {
    /// Monotonic effect id.
    pub effect_id: u64,
    /// Stable handler identity.
    pub handler_identity: String,
    /// Deterministic ordering key.
    pub ordering_key: u64,
    /// Typed request record.
    pub request: EffectRequest,
    /// Typed outcome record.
    pub outcome: EffectOutcome,
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


/// Typed failure kinds at the ProtocolMachine effect boundary.
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

/// Typed outcome for one ProtocolMachine effect callback.
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

#[cfg(test)]
mod effect_contract_tests {
    use super::*;

    #[test]
    fn effect_metadata_rejects_observational_blocking_contracts() {
        let metadata = EffectInterfaceMetadata {
            interface_name: "Runtime".to_string(),
            operation_name: "watch".to_string(),
            authority_class: EffectAuthorityClass::Observe,
            admissibility: EffectAdmissibility::DeclaredUseOnly,
            totality: EffectTotality::MayBlock,
            timeout_policy: EffectTimeoutPolicy::None,
            reentrancy_policy: EffectReentrancyPolicy::Allow,
            handler_domain: EffectHandlerDomain::External,
        };

        let err = metadata
            .validate()
            .expect_err("observational effects must not block");
        assert!(err.message.contains("observational effect"));
    }

    #[test]
    fn effect_metadata_rejects_internal_only_external_handlers() {
        let metadata = EffectInterfaceMetadata {
            interface_name: "Runtime".to_string(),
            operation_name: "topologyEvents".to_string(),
            authority_class: EffectAuthorityClass::Authoritative,
            admissibility: EffectAdmissibility::InternalOnly,
            totality: EffectTotality::Immediate,
            timeout_policy: EffectTimeoutPolicy::None,
            reentrancy_policy: EffectReentrancyPolicy::Allow,
            handler_domain: EffectHandlerDomain::External,
        };

        let err = metadata
            .validate()
            .expect_err("internal-only effects must not be external");
        assert!(err.message.contains("internal-only"));
    }
}
