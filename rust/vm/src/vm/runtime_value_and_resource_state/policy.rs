/// Information-flow policy used by epistemic `check`.
pub enum FlowPolicy {
    /// Permit all facts to all roles.
    AllowAll,
    /// Deny all flows.
    DenyAll,
    /// Permit only listed roles.
    AllowRoles(BTreeSet<String>),
    /// Deny listed roles.
    DenyRoles(BTreeSet<String>),
    /// Runtime closure policy:
    /// `Predicate(Box<dyn Fn(&Knowledge, &Role) -> bool>)`.
    Predicate(Box<dyn FlowPolicyFn>),
    /// Serializable knowledge-dependent predicate policy.
    PredicateExpr(FlowPredicate),
}

/// Cloneable dynamic predicate for runtime flow checks.
pub trait FlowPolicyFn: Send + Sync {
    /// Evaluate whether a fact may flow to a target role.
    fn eval(&self, knowledge: &KnowledgeFact, target_role: &str) -> bool;
    /// Clone trait-object predicate.
    fn clone_box(&self) -> Box<dyn FlowPolicyFn>;
}

impl<F> FlowPolicyFn for F
where
    F: Fn(&KnowledgeFact, &str) -> bool + Clone + Send + Sync + 'static,
{
    fn eval(&self, knowledge: &KnowledgeFact, target_role: &str) -> bool {
        self(knowledge, target_role)
    }

    fn clone_box(&self) -> Box<dyn FlowPolicyFn> {
        Box::new(self.clone())
    }
}

impl Clone for Box<dyn FlowPolicyFn> {
    fn clone(&self) -> Self {
        self.clone_box()
    }
}

#[allow(clippy::derivable_impls)]
impl Default for FlowPolicy {
    fn default() -> Self {
        Self::AllowAll
    }
}

impl Clone for FlowPolicy {
    fn clone(&self) -> Self {
        match self {
            Self::AllowAll => Self::AllowAll,
            Self::DenyAll => Self::DenyAll,
            Self::AllowRoles(roles) => Self::AllowRoles(roles.clone()),
            Self::DenyRoles(roles) => Self::DenyRoles(roles.clone()),
            Self::Predicate(predicate) => Self::Predicate(predicate.clone()),
            Self::PredicateExpr(predicate) => Self::PredicateExpr(predicate.clone()),
        }
    }
}

impl fmt::Debug for FlowPolicy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::AllowAll => f.write_str("AllowAll"),
            Self::DenyAll => f.write_str("DenyAll"),
            Self::AllowRoles(roles) => f.debug_tuple("AllowRoles").field(roles).finish(),
            Self::DenyRoles(roles) => f.debug_tuple("DenyRoles").field(roles).finish(),
            Self::Predicate(_) => f.write_str("Predicate(<dynamic>)"),
            Self::PredicateExpr(predicate) => {
                f.debug_tuple("PredicateExpr").field(predicate).finish()
            }
        }
    }
}

impl PartialEq for FlowPolicy {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::AllowAll, Self::AllowAll) => true,
            (Self::DenyAll, Self::DenyAll) => true,
            (Self::AllowRoles(lhs), Self::AllowRoles(rhs)) => lhs == rhs,
            (Self::DenyRoles(lhs), Self::DenyRoles(rhs)) => lhs == rhs,
            (Self::Predicate(lhs), Self::Predicate(rhs)) => {
                // Dynamic closure policies cannot be value-compared.
                // Equality is identity-based: true only when both variants
                // point to the exact same trait object instance.
                std::ptr::eq::<dyn FlowPolicyFn>(&**lhs, &**rhs)
            }
            (Self::PredicateExpr(lhs), Self::PredicateExpr(rhs)) => lhs == rhs,
            _ => false,
        }
    }
}

impl Eq for FlowPolicy {}

#[derive(Serialize, Deserialize)]
enum FlowPolicyRepr {
    AllowAll,
    DenyAll,
    AllowRoles(BTreeSet<String>),
    DenyRoles(BTreeSet<String>),
    PredicateExpr(FlowPredicate),
}

impl Serialize for FlowPolicy {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let repr = match self {
            Self::AllowAll => FlowPolicyRepr::AllowAll,
            Self::DenyAll => FlowPolicyRepr::DenyAll,
            Self::AllowRoles(roles) => FlowPolicyRepr::AllowRoles(roles.clone()),
            Self::DenyRoles(roles) => FlowPolicyRepr::DenyRoles(roles.clone()),
            Self::PredicateExpr(predicate) => FlowPolicyRepr::PredicateExpr(predicate.clone()),
            Self::Predicate(_) => {
                return Err(serde::ser::Error::custom(
                    "runtime closure predicate is not serializable",
                ))
            }
        };
        repr.serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for FlowPolicy {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let repr = FlowPolicyRepr::deserialize(deserializer)?;
        let policy = match repr {
            FlowPolicyRepr::AllowAll => Self::AllowAll,
            FlowPolicyRepr::DenyAll => Self::DenyAll,
            FlowPolicyRepr::AllowRoles(roles) => Self::AllowRoles(roles),
            FlowPolicyRepr::DenyRoles(roles) => Self::DenyRoles(roles),
            FlowPolicyRepr::PredicateExpr(predicate) => Self::PredicateExpr(predicate),
        };
        Ok(policy)
    }
}

impl FlowPolicy {
    /// Build a runtime closure-based flow predicate policy.
    #[must_use]
    pub fn predicate<F>(predicate: F) -> Self
    where
        F: Fn(&KnowledgeFact, &str) -> bool + Clone + Send + Sync + 'static,
    {
        Self::Predicate(Box::new(predicate))
    }
}

/// Serializable flow-policy predicate over known fact + destination.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum FlowPredicate {
    /// Allow when destination role starts with prefix.
    TargetRolePrefix(String),
    /// Allow when fact contains substring.
    FactContains(String),
    /// Allow when the fact endpoint role equals destination role.
    EndpointRoleMatchesTarget,
    /// Conjunction.
    All(Vec<FlowPredicate>),
    /// Disjunction.
    Any(Vec<FlowPredicate>),
}

impl FlowPolicy {
    /// Check whether knowledge flow to `target_role` is permitted.
    #[must_use]
    pub fn allows(&self, target_role: &str) -> bool {
        match self {
            Self::AllowAll => true,
            Self::DenyAll => false,
            Self::AllowRoles(roles) => roles.contains(target_role),
            Self::DenyRoles(roles) => !roles.contains(target_role),
            Self::Predicate(_) | Self::PredicateExpr(_) => true,
        }
    }

    /// Check whether a concrete knowledge fact may flow to a target role.
    #[must_use]
    pub fn allows_knowledge(&self, knowledge: &KnowledgeFact, target_role: &str) -> bool {
        match self {
            Self::Predicate(predicate) => predicate.eval(knowledge, target_role),
            Self::PredicateExpr(predicate) => predicate.eval(knowledge, target_role),
            other => other.allows(target_role),
        }
    }
}

impl FlowPredicate {
    /// Evaluate this serialized predicate against one fact and target role.
    #[must_use]
    pub fn eval(&self, knowledge: &KnowledgeFact, target_role: &str) -> bool {
        match self {
            Self::TargetRolePrefix(prefix) => target_role.starts_with(prefix),
            Self::FactContains(fragment) => knowledge.fact.contains(fragment),
            Self::EndpointRoleMatchesTarget => knowledge.endpoint.role == target_role,
            Self::All(predicates) => predicates
                .iter()
                .all(|predicate| predicate.eval(knowledge, target_role)),
            Self::Any(predicates) => predicates
                .iter()
                .any(|predicate| predicate.eval(knowledge, target_role)),
        }
    }
}

/// Typed runtime tuning profile for benchmark/runtime configuration harmonization.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq, Default)]
#[serde(rename_all = "snake_case")]
pub enum RuntimeTuningProfile {
    /// Default production-like tuning.
    #[default]
    Standard,
    /// Reference profile approximating early M1 stress behavior.
    M1StressReference,
}

/// Threaded scheduler round semantics mode.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq, Default)]
#[serde(rename_all = "snake_case")]
pub enum ThreadedRoundSemantics {
    /// Canonical one-step semantics aligned with Lean runner rounds.
    #[default]
    CanonicalOneStep,
    /// Performance extension: multi-pick waves within one round.
    WaveParallelExtension,
}

/// Effect-trace capture mode for runtime overhead control.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq, Default)]
#[serde(rename_all = "snake_case")]
pub enum EffectTraceCaptureMode {
    /// Record all canonical effect kinds.
    #[default]
    Full,
    /// Record only topology ingress events.
    TopologyOnly,
    /// Disable effect-trace recording.
    Disabled,
}

/// Retention policy for stored observability artifacts.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq, Default)]
#[serde(rename_all = "snake_case")]
pub enum ObservabilityRetentionMode {
    /// Retain all recorded artifacts.
    #[default]
    Full,
    /// Retain only the most recent `capacity` artifacts per stream.
    Capped,
    /// Disable retention entirely while preserving runtime behavior.
    Disabled,
}

/// Retention configuration for observability artifacts.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
pub struct ObservabilityRetentionConfig {
    /// Retention policy for observability artifacts.
    #[serde(default)]
    pub mode: ObservabilityRetentionMode,
    /// Maximum retained items per stream when `mode = capped`.
    #[serde(default = "default_observability_retention_capacity")]
    pub capacity: usize,
}

const fn default_observability_retention_capacity() -> usize {
    4_096
}

impl Default for ObservabilityRetentionConfig {
    fn default() -> Self {
        Self {
            mode: ObservabilityRetentionMode::Full,
            capacity: default_observability_retention_capacity(),
        }
    }
}

/// Payload validation mode for runtime message hardening.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq, Default)]
#[serde(rename_all = "snake_case")]
pub enum PayloadValidationMode {
    /// Disable VM-side payload validation checks.
    Off,
    /// Validate payload size and annotated `ValType` compatibility.
    #[default]
    Structural,
    /// Structural checks plus strict annotation requirement for `Send` and `Receive`.
    StrictSchema,
}
