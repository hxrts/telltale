//! TOML scenario format for simulation runs.
//!
//! A scenario specifies the roles, field/material layer, parameters, step count,
//! and middleware configuration for a simulation.

use serde::{Deserialize, Serialize};
use std::path::Path;
use std::time::Duration;
use telltale_types::FixedQ32;

use crate::fault::{
    AdversaryAction, AdversaryBudget, AdversaryBudgetMode, AdversaryProgram,
    AssumptionFailureClass, ScheduledAdversary, Trigger,
};
use crate::material::MaterialParams;
use crate::network::{LinkPolicy, NetworkConfig};
use crate::property::{parse_predicate, parse_property, Property, PropertyMonitor};
use crate::reconfiguration::{
    ReconfigurationAction, ReconfigurationEffect, ScheduledReconfiguration,
};
mod validation;

/// A simulation scenario loaded from TOML.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Scenario {
    /// Scenario metadata.
    pub name: String,
    /// Role names participating in the protocol.
    pub roles: Vec<String>,
    /// Number of simulation steps.
    pub steps: u64,
    /// Execution backend and concurrency policy.
    #[serde(default)]
    pub execution: ExecutionSpec,
    /// Deterministic seed for simulation middleware.
    #[serde(default = "default_seed")]
    pub seed: u64,
    /// Optional network configuration.
    #[serde(default)]
    pub network: Option<NetworkSpec>,
    /// Optional built-in material parameters for material-driven adapters.
    #[serde(default)]
    pub material: Option<MaterialParams>,
    /// First-class simulator reconfiguration operations.
    #[serde(default)]
    pub reconfigurations: Vec<ReconfigurationSpec>,
    /// Budgeted adversary declarations.
    #[serde(default)]
    pub adversaries: Vec<AdversarySpec>,
    /// Property monitoring configuration.
    #[serde(default)]
    pub properties: Option<PropertiesSpec>,
    /// Checkpoint interval (ticks). None = disabled.
    #[serde(default)]
    pub checkpoint_interval: Option<u64>,
    /// Optional theorem/profile declaration for theorem-indexed reporting.
    #[serde(default)]
    pub theorem: TheoremProfileSpec,
}

/// Execution configuration for one simulator run.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct ExecutionSpec {
    /// Execution backend selection.
    #[serde(default)]
    pub backend: ExecutionBackend,
    /// Scheduler policy selection.
    #[serde(default)]
    pub scheduler_policy: SchedulerPolicySpec,
    /// Scheduler lane width for one protocol-machine round.
    ///
    /// `None` lets the simulator choose the authoritative default for this backend.
    #[serde(default)]
    pub scheduler_concurrency: Option<u64>,
    /// Number of worker threads for the threaded backend.
    ///
    /// `None` lets the simulator choose the default for this backend.
    #[serde(default)]
    pub worker_threads: Option<u64>,
}

/// Requested simulator execution backend.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, Default, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum ExecutionBackend {
    /// Choose the simulator's authoritative default execution lane.
    #[default]
    Auto,
    /// Use the canonical single-thread protocol machine.
    Canonical,
    /// Use the threaded protocol machine.
    Threaded,
}

/// Resolved simulator backend after applying defaults and environment policy.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum ResolvedExecutionBackend {
    /// Canonical single-thread protocol machine.
    Canonical,
    /// Threaded protocol machine.
    Threaded,
}

/// Requested scheduler policy for one simulator run.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, Default, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum SchedulerPolicySpec {
    /// Choose the simulator's default scheduler policy.
    #[default]
    Auto,
    /// Cooperative scheduler semantics.
    Cooperative,
    /// Round-robin scheduler semantics.
    RoundRobin,
    /// Aging priority scheduler semantics.
    PriorityAging,
    /// Token-weighted priority scheduler semantics.
    PriorityTokenWeighted,
    /// Progress-aware scheduler semantics.
    ProgressAware,
}

/// Resolved scheduler policy after applying simulator defaults.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum ResolvedSchedulerPolicy {
    /// Cooperative single-lane scheduler policy.
    Cooperative,
    /// Basic round-robin scheduler policy.
    RoundRobin,
    /// Aging priority scheduler policy.
    PriorityAging,
    /// Token-weighted priority scheduler policy.
    PriorityTokenWeighted,
    /// Progress-aware scheduler policy.
    ProgressAware,
}

/// Fully resolved execution settings used by one simulator run.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct ResolvedExecution {
    /// Resolved backend.
    pub backend: ResolvedExecutionBackend,
    /// Resolved scheduler policy.
    pub scheduler_policy: ResolvedSchedulerPolicy,
    /// Scheduler lane width.
    pub scheduler_concurrency: u64,
    /// Worker-thread count.
    pub worker_threads: u64,
}

/// Declared theorem/profile configuration for one simulator run.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Default)]
pub struct TheoremProfileSpec {
    /// Scheduler-facing theorem profile.
    #[serde(default)]
    pub scheduler_profile: TheoremSchedulerProfile,
    /// Envelope-facing theorem profile.
    #[serde(default)]
    pub envelope_profile: TheoremEnvelopeProfile,
    /// Transport/fault assumption bundle.
    #[serde(default)]
    pub assumption_bundle: TheoremAssumptionBundle,
}

/// Proof-side execution regime classification for one resolved simulator run.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum ExecutionRegime {
    /// Canonical single-thread execution; authoritative exact replay/debug lane.
    CanonicalExact,
    /// Threaded execution at scheduler concurrency `1`; exact with respect to the canonical lane.
    ThreadedExact,
    /// Threaded execution at scheduler concurrency `> 1`; authoritative only modulo the declared envelope contract.
    ThreadedEnvelopeBounded,
}

/// Declared scheduler theorem profile.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq, Default)]
#[serde(rename_all = "snake_case")]
pub enum TheoremSchedulerProfile {
    /// Derive a scheduler profile from the resolved execution regime.
    #[default]
    Auto,
    /// Require canonical exact execution.
    CanonicalExact,
    /// Require threaded execution that remains exact at scheduler concurrency `1`.
    ThreadedExact,
    /// Classify the run under the threaded envelope regime.
    ThreadedEnvelope,
}

/// Declared envelope theorem profile.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq, Default)]
#[serde(rename_all = "snake_case")]
pub enum TheoremEnvelopeProfile {
    /// Derive an envelope profile from the resolved execution regime.
    #[default]
    Auto,
    /// Claim exact theorem-facing behavior.
    Exact,
    /// Claim protocol-machine envelope adherence.
    ProtocolMachineEnvelopeAdherence,
    /// Claim protocol-machine envelope admission.
    ProtocolMachineEnvelopeAdmission,
    /// Do not claim a theorem-facing envelope.
    None,
}

/// Declared transport/fault assumption bundle.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq, Default)]
#[serde(rename_all = "snake_case")]
pub enum TheoremAssumptionBundle {
    /// Derive an assumption bundle from the scenario middleware surface.
    #[default]
    Auto,
    /// No network middleware and no declared adversaries.
    FaultFreeTransport,
    /// Transport behavior is observed empirically rather than theorem-indexed.
    ObservedTransport,
    /// A partial-synchrony assumption bundle is declared.
    PartialSynchrony,
    /// A Byzantine/failure-envelope assumption bundle is declared.
    ByzantineEnvelope,
}

/// Eligibility classification for theorem-backed outputs.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum TheoremEligibility {
    /// Exact theorem-backed reporting is admissible for this run/profile pair.
    Exact,
    /// Only envelope-bounded theorem-backed reporting is admissible.
    EnvelopeBounded,
    /// The declared profile does not admit theorem-backed outputs for this run.
    Ineligible,
}

/// Resolved theorem/profile information for one run.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct ResolvedTheoremProfile {
    /// Resolved scheduler theorem profile.
    pub scheduler_profile: TheoremSchedulerProfile,
    /// Resolved envelope theorem profile.
    pub envelope_profile: TheoremEnvelopeProfile,
    /// Resolved transport/fault assumption bundle.
    pub assumption_bundle: TheoremAssumptionBundle,
    /// Eligibility of theorem-backed outputs under this profile.
    pub eligibility: TheoremEligibility,
    /// Optional explanation when theorem-backed output is ineligible.
    pub eligibility_reason: Option<String>,
}

#[derive(Debug, Clone, Copy)]
struct ExecutionEnvironment {
    available_parallelism: u64,
    threaded_available: bool,
}

/// Network configuration in TOML-friendly units.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NetworkSpec {
    /// Base latency in milliseconds.
    #[serde(default)]
    pub base_latency_ms: u64,
    /// Relative latency variance.
    #[serde(default)]
    pub latency_variance: FixedQ32,
    /// Loss probability per message.
    #[serde(default)]
    pub loss_probability: FixedQ32,
    /// Optional per-link role policies.
    #[serde(default)]
    pub links: Vec<LinkSpec>,
}

impl NetworkSpec {
    /// Converts the TOML-friendly spec to a runtime config.
    #[must_use]
    pub fn to_config(&self) -> NetworkConfig {
        NetworkConfig {
            base_latency: Duration::from_millis(self.base_latency_ms),
            latency_variance: self.latency_variance,
            loss_probability: self.loss_probability,
            links: self
                .links
                .iter()
                .map(|link| LinkPolicy {
                    from: link.from.clone(),
                    to: link.to.clone(),
                    enabled: link.enabled,
                    base_latency: link.base_latency_ms.map(Duration::from_millis),
                    latency_variance: link.latency_variance,
                    loss_probability: link.loss_probability,
                })
                .collect(),
        }
    }
}

/// Role-to-role link policy specification.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LinkSpec {
    /// Source role.
    pub from: String,
    /// Destination role.
    pub to: String,
    /// Whether this link is enabled while active.
    #[serde(default = "default_link_enabled")]
    pub enabled: bool,
    /// Optional base latency override in milliseconds.
    #[serde(default)]
    pub base_latency_ms: Option<u64>,
    /// Optional latency variance override.
    #[serde(default)]
    pub latency_variance: Option<FixedQ32>,
    /// Optional loss probability override.
    #[serde(default)]
    pub loss_probability: Option<FixedQ32>,
}

/// First-class simulator reconfiguration operation specification.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ReconfigurationSpec {
    /// When to activate the operation.
    pub trigger: TriggerSpec,
    /// What operation to apply.
    pub action: ReconfigurationAction,
    /// Whether the operation is pure or budget-consuming.
    #[serde(default)]
    pub effect: ReconfigurationEffect,
}

/// Budgeted adversary declaration.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AdversarySpec {
    /// Optional stable identifier for replay/artifact surfaces.
    #[serde(default)]
    pub id: Option<String>,
    /// When to activate the adversary.
    pub trigger: TriggerSpec,
    /// What adversarial behavior to activate.
    pub action: AdversaryActionSpec,
    /// Budget/accounting declaration for the adversary.
    pub budget: AdversaryBudgetSpec,
}

/// Trigger specification for adversaries and reconfigurations.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct TriggerSpec {
    /// Activate immediately when scheduled.
    #[serde(default)]
    pub immediate: bool,
    /// Activate at a specific simulation tick.
    #[serde(default)]
    pub at_tick: Option<u64>,
    /// Activate after a specific number of steps.
    #[serde(default)]
    pub after_step: Option<u64>,
    /// Activate randomly with the given probability each tick.
    #[serde(default)]
    pub random: Option<FixedQ32>,
    /// Activate when a specific observable event occurs.
    #[serde(default)]
    pub on_event: Option<OnEventSpec>,
}

/// Event trigger on a trace event.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OnEventSpec {
    /// Event kind to match (e.g., "sent", "received").
    pub kind: String,
    /// Optional role filter for the event.
    #[serde(default)]
    pub role: Option<String>,
}

/// Budget declaration for one adversary.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AdversaryBudgetSpec {
    /// Total budgeted disturbances or activations.
    pub total: u64,
    /// Assumption-bundle clause to diagnose if this budget is exhausted.
    #[serde(default)]
    pub assumption_failure: Option<AssumptionFailureClass>,
    /// Budget consumption model.
    #[serde(flatten)]
    pub mode: AdversaryBudgetModeSpec,
}

/// Budget consumption model for one adversary.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "mode", rename_all = "snake_case")]
pub enum AdversaryBudgetModeSpec {
    /// Deterministic one-shot activation budgeting.
    Activation,
    /// Independent per-message Bernoulli disturbance.
    Independent {
        /// Probability of disturbing one eligible message.
        probability: FixedQ32,
    },
    /// Per-window quota budgeting for correlated disturbance windows.
    Windowed {
        /// Window width in ticks.
        window_ticks: u64,
        /// Maximum disturbed messages in one window.
        max_per_window: u64,
    },
    /// Correlated burst budgeting started by Bernoulli activation.
    Correlated {
        /// Probability of starting a burst at one eligible message.
        probability: FixedQ32,
        /// Burst duration in ticks once activated.
        burst_ticks: u64,
    },
}

/// Adversary action specification.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum AdversaryActionSpec {
    /// Withhold/destroy selected messages.
    Withholding,
    /// Delay selected messages by N ticks.
    TimingDisturbance {
        /// Number of ticks to delay message delivery.
        ticks: u64,
    },
    /// Corrupt selected message payloads.
    Corruption,
    /// Crash a role (stop executing its coroutines).
    Crash {
        /// The role to crash.
        role: String,
        /// Duration in ticks before recovery. None means permanent.
        duration: Option<u64>,
    },
    /// Apply a byzantine-style interference profile to selected messages.
    ByzantineInterference {
        /// Probability of withholding a selected message.
        #[serde(default)]
        withholding_probability: FixedQ32,
        /// Probability of corrupting a selected message if not withheld.
        #[serde(default)]
        corruption_probability: FixedQ32,
        /// Optional delay if the selected message is neither withheld nor corrupted.
        #[serde(default)]
        delay_ticks: Option<u64>,
    },
}

/// Properties configuration.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct PropertiesSpec {
    /// Invariant property names to check.
    #[serde(default)]
    pub invariants: Vec<String>,
    /// Liveness property specifications.
    #[serde(default)]
    pub liveness: Vec<LivenessSpec>,
}

/// Liveness property specification.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LivenessSpec {
    /// Property name for reporting.
    pub name: String,
    /// Predicate expression that starts the liveness window.
    pub precondition: String,
    /// Predicate expression that must become true within bound.
    pub goal: String,
    /// Maximum steps to reach goal after precondition.
    pub bound: u64,
}

fn default_seed() -> u64 {
    0
}

fn default_link_enabled() -> bool {
    true
}

fn current_execution_environment() -> ExecutionEnvironment {
    let available_parallelism = std::thread::available_parallelism()
        .map(|n| u64::try_from(n.get()).unwrap_or(u64::MAX))
        .unwrap_or(1)
        .max(1);
    ExecutionEnvironment {
        available_parallelism,
        threaded_available: cfg!(feature = "multi-thread"),
    }
}

impl ExecutionSpec {
    fn resolve_for(&self, env: ExecutionEnvironment) -> Result<ResolvedExecution, String> {
        if matches!(self.scheduler_concurrency, Some(0)) {
            return Err("scenario.execution.scheduler_concurrency must be >= 1".to_string());
        }
        if matches!(self.worker_threads, Some(0)) {
            return Err("scenario.execution.worker_threads must be >= 1".to_string());
        }

        let backend = match self.backend {
            ExecutionBackend::Auto => {
                let _ = env;
                ResolvedExecutionBackend::Canonical
            }
            ExecutionBackend::Canonical => ResolvedExecutionBackend::Canonical,
            ExecutionBackend::Threaded => {
                if env.threaded_available {
                    ResolvedExecutionBackend::Threaded
                } else {
                    return Err(
                        "scenario.execution.backend = \"threaded\" requires simulator feature `multi-thread`"
                            .to_string(),
                    );
                }
            }
        };

        let scheduler_policy = match self.scheduler_policy {
            SchedulerPolicySpec::Auto | SchedulerPolicySpec::Cooperative => {
                ResolvedSchedulerPolicy::Cooperative
            }
            SchedulerPolicySpec::RoundRobin => ResolvedSchedulerPolicy::RoundRobin,
            SchedulerPolicySpec::PriorityAging => ResolvedSchedulerPolicy::PriorityAging,
            SchedulerPolicySpec::PriorityTokenWeighted => {
                ResolvedSchedulerPolicy::PriorityTokenWeighted
            }
            SchedulerPolicySpec::ProgressAware => ResolvedSchedulerPolicy::ProgressAware,
        };

        let parallel_default = env.available_parallelism.max(1);
        let scheduler_concurrency =
            self.scheduler_concurrency
                .unwrap_or_else(|| match self.backend {
                    ExecutionBackend::Auto => 1,
                    ExecutionBackend::Canonical => 1,
                    ExecutionBackend::Threaded => parallel_default,
                });
        let worker_threads = self.worker_threads.unwrap_or_else(|| match self.backend {
            ExecutionBackend::Auto => 1,
            ExecutionBackend::Canonical => 1,
            ExecutionBackend::Threaded => parallel_default,
        });

        if matches!(backend, ResolvedExecutionBackend::Canonical)
            && (scheduler_concurrency != 1 || worker_threads != 1)
        {
            return Err(
                "canonical simulator backend requires scheduler_concurrency = 1 and worker_threads = 1"
                    .to_string(),
            );
        }

        Ok(ResolvedExecution {
            backend,
            scheduler_policy,
            scheduler_concurrency,
            worker_threads,
        })
    }
}

impl ResolvedExecution {
    /// Classify this execution in the proof-side concurrency regime lattice.
    #[must_use]
    pub fn regime(&self) -> ExecutionRegime {
        match self.backend {
            ResolvedExecutionBackend::Canonical => ExecutionRegime::CanonicalExact,
            ResolvedExecutionBackend::Threaded if self.scheduler_concurrency <= 1 => {
                ExecutionRegime::ThreadedExact
            }
            ResolvedExecutionBackend::Threaded => ExecutionRegime::ThreadedEnvelopeBounded,
        }
    }
}

impl Scenario {
    /// Resolve theorem/profile information against one resolved execution.
    #[must_use]
    pub fn resolve_theorem_profile_for(
        &self,
        execution: &ResolvedExecution,
    ) -> ResolvedTheoremProfile {
        let execution_regime = execution.regime();
        let scheduler_profile = match self.theorem.scheduler_profile {
            TheoremSchedulerProfile::Auto => match execution_regime {
                ExecutionRegime::CanonicalExact => TheoremSchedulerProfile::CanonicalExact,
                ExecutionRegime::ThreadedExact => TheoremSchedulerProfile::ThreadedExact,
                ExecutionRegime::ThreadedEnvelopeBounded => {
                    TheoremSchedulerProfile::ThreadedEnvelope
                }
            },
            profile => profile,
        };
        let envelope_profile = match self.theorem.envelope_profile {
            TheoremEnvelopeProfile::Auto => match execution_regime {
                ExecutionRegime::CanonicalExact | ExecutionRegime::ThreadedExact => {
                    TheoremEnvelopeProfile::Exact
                }
                ExecutionRegime::ThreadedEnvelopeBounded => {
                    TheoremEnvelopeProfile::ProtocolMachineEnvelopeAdherence
                }
            },
            profile => profile,
        };
        let assumption_bundle = match self.theorem.assumption_bundle {
            TheoremAssumptionBundle::Auto
                if self.network.is_none()
                    && self.adversaries.is_empty()
                    && self.reconfigurations.is_empty() =>
            {
                TheoremAssumptionBundle::FaultFreeTransport
            }
            TheoremAssumptionBundle::Auto => TheoremAssumptionBundle::ObservedTransport,
            bundle => bundle,
        };

        let scheduler_error = match (scheduler_profile, execution_regime) {
            (TheoremSchedulerProfile::CanonicalExact, ExecutionRegime::CanonicalExact)
            | (TheoremSchedulerProfile::ThreadedExact, ExecutionRegime::ThreadedExact)
            | (
                TheoremSchedulerProfile::ThreadedEnvelope,
                ExecutionRegime::ThreadedEnvelopeBounded,
            ) => None,
            (TheoremSchedulerProfile::CanonicalExact, actual) => Some(format!(
                "scheduler profile canonical_exact requires canonical_exact execution, got {}",
                actual.as_str()
            )),
            (TheoremSchedulerProfile::ThreadedExact, actual) => Some(format!(
                "scheduler profile threaded_exact requires threaded_exact execution, got {}",
                actual.as_str()
            )),
            (TheoremSchedulerProfile::ThreadedEnvelope, actual) => Some(format!(
                "scheduler profile threaded_envelope requires threaded_envelope_bounded execution, got {}",
                actual.as_str()
            )),
            (TheoremSchedulerProfile::Auto, _) => None,
        };

        let envelope_error = match (envelope_profile, execution_regime) {
            (
                TheoremEnvelopeProfile::Exact,
                ExecutionRegime::CanonicalExact | ExecutionRegime::ThreadedExact,
            )
            | (
                TheoremEnvelopeProfile::ProtocolMachineEnvelopeAdherence
                | TheoremEnvelopeProfile::ProtocolMachineEnvelopeAdmission,
                _,
            )
            | (TheoremEnvelopeProfile::None, _)
            | (TheoremEnvelopeProfile::Auto, _) => None,
            (TheoremEnvelopeProfile::Exact, actual) => Some(format!(
                "envelope profile exact requires an exact execution regime, got {}",
                actual.as_str()
            )),
        };

        let assumption_error = match assumption_bundle {
            TheoremAssumptionBundle::FaultFreeTransport
                if self.network.is_some()
                    || !self.adversaries.is_empty()
                    || !self.reconfigurations.is_empty() =>
            {
                Some(
                    "assumption bundle fault_free_transport requires no network middleware, no declared adversaries, and no simulator reconfiguration program"
                        .to_string(),
                )
            }
            _ => None,
        };

        let eligibility_reason = scheduler_error
            .or(envelope_error)
            .or(assumption_error)
            .or_else(|| {
                if matches!(envelope_profile, TheoremEnvelopeProfile::None) {
                    Some(
                        "envelope profile none disables theorem-backed outputs for this run"
                            .to_string(),
                    )
                } else {
                    None
                }
            });

        let eligibility = if eligibility_reason.is_some() {
            TheoremEligibility::Ineligible
        } else {
            match envelope_profile {
                TheoremEnvelopeProfile::Exact => TheoremEligibility::Exact,
                TheoremEnvelopeProfile::ProtocolMachineEnvelopeAdherence
                | TheoremEnvelopeProfile::ProtocolMachineEnvelopeAdmission => {
                    TheoremEligibility::EnvelopeBounded
                }
                TheoremEnvelopeProfile::None | TheoremEnvelopeProfile::Auto => {
                    TheoremEligibility::Ineligible
                }
            }
        };

        ResolvedTheoremProfile {
            scheduler_profile,
            envelope_profile,
            assumption_bundle,
            eligibility,
            eligibility_reason,
        }
    }

    /// Resolve theorem/profile information against the scenario's resolved execution.
    ///
    /// # Errors
    ///
    /// Returns an error if execution resolution fails.
    pub fn resolved_theorem_profile(&self) -> Result<ResolvedTheoremProfile, String> {
        let execution = self.resolved_execution()?;
        Ok(self.resolve_theorem_profile_for(&execution))
    }
}

impl ExecutionRegime {
    /// Stable string form for diagnostics.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::CanonicalExact => "canonical_exact",
            Self::ThreadedExact => "threaded_exact",
            Self::ThreadedEnvelopeBounded => "threaded_envelope_bounded",
        }
    }
}

fn checked_u64_to_usize(name: &str, value: u64) -> Result<usize, String> {
    usize::try_from(value).map_err(|_| format!("{name} value {value} exceeds platform usize"))
}

fn validate_probability(name: &str, probability: FixedQ32) -> Result<(), String> {
    let zero = FixedQ32::zero();
    let one = FixedQ32::one();
    if !probability.is_finite() {
        return Err(format!("{name} must be finite"));
    }
    if probability < zero || probability > one {
        return Err(format!("{name} must be in [0,1], got {probability}"));
    }
    Ok(())
}

fn validate_non_negative(name: &str, value: FixedQ32) -> Result<(), String> {
    if !value.is_finite() {
        return Err(format!("{name} must be finite"));
    }
    if value < FixedQ32::zero() {
        return Err(format!("{name} must be non-negative, got {value}"));
    }
    Ok(())
}

impl Scenario {
    /// Load a scenario from a TOML file.
    ///
    /// # Errors
    ///
    /// Returns an error if the file cannot be read or parsed.
    pub fn from_file(path: &Path) -> Result<Self, String> {
        let content =
            std::fs::read_to_string(path).map_err(|e| format!("read {}: {e}", path.display()))?;
        Self::parse(&content)
    }

    /// Parse a scenario from a TOML string.
    ///
    /// # Errors
    ///
    /// Returns an error if parsing fails.
    pub fn parse(s: &str) -> Result<Self, String> {
        let scenario: Self = toml::from_str(s).map_err(|e| format!("parse TOML: {e}"))?;
        scenario.validate_semantics()?;
        Ok(scenario)
    }

    /// Convert optional network spec to runtime config.
    #[must_use]
    pub fn network_config(&self) -> Option<NetworkConfig> {
        self.network.as_ref().map(NetworkSpec::to_config)
    }

    /// Whether this scenario requires the network model layer.
    #[must_use]
    pub fn requires_network_model(&self) -> bool {
        self.network.is_some()
            || self
                .reconfigurations
                .iter()
                .any(|operation| operation.action.affects_network())
    }

    /// Resolve execution settings after applying simulator defaults and capability checks.
    ///
    /// # Errors
    ///
    /// Returns an error if the requested backend/settings are invalid.
    pub fn resolved_execution(&self) -> Result<ResolvedExecution, String> {
        self.execution.resolve_for(current_execution_environment())
    }

    /// Convert adversary specs to a resolved adversary program.
    pub fn adversary_program(&self) -> Result<AdversaryProgram, String> {
        let mut adversaries = Vec::new();
        for (idx, adversary) in self.adversaries.iter().enumerate() {
            let trigger = adversary.trigger.to_trigger()?;
            let action = adversary.action.to_action()?;
            let budget = adversary.budget.to_budget(&action)?;
            adversaries.push(ScheduledAdversary {
                adversary_id: adversary
                    .id
                    .clone()
                    .unwrap_or_else(|| format!("adversary:{idx}")),
                action,
                trigger,
                budget,
            });
        }
        Ok(AdversaryProgram { adversaries })
    }

    /// Convert reconfiguration specs to one scheduled reconfiguration program.
    pub fn reconfiguration_schedule(&self) -> Result<Vec<ScheduledReconfiguration>, String> {
        self.reconfigurations
            .iter()
            .enumerate()
            .map(|(idx, operation)| {
                Ok(ScheduledReconfiguration {
                    operation_id: format!("reconfiguration:{idx}"),
                    trigger: operation.trigger.to_trigger()?,
                    action: operation.action.clone(),
                    effect: operation.effect.clone(),
                })
            })
            .collect()
    }

    /// Build a property monitor from scenario properties.
    pub fn property_monitor(&self) -> Result<Option<PropertyMonitor>, String> {
        let Some(spec) = &self.properties else {
            return Ok(None);
        };
        let mut props = Vec::new();
        for inv in &spec.invariants {
            props.push(parse_property(inv)?);
        }
        for liv in &spec.liveness {
            let pre = parse_predicate(&liv.precondition)?;
            let goal = parse_predicate(&liv.goal)?;
            props.push(Property::Liveness {
                name: liv.name.clone(),
                precondition: pre,
                goal,
                bound: checked_u64_to_usize("liveness bound", liv.bound)?,
            });
        }
        Ok(Some(PropertyMonitor::new(props)))
    }

    /// Validate scenario semantics that are not enforced by TOML shape parsing.
    ///
    /// # Errors
    ///
    /// Returns an error if semantic validation fails.
    pub fn validate_semantics(&self) -> Result<(), String> {
        validation::validate_semantics(self)
    }
}

impl TriggerSpec {
    fn to_trigger(&self) -> Result<Trigger, String> {
        let mut triggers = Vec::new();
        if self.immediate {
            triggers.push(Trigger::Immediate);
        }
        if let Some(t) = self.at_tick {
            triggers.push(Trigger::AtTick(t));
        }
        if let Some(t) = self.after_step {
            triggers.push(Trigger::AfterStep(t));
        }
        if let Some(p) = self.random {
            validate_probability("trigger.random", p)?;
            triggers.push(Trigger::Random(p));
        }
        if let Some(on) = &self.on_event {
            let kind = on.kind.trim().to_lowercase();
            match kind.as_str() {
                "sent" | "received" | "opened" | "closed" | "invoked" | "halted" | "faulted" => {}
                _ => return Err(format!("unsupported on_event kind: {}", on.kind)),
            }
            triggers.push(Trigger::OnEvent {
                kind: on.kind.clone(),
                role: on.role.clone(),
            });
        }
        if triggers.is_empty() {
            return Ok(Trigger::Immediate);
        }
        if triggers.len() > 1 {
            return Err("trigger must specify exactly one condition".into());
        }
        Ok(triggers.remove(0))
    }
}

impl AdversaryBudgetSpec {
    fn to_budget(&self, action: &AdversaryAction) -> Result<AdversaryBudget, String> {
        let assumption_failure = self
            .assumption_failure
            .unwrap_or_else(|| action.default_assumption_failure());
        Ok(AdversaryBudget {
            total: self.total,
            assumption_failure,
            mode: match self.mode {
                AdversaryBudgetModeSpec::Activation => AdversaryBudgetMode::Activation,
                AdversaryBudgetModeSpec::Independent { probability } => {
                    validate_probability("adversary.budget.probability", probability)?;
                    AdversaryBudgetMode::Independent { probability }
                }
                AdversaryBudgetModeSpec::Windowed {
                    window_ticks,
                    max_per_window,
                } => AdversaryBudgetMode::Windowed {
                    window_ticks,
                    max_per_window,
                },
                AdversaryBudgetModeSpec::Correlated {
                    probability,
                    burst_ticks,
                } => {
                    validate_probability("adversary.budget.probability", probability)?;
                    AdversaryBudgetMode::Correlated {
                        probability,
                        burst_ticks,
                    }
                }
            },
        })
    }
}

impl AdversaryActionSpec {
    fn to_action(&self) -> Result<AdversaryAction, String> {
        match self {
            AdversaryActionSpec::Withholding => Ok(AdversaryAction::Withholding),
            AdversaryActionSpec::TimingDisturbance { ticks } => {
                Ok(AdversaryAction::TimingDisturbance {
                    ticks: checked_u64_to_usize("adversary.timing_disturbance.ticks", *ticks)?,
                })
            }
            AdversaryActionSpec::Corruption => Ok(AdversaryAction::Corruption),
            AdversaryActionSpec::Crash { role, duration } => Ok(AdversaryAction::Crash {
                role: role.clone(),
                duration: match duration {
                    Some(value) => Some(checked_u64_to_usize("adversary.crash.duration", *value)?),
                    None => None,
                },
            }),
            AdversaryActionSpec::ByzantineInterference {
                withholding_probability,
                corruption_probability,
                delay_ticks,
            } => {
                validate_probability(
                    "adversary.byzantine_interference.withholding_probability",
                    *withholding_probability,
                )?;
                validate_probability(
                    "adversary.byzantine_interference.corruption_probability",
                    *corruption_probability,
                )?;
                Ok(AdversaryAction::ByzantineInterference {
                    withholding_probability: *withholding_probability,
                    corruption_probability: *corruption_probability,
                    delay_ticks: delay_ticks
                        .map(|value| {
                            checked_u64_to_usize(
                                "adversary.byzantine_interference.delay_ticks",
                                value,
                            )
                        })
                        .transpose()?,
                })
            }
        }
    }
}

#[cfg(test)]
mod tests;
