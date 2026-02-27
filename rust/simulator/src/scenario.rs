//! TOML scenario format for simulation runs.
//!
//! A scenario specifies the roles, material layer, parameters, step count,
//! and output configuration for a simulation.

use serde::{Deserialize, Serialize};
use std::path::Path;
use std::time::Duration;
use telltale_types::FixedQ32;

use crate::fault::{Fault, FaultSchedule, ScheduledFault, Trigger};
use crate::material::MaterialParams;
use crate::network::{LinkPolicy, NetworkConfig, Partition};
use crate::property::{parse_predicate, Property, PropertyMonitor};
use invariants::parse_invariant;

mod invariants;
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
    /// Scheduler concurrency level.
    #[serde(default = "default_concurrency")]
    pub concurrency: u64,
    /// Deterministic seed for simulation middleware.
    #[serde(default = "default_seed")]
    pub seed: u64,
    /// Optional network configuration.
    #[serde(default)]
    pub network: Option<NetworkSpec>,
    /// Material parameters.
    pub material: MaterialParams,
    /// Fault injection events.
    #[serde(default)]
    pub events: Vec<EventSpec>,
    /// Property monitoring configuration.
    #[serde(default)]
    pub properties: Option<PropertiesSpec>,
    /// Checkpoint interval (ticks). None = disabled.
    #[serde(default)]
    pub checkpoint_interval: Option<u64>,
    /// Output configuration.
    #[serde(default)]
    pub output: OutputConfig,
}

/// Output configuration for trace writing.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OutputConfig {
    /// Output file path (defaults to stdout if not set).
    pub file: Option<String>,
    /// Output format.
    #[serde(default)]
    pub format: OutputFormat,
}

impl Default for OutputConfig {
    fn default() -> Self {
        Self {
            file: None,
            format: OutputFormat::Json,
        }
    }
}

/// Trace output format.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum OutputFormat {
    /// JSON array of step records.
    #[default]
    Json,
    /// JSON lines (one record per line).
    Jsonl,
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
    /// Optional static partitions.
    #[serde(default)]
    pub partitions: Vec<PartitionSpec>,
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
            partitions: self
                .partitions
                .iter()
                .map(|p| Partition {
                    groups: p.groups.clone(),
                    start_tick: p.start_tick,
                    end_tick: p.end_tick,
                })
                .collect(),
            links: self
                .links
                .iter()
                .map(|link| LinkPolicy {
                    from: link.from.clone(),
                    to: link.to.clone(),
                    start_tick: link.start_tick,
                    end_tick: link.end_tick,
                    enabled: link.enabled,
                    base_latency: link.base_latency_ms.map(Duration::from_millis),
                    latency_variance: link.latency_variance,
                    loss_probability: link.loss_probability,
                })
                .collect(),
        }
    }
}

/// Partition specification for network configs.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PartitionSpec {
    /// Groups of roles that can communicate within but not across.
    pub groups: Vec<Vec<String>>,
    /// Tick when the partition becomes active.
    pub start_tick: u64,
    /// Tick when the partition heals.
    pub end_tick: u64,
}

/// Role-to-role link policy specification.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LinkSpec {
    /// Source role.
    pub from: String,
    /// Destination role.
    pub to: String,
    /// Tick when this link policy becomes active.
    #[serde(default)]
    pub start_tick: Option<u64>,
    /// Tick when this link policy becomes inactive.
    #[serde(default)]
    pub end_tick: Option<u64>,
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

/// Fault injection event specification.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EventSpec {
    /// When to activate the fault.
    pub trigger: TriggerSpec,
    /// What fault to inject.
    pub action: FaultActionSpec,
}

/// Trigger specification for events.
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
    /// Activate when a specific event occurs.
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

/// Fault action specification.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum FaultActionSpec {
    /// Drop messages with given probability.
    MessageDrop {
        /// Probability of dropping each message (0.0 to 1.0).
        probability: FixedQ32,
    },
    /// Delay messages by N ticks.
    MessageDelay {
        /// Number of ticks to delay message delivery.
        ticks: u64,
    },
    /// Corrupt message payload with given probability.
    MessageCorruption {
        /// Probability of corrupting each message (0.0 to 1.0).
        probability: FixedQ32,
    },
    /// Crash a role (stop executing its coroutines).
    NodeCrash {
        /// The role to crash.
        role: String,
        /// Duration in ticks before recovery. None means permanent.
        duration: Option<u64>,
    },
    /// Partition roles into disconnected groups.
    NetworkPartition {
        /// Groups of roles that can communicate within but not across.
        groups: Vec<Vec<String>>,
        /// Duration in ticks before partition heals.
        duration: u64,
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

fn default_concurrency() -> u64 {
    1
}

fn default_link_enabled() -> bool {
    true
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

    /// Convert event specs to a fault schedule.
    pub fn fault_schedule(&self) -> Result<FaultSchedule, String> {
        let mut faults = Vec::new();
        for event in &self.events {
            let trigger = event.trigger.to_trigger()?;
            let fault = event.action.to_fault()?;
            faults.push(ScheduledFault {
                fault,
                trigger,
                duration: None,
            });
        }
        Ok(FaultSchedule {
            faults,
            max_concurrent: usize::MAX,
        })
    }

    /// Build a property monitor from scenario properties.
    pub fn property_monitor(&self) -> Result<Option<PropertyMonitor>, String> {
        let Some(spec) = &self.properties else {
            return Ok(None);
        };
        let mut props = Vec::new();
        for inv in &spec.invariants {
            props.push(parse_invariant(inv)?);
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

impl FaultActionSpec {
    fn to_fault(&self) -> Result<Fault, String> {
        match self {
            FaultActionSpec::MessageDrop { probability } => {
                validate_probability("event.message_drop.probability", *probability)?;
                Ok(Fault::MessageDrop {
                    probability: *probability,
                })
            }
            FaultActionSpec::MessageDelay { ticks } => Ok(Fault::MessageDelay {
                ticks: checked_u64_to_usize("event.message_delay.ticks", *ticks)?,
            }),
            FaultActionSpec::MessageCorruption { probability } => {
                validate_probability("event.message_corruption.probability", *probability)?;
                Ok(Fault::MessageCorruption {
                    probability: *probability,
                })
            }
            FaultActionSpec::NodeCrash { role, duration } => Ok(Fault::NodeCrash {
                role: role.clone(),
                duration: match duration {
                    Some(value) => Some(checked_u64_to_usize("event.node_crash.duration", *value)?),
                    None => None,
                },
            }),
            FaultActionSpec::NetworkPartition { groups, duration } => Ok(Fault::NetworkPartition {
                groups: groups.clone(),
                duration: checked_u64_to_usize("event.network_partition.duration", *duration)?,
            }),
        }
    }
}

#[cfg(test)]
mod tests;
