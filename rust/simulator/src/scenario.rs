//! TOML scenario format for simulation runs.
//!
//! A scenario specifies the roles, material layer, parameters, step count,
//! and output configuration for a simulation.

use serde::{Deserialize, Serialize};
use std::path::Path;
use std::time::Duration;

use crate::fault::{Fault, FaultSchedule, ScheduledFault, Trigger};
use crate::material::MaterialParams;
use crate::network::{NetworkConfig, Partition};
use crate::property::{parse_predicate, Property, PropertyMonitor};

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
    pub latency_variance: f64,
    /// Loss probability per message.
    #[serde(default)]
    pub loss_probability: f64,
    /// Optional static partitions.
    #[serde(default)]
    pub partitions: Vec<PartitionSpec>,
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
    pub random: Option<f64>,
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
        probability: f64,
    },
    /// Delay messages by N ticks.
    MessageDelay {
        /// Number of ticks to delay message delivery.
        ticks: u64,
    },
    /// Corrupt message payload with given probability.
    MessageCorruption {
        /// Probability of corrupting each message (0.0 to 1.0).
        probability: f64,
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
        toml::from_str(s).map_err(|e| format!("parse TOML: {e}"))
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
            let fault = event.action.to_fault();
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
                bound: liv.bound as usize,
            });
        }
        Ok(Some(PropertyMonitor::new(props)))
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
            triggers.push(Trigger::Random(p));
        }
        if let Some(on) = &self.on_event {
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
    fn to_fault(&self) -> Fault {
        match self {
            FaultActionSpec::MessageDrop { probability } => Fault::MessageDrop {
                probability: *probability,
            },
            FaultActionSpec::MessageDelay { ticks } => Fault::MessageDelay {
                ticks: *ticks as usize,
            },
            FaultActionSpec::MessageCorruption { probability } => Fault::MessageCorruption {
                probability: *probability,
            },
            FaultActionSpec::NodeCrash { role, duration } => Fault::NodeCrash {
                role: role.clone(),
                duration: duration.map(|d| d as usize),
            },
            FaultActionSpec::NetworkPartition { groups, duration } => Fault::NetworkPartition {
                groups: groups.clone(),
                duration: *duration as usize,
            },
        }
    }
}

fn parse_invariant(name: &str) -> Result<Property, String> {
    match name {
        "no_faults" => Ok(Property::NoFaults),
        "simplex" => Ok(Property::Simplex),
        _ => {
            if let Some((base, args)) = parse_call(name) {
                match base {
                    "send_recv_liveness" => {
                        if args.len() != 2 {
                            return Err("send_recv_liveness requires (sid,bound)".into());
                        }
                        let sid = args[0]
                            .parse::<usize>()
                            .map_err(|_| "invalid session id".to_string())?;
                        let bound = args[1]
                            .parse::<usize>()
                            .map_err(|_| "invalid bound".to_string())?;
                        return Ok(Property::SendRecvLiveness { sid, bound });
                    }
                    "buffer_bound" => {
                        if args.len() != 2 {
                            return Err("buffer_bound requires (sid,max)".into());
                        }
                        let sid = args[0]
                            .parse::<usize>()
                            .map_err(|_| "invalid session id".to_string())?;
                        let max = args[1]
                            .parse::<usize>()
                            .map_err(|_| "invalid max".to_string())?;
                        return Ok(Property::BufferBound { sid, max });
                    }
                    "type_monotonicity" => {
                        if args.len() != 1 {
                            return Err("type_monotonicity requires (sid)".into());
                        }
                        let sid = args[0]
                            .parse::<usize>()
                            .map_err(|_| "invalid session id".to_string())?;
                        return Ok(Property::TypeMonotonicity { sid });
                    }
                    _ => {}
                }
            }
            Err(format!("unknown invariant: {name}"))
        }
    }
}

fn parse_call(expr: &str) -> Option<(&str, Vec<&str>)> {
    let expr = expr.trim();
    let expr = expr.strip_suffix(')')?;
    let (name, args) = expr.split_once('(')?;
    let args = args
        .split(',')
        .map(|s| s.trim())
        .filter(|s| !s.is_empty())
        .collect::<Vec<_>>();
    Some((name.trim(), args))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_mean_field_scenario() {
        let toml = r#"
            name = "mean_field_ising"
            roles = ["A", "B"]
            steps = 1000
            seed = 42

            [material]
            layer = "mean_field"

            [material.params]
            beta = 1.5
            species = ["up", "down"]
            initial_state = [0.6, 0.4]
            step_size = 0.01

            [output]
            format = "jsonl"
        "#;

        let scenario = Scenario::parse(toml).expect("parse scenario");
        assert_eq!(scenario.name, "mean_field_ising");
        assert_eq!(scenario.roles, vec!["A", "B"]);
        assert_eq!(scenario.steps, 1000);
        assert_eq!(scenario.seed, 42);
        match &scenario.material {
            MaterialParams::MeanField(mf) => {
                assert!((mf.beta - 1.5).abs() < f64::EPSILON);
            }
            _ => panic!("expected MeanField"),
        }
    }

    #[test]
    fn test_default_seed_when_missing() {
        let toml = r#"
            name = "default_seed"
            roles = ["A", "B"]
            steps = 1

            [material]
            layer = "mean_field"

            [material.params]
            beta = 1.0
            species = ["up", "down"]
            initial_state = [0.5, 0.5]
            step_size = 0.01
        "#;

        let scenario = Scenario::parse(toml).expect("parse scenario");
        assert_eq!(scenario.seed, 0);
    }
}
