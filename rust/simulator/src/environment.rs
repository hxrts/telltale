//! Generic environment-model boundaries for simulator extensions.

use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use telltale_machine::model::state::SessionId;
use telltale_types::FixedQ32;

/// One generic node pose in an external environment model.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Default)]
pub struct NodePose {
    /// Spatial coordinates in a model-defined embedding.
    pub coordinates: Vec<FixedQ32>,
    /// Model-defined orientation components.
    pub orientation: Vec<FixedQ32>,
}

/// Generic per-node capability state for environment-driven limits.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Default)]
pub struct NodeCapabilityState {
    /// Remaining or maximum admission slots for persistent communication relationships.
    pub connection_slots: Option<u64>,
    /// Queue budget available to the environment layer.
    pub queue_budget: Option<u64>,
    /// Duty-cycle budget available to the node.
    pub duty_cycle_budget: Option<u64>,
    /// Memory ceiling or remaining memory budget.
    pub memory_ceiling: Option<u64>,
    /// Energy or battery budget.
    pub energy_budget: Option<u64>,
    /// Additional domain-neutral limit counters keyed by external model name.
    #[serde(default)]
    pub custom_limits: BTreeMap<String, u64>,
}

/// Potential communication edge exposed by a topology model.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct PotentialLink {
    /// Current simulator tick.
    pub tick: u64,
    /// Source role.
    pub from: String,
    /// Destination role.
    pub to: String,
    /// Whether the edge is currently reachable.
    pub reachable: bool,
    /// Optional environment-side explanation.
    pub reason: Option<String>,
}

/// One communication relationship evaluated by a link-admission model.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct LinkAdmissionDecision {
    /// Current simulator tick.
    pub tick: u64,
    /// Source role.
    pub from: String,
    /// Destination role.
    pub to: String,
    /// Whether the relationship is admissible.
    pub admitted: bool,
    /// Optional diagnosis when rejected.
    pub reason: Option<String>,
}

/// One protocol-visible transmission observed by the shared execution core.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct TransmissionIntent {
    /// Current simulator tick.
    pub tick: u64,
    /// Logical step index used by the shared execution loop.
    pub logical_step: u64,
    /// Session identifier for the transmission.
    pub session: SessionId,
    /// Source role.
    pub from: String,
    /// Destination role.
    pub to: String,
    /// Protocol label.
    pub label: String,
}

/// Delivery classification emitted by a medium model.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
#[allow(missing_docs)]
pub enum MediumOutcomeKind {
    DeliverNow,
    Delay { ticks: u64 },
    Corrupt,
    Collision,
    Contended,
    Drop,
}

/// Environment-side resolution for one observed transmission.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct MediumResolution {
    /// Transmission being classified.
    pub transmission: TransmissionIntent,
    /// Environment-side medium outcome.
    pub outcome: MediumOutcomeKind,
    /// Optional explanation or attenuation/collision note.
    pub reason: Option<String>,
}

/// Canonical round snapshot shared across environment extension points.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Default)]
pub struct EnvironmentSnapshot {
    /// Current simulator tick.
    pub tick: u64,
    /// Logical step index from the shared execution loop.
    pub logical_step: u64,
    /// Participating roles for the scenario.
    pub roles: Vec<String>,
    /// Active built-in field layer, when the scenario uses one.
    pub field_layer: Option<String>,
    /// Current node-local physical state exported from coroutine registers.
    #[serde(default)]
    pub field_state: BTreeMap<String, Vec<FixedQ32>>,
    /// Generic latent environment state owned by external models.
    #[serde(default)]
    pub latent_state: BTreeMap<String, Vec<FixedQ32>>,
    /// Current node positions/orientations.
    #[serde(default)]
    pub node_positions: BTreeMap<String, NodePose>,
    /// Current capability state by role.
    #[serde(default)]
    pub node_capabilities: BTreeMap<String, NodeCapabilityState>,
    /// Current potential communication edges.
    #[serde(default)]
    pub potential_links: Vec<PotentialLink>,
}

/// Canonical environment artifact emitted by simulator environment hooks.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(tag = "kind", rename_all = "snake_case")]
#[allow(missing_docs)]
pub enum EnvironmentArtifact {
    Mobility {
        tick: u64,
        role: String,
        pose: NodePose,
    },
    Capability {
        tick: u64,
        role: String,
        state: NodeCapabilityState,
    },
    Reachability {
        tick: u64,
        from: String,
        to: String,
        reachable: bool,
        reason: Option<String>,
    },
    Admission {
        tick: u64,
        from: String,
        to: String,
        admitted: bool,
        reason: Option<String>,
    },
    Medium {
        tick: u64,
        transmission: TransmissionIntent,
        outcome: MediumOutcomeKind,
        reason: Option<String>,
    },
}

/// Canonical environment trace emitted by the shared execution core.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Default)]
pub struct EnvironmentTrace {
    /// Ordered environment artifacts emitted during the run.
    pub records: Vec<EnvironmentArtifact>,
}

/// Topology model deciding potential communication reachability.
pub trait TopologyModel: Send + Sync {
    /// Resolve potential communication links for the current snapshot.
    fn potential_links(&self, snapshot: &EnvironmentSnapshot)
        -> Result<Vec<PotentialLink>, String>;
}

/// Medium model deciding delivery/collision/contention outcomes.
pub trait MediumModel: Send + Sync {
    /// Resolve environment-side outcomes for the transmissions observed this round.
    fn resolve_transmissions(
        &self,
        snapshot: &EnvironmentSnapshot,
        transmissions: &[TransmissionIntent],
    ) -> Result<Vec<MediumResolution>, String>;
}

/// Mobility model advancing node pose deterministically over simulator time.
pub trait MobilityModel: Send + Sync {
    /// Advance the node pose map for the current snapshot.
    fn advance(&self, snapshot: &EnvironmentSnapshot)
        -> Result<BTreeMap<String, NodePose>, String>;
}

/// Node capability model describing per-node limits.
pub trait NodeCapabilityModel: Send + Sync {
    /// Compute per-node capability state for the current snapshot.
    fn node_capabilities(
        &self,
        snapshot: &EnvironmentSnapshot,
    ) -> Result<BTreeMap<String, NodeCapabilityState>, String>;
}

/// Admission model deciding whether communication relationships are admissible.
pub trait LinkAdmissionModel: Send + Sync {
    /// Evaluate candidate links against topology and capability constraints.
    fn evaluate_links(
        &self,
        snapshot: &EnvironmentSnapshot,
        reachability: &[PotentialLink],
        capabilities: &BTreeMap<String, NodeCapabilityState>,
    ) -> Result<Vec<LinkAdmissionDecision>, String>;
}

/// Borrowed environment-model bundle provided by a host integration.
#[derive(Clone, Copy, Default)]
pub struct EnvironmentModels<'a> {
    /// Optional topology model.
    pub topology: Option<&'a dyn TopologyModel>,
    /// Optional medium model.
    pub medium: Option<&'a dyn MediumModel>,
    /// Optional mobility model.
    pub mobility: Option<&'a dyn MobilityModel>,
    /// Optional node capability model.
    pub node_capabilities: Option<&'a dyn NodeCapabilityModel>,
    /// Optional link-admission model.
    pub link_admission: Option<&'a dyn LinkAdmissionModel>,
}

impl EnvironmentModels<'_> {
    /// Whether no environment models were supplied.
    #[must_use]
    pub fn is_empty(self) -> bool {
        self.topology.is_none()
            && self.medium.is_none()
            && self.mobility.is_none()
            && self.node_capabilities.is_none()
            && self.link_admission.is_none()
    }
}

/// Round-driven environment controller used by the shared execution core.
pub struct EnvironmentController<'a> {
    models: EnvironmentModels<'a>,
    snapshot: EnvironmentSnapshot,
    trace: EnvironmentTrace,
}

impl<'a> EnvironmentController<'a> {
    /// Build one environment controller for the supplied model bundle.
    #[must_use]
    pub fn new(
        roles: &[String],
        field_layer: Option<String>,
        models: Option<EnvironmentModels<'a>>,
    ) -> Self {
        Self {
            models: models.unwrap_or_default(),
            snapshot: EnvironmentSnapshot {
                roles: roles.to_vec(),
                field_layer,
                ..EnvironmentSnapshot::default()
            },
            trace: EnvironmentTrace::default(),
        }
    }

    /// Whether the controller has any active environment models.
    #[must_use]
    pub fn is_active(&self) -> bool {
        !self.models.is_empty()
    }

    /// Refresh the shared snapshot at the start of a round and emit non-medium artifacts.
    pub fn begin_round(
        &mut self,
        tick: u64,
        logical_step: u64,
        field_state: BTreeMap<String, Vec<FixedQ32>>,
    ) -> Result<(), String> {
        self.snapshot.tick = tick;
        self.snapshot.logical_step = logical_step;
        self.snapshot.field_state = field_state;

        if let Some(model) = self.models.mobility {
            self.snapshot.node_positions = model.advance(&self.snapshot)?;
            for (role, pose) in &self.snapshot.node_positions {
                self.trace.records.push(EnvironmentArtifact::Mobility {
                    tick,
                    role: role.clone(),
                    pose: pose.clone(),
                });
            }
        }

        if let Some(model) = self.models.node_capabilities {
            self.snapshot.node_capabilities = model.node_capabilities(&self.snapshot)?;
            for (role, state) in &self.snapshot.node_capabilities {
                self.trace.records.push(EnvironmentArtifact::Capability {
                    tick,
                    role: role.clone(),
                    state: state.clone(),
                });
            }
        }

        if let Some(model) = self.models.topology {
            self.snapshot.potential_links = model.potential_links(&self.snapshot)?;
            for link in &self.snapshot.potential_links {
                self.trace.records.push(EnvironmentArtifact::Reachability {
                    tick,
                    from: link.from.clone(),
                    to: link.to.clone(),
                    reachable: link.reachable,
                    reason: link.reason.clone(),
                });
            }
        }

        if let Some(model) = self.models.link_admission {
            let decisions = model.evaluate_links(
                &self.snapshot,
                &self.snapshot.potential_links,
                &self.snapshot.node_capabilities,
            )?;
            for decision in decisions {
                self.trace.records.push(EnvironmentArtifact::Admission {
                    tick,
                    from: decision.from,
                    to: decision.to,
                    admitted: decision.admitted,
                    reason: decision.reason,
                });
            }
        }

        Ok(())
    }

    /// Resolve medium-side artifacts from transmissions observed in this round.
    pub fn finish_round(&mut self, transmissions: &[TransmissionIntent]) -> Result<(), String> {
        let Some(model) = self.models.medium else {
            return Ok(());
        };

        for resolution in model.resolve_transmissions(&self.snapshot, transmissions)? {
            self.trace.records.push(EnvironmentArtifact::Medium {
                tick: resolution.transmission.tick,
                transmission: resolution.transmission,
                outcome: resolution.outcome,
                reason: resolution.reason,
            });
        }
        Ok(())
    }

    /// Latest environment snapshot after the most recent round preparation.
    #[must_use]
    pub fn snapshot(&self) -> &EnvironmentSnapshot {
        &self.snapshot
    }

    /// Canonical environment trace emitted by the controller.
    #[must_use]
    pub fn trace(&self) -> &EnvironmentTrace {
        &self.trace
    }
}
