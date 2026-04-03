//! First-class simulator reconfiguration operations and canonical traces.

use serde::{Deserialize, Serialize};
use std::collections::BTreeSet;
use std::sync::Mutex;
use std::time::Duration;
use telltale_machine::model::effects::EffectHandler;
use telltale_machine::ObsEvent;
use telltale_types::FixedQ32;

use crate::fault::Trigger;
use crate::network::{LinkPolicy, NetworkModel};
use crate::rng::SimRng;

fn default_true() -> bool {
    true
}

/// Directed link named in a reconfiguration footprint.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReconfigurationLink {
    /// Source role.
    pub from: String,
    /// Destination role.
    pub to: String,
}

/// Canonical footprint for one simulator reconfiguration operation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Default)]
pub struct ReconfigurationFootprint {
    /// Roles directly affected by this operation.
    pub roles: Vec<String>,
    /// Directed links directly affected by this operation.
    pub links: Vec<ReconfigurationLink>,
}

/// Whether a reconfiguration is semantics-only or consumes transition budget.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, Default)]
#[serde(rename_all = "snake_case")]
pub enum ReconfigurationEffectKind {
    /// Pure reconfiguration with no separate transition-choreography budget.
    #[default]
    Pure,
    /// Reconfiguration whose cutover consumes explicit transition budget.
    TransitionChoreography,
}

/// Cost classification for one reconfiguration operation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReconfigurationEffect {
    /// Reconfiguration budget class.
    #[serde(default)]
    pub kind: ReconfigurationEffectKind,
    /// Transition-choreography budget cost.
    #[serde(default)]
    pub budget_cost: u64,
}

impl Default for ReconfigurationEffect {
    fn default() -> Self {
        Self {
            kind: ReconfigurationEffectKind::Pure,
            budget_cost: 0,
        }
    }
}

/// First-class simulator reconfiguration action.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum ReconfigurationAction {
    /// Update one directed link policy.
    Link {
        /// Source role.
        from: String,
        /// Destination role.
        to: String,
        /// Whether the link remains enabled after the update.
        #[serde(default = "default_true")]
        enabled: bool,
        /// Optional latency override in milliseconds.
        #[serde(default)]
        base_latency_ms: Option<u64>,
        /// Optional latency variance override.
        #[serde(default)]
        latency_variance: Option<FixedQ32>,
        /// Optional loss probability override.
        #[serde(default)]
        loss_probability: Option<FixedQ32>,
    },
    /// Record an explicit delegation operation between two roles.
    Delegation {
        /// Stable delegation scope or operation name.
        scope: String,
        /// Revoked/delegating role.
        from_role: String,
        /// Activated/delegate role.
        to_role: String,
    },
    /// Record an explicit handoff operation between two roles.
    Handoff {
        /// Stable handoff identifier.
        handoff_id: String,
        /// Revoked role.
        from_role: String,
        /// Activated role.
        to_role: String,
    },
    /// Update one federation partitioning policy.
    Federation {
        /// Stable federation identifier.
        federation: String,
        /// Whether the named federation becomes active.
        #[serde(default = "default_true")]
        enabled: bool,
        /// Communication groups when the federation is active.
        #[serde(default)]
        groups: Vec<Vec<String>>,
    },
    /// Record a role-local or multi-role mode transition.
    ModeTransition {
        /// Roles that participate in the transition.
        roles: Vec<String>,
        /// Previous mode name.
        from_mode: String,
        /// Target mode name.
        to_mode: String,
    },
}

impl ReconfigurationAction {
    /// Stable action kind name.
    #[must_use]
    pub fn kind_name(&self) -> &'static str {
        match self {
            Self::Link { .. } => "link",
            Self::Delegation { .. } => "delegation",
            Self::Handoff { .. } => "handoff",
            Self::Federation { .. } => "federation",
            Self::ModeTransition { .. } => "mode_transition",
        }
    }

    /// Return the canonical footprint for this action.
    #[must_use]
    pub fn footprint(&self) -> ReconfigurationFootprint {
        match self {
            Self::Link { from, to, .. } => ReconfigurationFootprint {
                roles: vec![from.clone(), to.clone()],
                links: vec![ReconfigurationLink {
                    from: from.clone(),
                    to: to.clone(),
                }],
            },
            Self::Delegation {
                from_role, to_role, ..
            }
            | Self::Handoff {
                from_role, to_role, ..
            } => ReconfigurationFootprint {
                roles: vec![from_role.clone(), to_role.clone()],
                links: Vec::new(),
            },
            Self::Federation { groups, .. } => {
                let mut roles = groups
                    .iter()
                    .flat_map(|group| group.iter().cloned())
                    .collect::<BTreeSet<_>>()
                    .into_iter()
                    .collect::<Vec<_>>();
                roles.sort();
                ReconfigurationFootprint {
                    roles,
                    links: Vec::new(),
                }
            }
            Self::ModeTransition { roles, .. } => {
                let mut roles = roles
                    .iter()
                    .cloned()
                    .collect::<BTreeSet<_>>()
                    .into_iter()
                    .collect::<Vec<_>>();
                roles.sort();
                ReconfigurationFootprint {
                    roles,
                    links: Vec::new(),
                }
            }
        }
    }

    /// Whether this action mutates the network model directly.
    #[must_use]
    pub fn affects_network(&self) -> bool {
        matches!(self, Self::Link { .. } | Self::Federation { .. })
    }

    fn apply_to_network<H: EffectHandler>(&self, network: &NetworkModel<H>) -> Result<(), String> {
        match self {
            Self::Link {
                from,
                to,
                enabled,
                base_latency_ms,
                latency_variance,
                loss_probability,
            } => network.set_link_policy(LinkPolicy {
                from: from.clone(),
                to: to.clone(),
                enabled: *enabled,
                base_latency: base_latency_ms.map(Duration::from_millis),
                latency_variance: *latency_variance,
                loss_probability: *loss_probability,
            }),
            Self::Federation {
                federation,
                enabled,
                groups,
            } => {
                if *enabled {
                    network.set_federation_groups(federation.clone(), groups.clone())
                } else {
                    network.clear_federation(federation)
                }
            }
            Self::Delegation { .. } | Self::Handoff { .. } | Self::ModeTransition { .. } => Ok(()),
        }
    }
}

/// One scheduled simulator reconfiguration operation.
#[derive(Debug, Clone)]
pub struct ScheduledReconfiguration {
    /// Stable operation identifier.
    pub operation_id: String,
    /// When the operation activates.
    pub trigger: Trigger,
    /// Operation payload.
    pub action: ReconfigurationAction,
    /// Budget classification.
    pub effect: ReconfigurationEffect,
}

/// Canonical trace entry for one applied simulator reconfiguration.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReconfigurationRecord {
    /// Stable operation identifier.
    pub operation_id: String,
    /// Global tick where the operation became active.
    pub tick: u64,
    /// Logical round count where the operation became active.
    pub logical_step: u64,
    /// Canonical action payload.
    pub action: ReconfigurationAction,
    /// Budget classification.
    pub effect: ReconfigurationEffect,
    /// Canonical derived footprint.
    pub footprint: ReconfigurationFootprint,
}

/// Reconfiguration accounting summary for one simulator run.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Default)]
pub struct ReconfigurationSummary {
    /// Total applied reconfiguration operations.
    pub applied_operations: u64,
    /// Pure reconfiguration count.
    pub pure_operations: u64,
    /// Transition-choreography count.
    pub transition_operations: u64,
    /// Total transition budget consumed.
    pub transition_budget_consumed: u64,
}

#[derive(Debug, Clone)]
struct ScheduledReconfigurationState {
    operation_id: String,
    trigger: Trigger,
    action: ReconfigurationAction,
    effect: ReconfigurationEffect,
    activated: bool,
}

struct ReconfigurationState {
    scheduled: Vec<ScheduledReconfigurationState>,
    applied: Vec<ReconfigurationRecord>,
    rng: SimRng,
    last_trace_len: usize,
}

/// Stateful reconfiguration controller shared by one simulator run.
pub struct ReconfigurationController {
    state: Mutex<ReconfigurationState>,
}

impl ReconfigurationController {
    /// Create a controller from one scheduled program.
    #[must_use]
    pub fn new(program: Vec<ScheduledReconfiguration>, rng: SimRng) -> Self {
        let scheduled = program
            .into_iter()
            .map(|operation| ScheduledReconfigurationState {
                operation_id: operation.operation_id,
                trigger: operation.trigger,
                action: operation.action,
                effect: operation.effect,
                activated: false,
            })
            .collect();
        Self {
            state: Mutex::new(ReconfigurationState {
                scheduled,
                applied: Vec::new(),
                rng,
                last_trace_len: 0,
            }),
        }
    }

    fn lock_state(&self) -> Result<std::sync::MutexGuard<'_, ReconfigurationState>, String> {
        self.state
            .lock()
            .map_err(|_| "reconfiguration state lock poisoned".to_string())
    }

    /// Whether any scheduled operation mutates the network model.
    pub fn requires_network_model(&self) -> Result<bool, String> {
        Ok(self
            .lock_state()?
            .scheduled
            .iter()
            .any(|operation| operation.action.affects_network()))
    }

    /// Advance reconfiguration scheduling and apply due operations.
    pub fn tick<H: EffectHandler>(
        &self,
        tick: u64,
        logical_step: u64,
        trace: &[ObsEvent],
        network: Option<&NetworkModel<H>>,
    ) -> Result<(), String> {
        let mut state = self.lock_state()?;
        let new_events = trace.get(state.last_trace_len..).unwrap_or(&[]);

        let ReconfigurationState {
            scheduled,
            applied,
            rng,
            ..
        } = &mut *state;

        for operation in scheduled.iter_mut() {
            if operation.activated {
                continue;
            }
            if !trigger_fires(&operation.trigger, tick, logical_step, new_events, rng) {
                continue;
            }
            if operation.action.affects_network() {
                let network = network.ok_or_else(|| {
                    format!(
                        "reconfiguration `{}` requires a network model",
                        operation.operation_id
                    )
                })?;
                operation.action.apply_to_network(network)?;
            }
            applied.push(ReconfigurationRecord {
                operation_id: operation.operation_id.clone(),
                tick,
                logical_step,
                footprint: operation.action.footprint(),
                action: operation.action.clone(),
                effect: operation.effect.clone(),
            });
            operation.activated = true;
        }

        state.last_trace_len = trace.len();
        Ok(())
    }

    /// Canonical applied reconfiguration trace.
    pub fn trace(&self) -> Result<Vec<ReconfigurationRecord>, String> {
        Ok(self.lock_state()?.applied.clone())
    }

    /// Reconfiguration accounting summary.
    pub fn summary(&self) -> Result<ReconfigurationSummary, String> {
        let applied = &self.lock_state()?.applied;
        let mut summary = ReconfigurationSummary {
            applied_operations: u64::try_from(applied.len()).unwrap_or(u64::MAX),
            ..ReconfigurationSummary::default()
        };
        for record in applied {
            match record.effect.kind {
                ReconfigurationEffectKind::Pure => {
                    summary.pure_operations = summary.pure_operations.saturating_add(1);
                }
                ReconfigurationEffectKind::TransitionChoreography => {
                    summary.transition_operations = summary.transition_operations.saturating_add(1);
                    summary.transition_budget_consumed = summary
                        .transition_budget_consumed
                        .saturating_add(record.effect.budget_cost);
                }
            }
        }
        Ok(summary)
    }
}

fn trigger_fires(
    trigger: &Trigger,
    tick: u64,
    logical_step: u64,
    events: &[ObsEvent],
    rng: &mut SimRng,
) -> bool {
    match trigger {
        Trigger::Immediate => true,
        Trigger::AtTick(value) => tick >= *value,
        Trigger::AfterStep(value) => logical_step >= *value,
        Trigger::Random(probability) => rng.should_trigger(*probability),
        Trigger::OnEvent { kind, role } => {
            let kind = kind.to_lowercase();
            events
                .iter()
                .any(|event| event_matches(event, &kind, role.as_deref()))
        }
    }
}

fn event_matches(event: &ObsEvent, kind: &str, role: Option<&str>) -> bool {
    match event {
        ObsEvent::Sent { from, to, .. } => {
            if kind != "sent" {
                return false;
            }
            role.map_or(true, |expected| expected == from || expected == to)
        }
        ObsEvent::Received { from, to, .. } => {
            if kind != "received" {
                return false;
            }
            role.map_or(true, |expected| expected == from || expected == to)
        }
        ObsEvent::Opened { .. } => kind == "opened" && role.is_none(),
        ObsEvent::Closed { .. } => kind == "closed" && role.is_none(),
        ObsEvent::Invoked { role: observed, .. } => {
            if kind != "invoked" {
                return false;
            }
            role.map_or(true, |expected| expected == observed)
        }
        ObsEvent::Halted { .. } => kind == "halted" && role.is_none(),
        ObsEvent::Faulted { .. } => kind == "faulted" && role.is_none(),
        _ => false,
    }
}
