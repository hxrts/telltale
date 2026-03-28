//! Protocol composition API for running many protocols in one ProtocolMachine instance.
//!
//! This layer provides:
//! - proof-carrying admission (`LinkOKFull`-style certificate flag),
//! - shared immutable protocol artifacts (`Arc<CodeImage>`),
//! - memory-budget accounting for composed workloads.

use std::collections::BTreeSet;
use std::mem::size_of;
use std::sync::Arc;

use crate::determinism::DeterminismMode;
use crate::effect::EffectHandler;
use crate::engine::{ProtocolMachine, ProtocolMachineConfig, ProtocolMachineError};
use crate::loader::CodeImage;
use crate::output_condition::OutputConditionPolicy;
use crate::runtime_contracts::{
    enforce_protocol_machine_runtime_gates, execution_profile_supported,
    ProtocolMachineAdmissibilityClass, ProtocolMachineEscalationWindowClass,
    ProtocolMachineExecutionProfile, ProtocolMachineFairnessAssumption, RuntimeContracts,
    RuntimeGateResult,
};
use crate::scheduler::SchedPolicy;
use telltale_types::{
    canonical_transport_boundaries, canonicalize_placement_observations, PlacementObservation,
    TransportBoundaryObservation,
};

/// Determinism capability required to admit a protocol bundle.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DeterminismCapability {
    /// Supports full determinism for fixed initial state/policy/effect trace.
    Full,
    /// Supports determinism modulo effect traces.
    ModuloEffects,
    /// Supports determinism modulo admissible commutativity.
    ModuloCommutativity,
    /// Supports replay determinism profile.
    Replay,
}

/// Scheduler profile capability required to admit a protocol bundle.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SchedulerCapability {
    /// Cooperative scheduler profile.
    Cooperative,
    /// Round-robin scheduler profile.
    RoundRobin,
    /// Priority scheduler profile.
    Priority,
    /// Progress-aware scheduler profile.
    ProgressAware,
}

/// Theorem-pack capabilities surfaced by a proof artifact.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TheoremPackCapabilities {
    /// Determinism profiles certified by the proof artifact.
    pub determinism: Vec<DeterminismCapability>,
    /// Scheduler profiles certified by the proof artifact.
    pub schedulers: Vec<SchedulerCapability>,
    /// Whether output-condition commit-gating is certified.
    pub output_condition_gating: bool,
}

impl TheoremPackCapabilities {
    /// Capability set that allows all currently supported advanced runtime modes.
    #[must_use]
    pub fn full() -> Self {
        Self {
            determinism: vec![
                DeterminismCapability::Full,
                DeterminismCapability::ModuloEffects,
                DeterminismCapability::ModuloCommutativity,
                DeterminismCapability::Replay,
            ],
            schedulers: vec![
                SchedulerCapability::Cooperative,
                SchedulerCapability::RoundRobin,
                SchedulerCapability::Priority,
                SchedulerCapability::ProgressAware,
            ],
            output_condition_gating: true,
        }
    }

    /// Proof-carrying execution profile derived from theorem-pack capabilities.
    #[must_use]
    pub fn execution_profile(&self) -> ProtocolMachineExecutionProfile {
        let mut fairness_assumptions: std::collections::BTreeSet<_> =
            [ProtocolMachineFairnessAssumption::ScheduleConfluence]
                .into_iter()
                .collect();
        if self.schedulers.iter().any(|scheduler| {
            matches!(
                scheduler,
                SchedulerCapability::RoundRobin
                    | SchedulerCapability::Priority
                    | SchedulerCapability::ProgressAware
            )
        }) {
            fairness_assumptions.insert(ProtocolMachineFairnessAssumption::StarvationFreedom);
        }
        if self
            .schedulers
            .iter()
            .any(|scheduler| matches!(scheduler, SchedulerCapability::ProgressAware))
        {
            fairness_assumptions.insert(ProtocolMachineFairnessAssumption::LivenessFairness);
        }

        let mut admissibility_classes: std::collections::BTreeSet<_> = [
            ProtocolMachineAdmissibilityClass::LocalEnvelope,
            ProtocolMachineAdmissibilityClass::ShardedEnvelope,
        ]
        .into_iter()
        .collect();
        let mut escalation_window_classes: std::collections::BTreeSet<_> =
            [ProtocolMachineEscalationWindowClass::ProgressContract]
                .into_iter()
                .collect();
        if self.output_condition_gating {
            admissibility_classes.insert(ProtocolMachineAdmissibilityClass::ProtocolEnvelopeBridge);
            escalation_window_classes.insert(ProtocolMachineEscalationWindowClass::ProtocolBridge);
        }
        if self
            .determinism
            .iter()
            .any(|capability| !matches!(capability, DeterminismCapability::Full))
        {
            escalation_window_classes
                .insert(ProtocolMachineEscalationWindowClass::AdmissionComplexity);
        }

        ProtocolMachineExecutionProfile {
            fairness_assumptions,
            admissibility_classes,
            escalation_window_classes,
            theorem_pack_eligibility: vec![
                ("protocol_machine_envelope_adherence".to_string(), true),
                (
                    "protocol_machine_envelope_admission".to_string(),
                    self.determinism.iter().any(|capability| {
                        matches!(
                            capability,
                            DeterminismCapability::Full
                                | DeterminismCapability::Replay
                                | DeterminismCapability::ModuloEffects
                                | DeterminismCapability::ModuloCommutativity
                        )
                    }),
                ),
                (
                    "protocol_envelope_bridge".to_string(),
                    self.output_condition_gating,
                ),
            ],
        }
    }
}

/// Proof/certificate artifact required for composed protocol admission.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompositionCertificate {
    /// Stable identifier for the certificate/proof artifact.
    pub artifact_id: String,
    /// Whether this artifact witnesses `LinkOKFull`-style compatibility.
    pub link_ok_full: bool,
    /// Theorem-pack capabilities proven by this certificate.
    pub theorem_pack: TheoremPackCapabilities,
    /// Optional runtime contract bundle required for advanced runtime modes.
    pub runtime_contracts: Option<RuntimeContracts>,
}

/// Reconfiguration policy admitted for one protocol bundle.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct ReconfigurationPolicy {
    /// Whether the runtime may change the active member set over time.
    pub dynamic_membership: bool,
    /// Whether consecutive member sets must overlap.
    pub overlap_required: bool,
}

/// Deterministic audit artifact emitted for one accepted reconfiguration.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct ReconfigurationEvent {
    /// Stable bundle/certificate identifier.
    pub artifact_id: String,
    /// Monotonic epoch after the transition.
    pub epoch: u64,
    /// Canonical sorted member set before the transition.
    pub previous_members: Vec<String>,
    /// Canonical sorted member set after the transition.
    pub next_members: Vec<String>,
    /// Canonical sorted members added by the transition.
    pub added_members: Vec<String>,
    /// Canonical sorted members removed by the transition.
    pub removed_members: Vec<String>,
    /// Whether overlap was preserved on this transition.
    pub overlap_preserved: bool,
    /// Policy flag carried by the admitted bundle.
    pub dynamic_membership: bool,
    /// Policy flag carried by the admitted bundle.
    pub overlap_required: bool,
}

/// Deterministic placement-aware reconfiguration step.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct ReconfigurationPlanStep {
    /// Stable step identifier within the plan.
    pub step_id: String,
    /// Canonical sorted membership set after this step.
    pub next_members: Vec<String>,
    /// Canonical placement observations for the target membership set.
    pub placements: Vec<PlacementObservation>,
}

/// Deterministic multi-step reconfiguration plan.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct ReconfigurationPlan {
    /// Stable plan identifier.
    pub plan_id: String,
    /// Canonical ordered steps for the plan.
    pub steps: Vec<ReconfigurationPlanStep>,
}

/// Canonical semantic artifact for one executed reconfiguration phase.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct ReconfigurationPhaseArtifact {
    /// Stable step identifier.
    pub step_id: String,
    /// Accepted membership transition event.
    pub event: ReconfigurationEvent,
    /// Canonical placement observations for the active membership after the step.
    pub placements: Vec<PlacementObservation>,
    /// Canonical transport-observable boundaries implied by the placements.
    pub transport_boundaries: Vec<TransportBoundaryObservation>,
}

/// Canonical semantic artifact for one executed reconfiguration plan.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct ReconfigurationPlanExecution {
    /// Stable certificate artifact id.
    pub artifact_id: String,
    /// Stable plan identifier.
    pub plan_id: String,
    /// Canonical initial membership set.
    pub initial_members: Vec<String>,
    /// Executed phases in order.
    pub phases: Vec<ReconfigurationPhaseArtifact>,
    /// Canonical final membership set.
    pub final_members: Vec<String>,
}

/// Serializable snapshot of the reconfiguration state for one admitted bundle.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct ReconfigurationRuntimeSnapshot {
    /// Current epoch.
    pub epoch: u64,
    /// Canonical sorted active members.
    pub active_members: Vec<String>,
    /// Deterministic accepted transition history.
    pub history: Vec<ReconfigurationEvent>,
    /// Deterministic executed plan artifacts.
    pub plan_executions: Vec<ReconfigurationPlanExecution>,
}

#[derive(Debug, Clone, Default)]
struct ReconfigurationRuntimeState {
    epoch: u64,
    active_members: BTreeSet<String>,
    history: Vec<ReconfigurationEvent>,
    plan_executions: Vec<ReconfigurationPlanExecution>,
}

/// Immutable protocol bundle loaded by the composition API.
#[derive(Debug, Clone)]
pub struct ProtocolBundle {
    /// Shared immutable code image.
    pub code: Arc<CodeImage>,
    /// Certificate checked at admission time.
    pub certificate: CompositionCertificate,
    /// Optional runtime reconfiguration policy admitted for this bundle.
    pub reconfiguration_policy: Option<ReconfigurationPolicy>,
}

impl ProtocolBundle {
    /// Construct a bundle from a code image and certificate.
    #[must_use]
    pub fn new(code: Arc<CodeImage>, certificate: CompositionCertificate) -> Self {
        Self {
            code,
            certificate,
            reconfiguration_policy: None,
        }
    }

    /// Attach a deterministic reconfiguration policy to the bundle.
    #[must_use]
    pub fn with_reconfiguration_policy(mut self, policy: ReconfigurationPolicy) -> Self {
        self.reconfiguration_policy = Some(policy);
        self
    }

    /// The admitted reconfiguration policy for this bundle, if any.
    #[must_use]
    pub fn reconfiguration_policy(&self) -> Option<&ReconfigurationPolicy> {
        self.reconfiguration_policy.as_ref()
    }
}

/// Memory budget policy for composed execution.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MemoryBudget {
    /// Max bytes allowed per coroutine.
    pub max_bytes_per_coroutine: usize,
    /// Max bytes allowed per session.
    pub max_bytes_per_session: usize,
    /// Max incremental bytes allowed per additional protocol.
    pub max_incremental_bytes_per_protocol: usize,
}

impl Default for MemoryBudget {
    fn default() -> Self {
        Self {
            max_bytes_per_coroutine: 64 * 1024,
            max_bytes_per_session: 256 * 1024,
            max_incremental_bytes_per_protocol: 128 * 1024,
        }
    }
}

/// Composition memory usage snapshot.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct MemoryUsage {
    /// Estimated bytes per coroutine.
    pub bytes_per_coroutine: usize,
    /// Estimated bytes per session.
    pub bytes_per_session: usize,
    /// Estimated incremental overhead per protocol.
    pub incremental_bytes_per_protocol: usize,
    /// Number of loaded protocol bundles.
    pub protocol_count: usize,
    /// Number of live sessions.
    pub session_count: usize,
    /// Number of live coroutines.
    pub coroutine_count: usize,
}

/// Errors emitted by the composition API.
#[derive(Debug, thiserror::Error)]
pub enum CompositionError {
    /// Missing/invalid proof artifact.
    #[error("bundle `{artifact_id}` rejected: missing LinkOKFull compatibility evidence")]
    MissingCompatibilityProof {
        /// Certificate artifact id that failed admission.
        artifact_id: String,
    },
    /// The certificate does not expose required theorem/capability evidence.
    #[error("bundle `{artifact_id}` rejected: missing required capability `{capability}`")]
    MissingCapability {
        /// Certificate artifact id that failed admission.
        artifact_id: String,
        /// Human-readable capability key.
        capability: String,
    },
    /// Advanced runtime mode requires runtime contract evidence.
    #[error("bundle `{artifact_id}` rejected: missing ProtocolMachine runtime contracts for advanced mode")]
    MissingRuntimeContracts {
        /// Certificate artifact id that failed admission.
        artifact_id: String,
    },
    /// Bundle index does not exist.
    #[error("bundle index {bundle_idx} is out of range")]
    InvalidBundleIndex {
        /// The bundle index that was requested.
        bundle_idx: usize,
    },
    /// Reconfiguration was requested for a bundle that did not admit it.
    #[error("bundle `{artifact_id}` rejected reconfiguration request: bundle is not reconfiguration-enabled")]
    ReconfigurationDisabled {
        /// Certificate artifact id associated with the rejected bundle.
        artifact_id: String,
    },
    /// Reconfiguration requires a runtime capability that was not supplied.
    #[error("bundle `{artifact_id}` rejected reconfiguration request: missing required capability `{capability}`")]
    MissingReconfigurationCapability {
        /// Certificate artifact id associated with the rejected bundle.
        artifact_id: String,
        /// Human-readable capability key.
        capability: String,
    },
    /// Reconfiguration attempted to produce an empty membership set.
    #[error(
        "bundle `{artifact_id}` rejected reconfiguration request: membership set may not be empty"
    )]
    EmptyMembership {
        /// Certificate artifact id associated with the rejected bundle.
        artifact_id: String,
    },
    /// Reconfiguration violated the admitted overlap policy.
    #[error("bundle `{artifact_id}` rejected reconfiguration request: overlap_required but member sets are disjoint")]
    OverlapRequiredViolation {
        /// Certificate artifact id associated with the rejected bundle.
        artifact_id: String,
    },
    /// Reconfiguration plan was internally inconsistent.
    #[error("bundle `{artifact_id}` rejected reconfiguration plan: {reason}")]
    InvalidReconfigurationPlan {
        /// Certificate artifact id associated with the rejected bundle.
        artifact_id: String,
        /// Human-readable validation reason.
        reason: String,
    },
    /// Admission would violate memory budget.
    #[error("bundle `{artifact_id}` rejected: memory budget exceeded ({reason})")]
    BudgetExceeded {
        /// Certificate artifact id associated with the rejected bundle.
        artifact_id: String,
        /// Human-readable budget reason.
        reason: String,
    },
    /// ProtocolMachine-layer load/run failure.
    #[error(transparent)]
    Vm(#[from] ProtocolMachineError),
}

/// Runtime wrapper for composed protocol execution.
#[derive(Debug)]
pub struct ComposedRuntime {
    machine: ProtocolMachine,
    bundles: Vec<ProtocolBundle>,
    reconfiguration_states: Vec<Option<ReconfigurationRuntimeState>>,
    budget: MemoryBudget,
    usage: MemoryUsage,
}

impl ComposedRuntime {
    /// Create an empty composed runtime.
    #[must_use]
    pub fn new(config: ProtocolMachineConfig, budget: MemoryBudget) -> Self {
        let machine = ProtocolMachine::new(config);
        Self {
            machine,
            bundles: Vec::new(),
            reconfiguration_states: Vec::new(),
            budget,
            usage: MemoryUsage {
                bytes_per_coroutine: size_of::<crate::coroutine::Coroutine>(),
                bytes_per_session: size_of::<crate::session::SessionState>(),
                incremental_bytes_per_protocol: size_of::<Arc<CodeImage>>(),
                ..MemoryUsage::default()
            },
        }
    }

    /// Admit a protocol bundle after certificate + budget checks.
    ///
    /// # Errors
    ///
    /// Returns a `CompositionError` when proof or budget checks fail.
    pub fn admit_bundle(&mut self, bundle: ProtocolBundle) -> Result<(), CompositionError> {
        if !bundle.certificate.link_ok_full {
            return Err(CompositionError::MissingCompatibilityProof {
                artifact_id: bundle.certificate.artifact_id,
            });
        }
        self.require_capabilities(&bundle)?;

        if self.usage.incremental_bytes_per_protocol
            > self.budget.max_incremental_bytes_per_protocol
        {
            return Err(CompositionError::BudgetExceeded {
                artifact_id: bundle.certificate.artifact_id,
                reason: "incremental protocol overhead".to_string(),
            });
        }

        self.bundles.push(bundle);
        self.reconfiguration_states
            .push(Some(ReconfigurationRuntimeState::default()));
        self.usage.protocol_count = self.bundles.len();
        Ok(())
    }

    /// Load one session instance from an admitted bundle index.
    ///
    /// # Errors
    ///
    /// Returns a `CompositionError` when index is invalid or ProtocolMachine loading fails.
    pub fn load_bundle_session(&mut self, bundle_idx: usize) -> Result<usize, CompositionError> {
        let bundle = self
            .bundles
            .get(bundle_idx)
            .ok_or(CompositionError::InvalidBundleIndex { bundle_idx })?;

        let sid = self.machine.load_choreography(&bundle.code)?;
        self.refresh_usage();
        self.assert_budget(bundle_idx)?;
        Ok(sid)
    }

    /// Load `sessions` instances from a bundle index.
    ///
    /// # Errors
    ///
    /// Returns a `CompositionError` when any session load fails.
    pub fn load_bundle_sessions(
        &mut self,
        bundle_idx: usize,
        sessions: usize,
    ) -> Result<Vec<usize>, CompositionError> {
        let mut out = Vec::with_capacity(sessions);
        for _ in 0..sessions {
            out.push(self.load_bundle_session(bundle_idx)?);
        }
        Ok(out)
    }

    /// Run the composed runtime.
    ///
    /// # Errors
    ///
    /// Returns ProtocolMachine-layer errors as composition errors.
    pub fn run(
        &mut self,
        handler: &dyn EffectHandler,
        max_steps: usize,
    ) -> Result<(), CompositionError> {
        self.machine.run(handler, max_steps)?;
        self.refresh_usage();
        Ok(())
    }

    /// Access current memory usage snapshot.
    #[must_use]
    pub fn memory_usage(&self) -> &MemoryUsage {
        &self.usage
    }

    /// Access admitted bundles.
    #[must_use]
    pub fn bundles(&self) -> &[ProtocolBundle] {
        &self.bundles
    }

    fn simulate_reconfiguration_transition(
        artifact_id: &str,
        policy: &ReconfigurationPolicy,
        state: &mut ReconfigurationRuntimeState,
        next_members: BTreeSet<String>,
    ) -> Result<ReconfigurationEvent, CompositionError> {
        if next_members.is_empty() {
            return Err(CompositionError::EmptyMembership {
                artifact_id: artifact_id.to_string(),
            });
        }

        let overlap_preserved =
            state.active_members.is_empty() || !state.active_members.is_disjoint(&next_members);
        if policy.overlap_required && !overlap_preserved {
            return Err(CompositionError::OverlapRequiredViolation {
                artifact_id: artifact_id.to_string(),
            });
        }

        let previous_members: Vec<String> = state.active_members.iter().cloned().collect();
        let next_members_vec: Vec<String> = next_members.iter().cloned().collect();
        let added_members: Vec<String> = next_members
            .difference(&state.active_members)
            .cloned()
            .collect();
        let removed_members: Vec<String> = state
            .active_members
            .difference(&next_members)
            .cloned()
            .collect();

        state.epoch = state.epoch.saturating_add(1);
        state.active_members = next_members;
        let event = ReconfigurationEvent {
            artifact_id: artifact_id.to_string(),
            epoch: state.epoch,
            previous_members,
            next_members: next_members_vec,
            added_members,
            removed_members,
            overlap_preserved,
            dynamic_membership: policy.dynamic_membership,
            overlap_required: policy.overlap_required,
        };
        state.history.push(event.clone());
        Ok(event)
    }

    fn validate_plan_step(
        artifact_id: &str,
        step: &ReconfigurationPlanStep,
    ) -> Result<
        (
            BTreeSet<String>,
            Vec<PlacementObservation>,
            Vec<TransportBoundaryObservation>,
        ),
        CompositionError,
    > {
        let next_members = step.next_members.iter().cloned().collect::<BTreeSet<_>>();
        if next_members.is_empty() {
            return Err(CompositionError::InvalidReconfigurationPlan {
                artifact_id: artifact_id.to_string(),
                reason: format!(
                    "step `{}` must preserve a non-empty membership set",
                    step.step_id
                ),
            });
        }
        let placements =
            canonicalize_placement_observations(&step.placements).map_err(|reason| {
                CompositionError::InvalidReconfigurationPlan {
                    artifact_id: artifact_id.to_string(),
                    reason: format!("step `{}` has invalid placements: {reason}", step.step_id),
                }
            })?;
        let placement_roles = placements
            .iter()
            .map(|placement| placement.role.clone())
            .collect::<BTreeSet<_>>();
        if placement_roles != next_members {
            return Err(CompositionError::InvalidReconfigurationPlan {
                artifact_id: artifact_id.to_string(),
                reason: format!(
                    "step `{}` placements must match next_members exactly",
                    step.step_id
                ),
            });
        }
        let transport_boundaries =
            canonical_transport_boundaries(&placements).map_err(|reason| {
                CompositionError::InvalidReconfigurationPlan {
                    artifact_id: artifact_id.to_string(),
                    reason: format!(
                        "step `{}` has invalid transport boundaries: {reason}",
                        step.step_id
                    ),
                }
            })?;
        Ok((next_members, placements, transport_boundaries))
    }

    fn snapshot_from_state(state: &ReconfigurationRuntimeState) -> ReconfigurationRuntimeSnapshot {
        ReconfigurationRuntimeSnapshot {
            epoch: state.epoch,
            active_members: state.active_members.iter().cloned().collect(),
            history: state.history.clone(),
            plan_executions: state.plan_executions.clone(),
        }
    }

    fn restore_snapshot_into_state(
        artifact_id: &str,
        state: &mut ReconfigurationRuntimeState,
        snapshot: ReconfigurationRuntimeSnapshot,
    ) -> Result<(), CompositionError> {
        let active_members = snapshot
            .active_members
            .iter()
            .cloned()
            .collect::<BTreeSet<_>>();
        if active_members.is_empty() {
            return Err(CompositionError::InvalidReconfigurationPlan {
                artifact_id: artifact_id.to_string(),
                reason: "snapshot must preserve a non-empty active membership set".to_string(),
            });
        }
        if snapshot
            .history
            .windows(2)
            .any(|window| window[0].epoch >= window[1].epoch)
        {
            return Err(CompositionError::InvalidReconfigurationPlan {
                artifact_id: artifact_id.to_string(),
                reason: "snapshot history must have strictly increasing epochs".to_string(),
            });
        }
        if let Some(last_event) = snapshot.history.last() {
            let final_from_history = last_event
                .next_members
                .iter()
                .cloned()
                .collect::<BTreeSet<_>>();
            if final_from_history != active_members {
                return Err(CompositionError::InvalidReconfigurationPlan {
                    artifact_id: artifact_id.to_string(),
                    reason: "snapshot active membership must match the final history event"
                        .to_string(),
                });
            }
            if last_event.epoch != snapshot.epoch {
                return Err(CompositionError::InvalidReconfigurationPlan {
                    artifact_id: artifact_id.to_string(),
                    reason: "snapshot epoch must match the final history event epoch".to_string(),
                });
            }
        } else if snapshot.epoch != 0 {
            return Err(CompositionError::InvalidReconfigurationPlan {
                artifact_id: artifact_id.to_string(),
                reason: "empty snapshot history must use epoch 0".to_string(),
            });
        }
        if snapshot
            .plan_executions
            .iter()
            .any(|execution| execution.phases.is_empty())
        {
            return Err(CompositionError::InvalidReconfigurationPlan {
                artifact_id: artifact_id.to_string(),
                reason: "snapshot plan executions must contain at least one phase".to_string(),
            });
        }
        state.epoch = snapshot.epoch;
        state.active_members = active_members;
        state.history = snapshot.history;
        state.plan_executions = snapshot.plan_executions;
        Ok(())
    }

    /// Seed the active membership set for one admitted reconfiguration-enabled bundle.
    ///
    /// # Errors
    ///
    /// Returns a `CompositionError` when the bundle index is invalid, reconfiguration is disabled,
    /// or the membership set is empty.
    pub fn seed_bundle_membership<I, S>(
        &mut self,
        bundle_idx: usize,
        members: I,
    ) -> Result<(), CompositionError>
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        let bundle = self
            .bundles
            .get(bundle_idx)
            .ok_or(CompositionError::InvalidBundleIndex { bundle_idx })?;
        let state = self
            .reconfiguration_states
            .get_mut(bundle_idx)
            .ok_or(CompositionError::InvalidBundleIndex { bundle_idx })?
            .as_mut()
            .ok_or_else(|| CompositionError::ReconfigurationDisabled {
                artifact_id: bundle.certificate.artifact_id.clone(),
            })?;
        if bundle.reconfiguration_policy.is_none() {
            return Err(CompositionError::ReconfigurationDisabled {
                artifact_id: bundle.certificate.artifact_id.clone(),
            });
        }
        let members: BTreeSet<String> = members.into_iter().map(Into::into).collect();
        if members.is_empty() {
            return Err(CompositionError::EmptyMembership {
                artifact_id: bundle.certificate.artifact_id.clone(),
            });
        }
        state.active_members = members;
        state.epoch = 0;
        state.history.clear();
        state.plan_executions.clear();
        Ok(())
    }

    /// Apply one deterministic reconfiguration transition to an admitted bundle.
    ///
    /// # Errors
    ///
    /// Returns a `CompositionError` when the bundle index is invalid, the bundle does not admit
    /// reconfiguration, the transition violates required overlap, or the new membership set is
    /// empty.
    pub fn reconfigure_bundle<I, S>(
        &mut self,
        bundle_idx: usize,
        next_members: I,
    ) -> Result<ReconfigurationEvent, CompositionError>
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        let bundle = self
            .bundles
            .get(bundle_idx)
            .ok_or(CompositionError::InvalidBundleIndex { bundle_idx })?;
        let Some(policy) = bundle.reconfiguration_policy.as_ref() else {
            return Err(CompositionError::ReconfigurationDisabled {
                artifact_id: bundle.certificate.artifact_id.clone(),
            });
        };
        if !policy.dynamic_membership {
            return Err(CompositionError::ReconfigurationDisabled {
                artifact_id: bundle.certificate.artifact_id.clone(),
            });
        }

        let state = self
            .reconfiguration_states
            .get_mut(bundle_idx)
            .ok_or(CompositionError::InvalidBundleIndex { bundle_idx })?
            .as_mut()
            .ok_or_else(|| CompositionError::ReconfigurationDisabled {
                artifact_id: bundle.certificate.artifact_id.clone(),
            })?;
        let next_members: BTreeSet<String> = next_members.into_iter().map(Into::into).collect();
        Self::simulate_reconfiguration_transition(
            &bundle.certificate.artifact_id,
            policy,
            state,
            next_members,
        )
    }

    /// The canonical sorted active member set for one bundle, if configured.
    #[must_use]
    pub fn bundle_members(&self, bundle_idx: usize) -> Option<&BTreeSet<String>> {
        self.reconfiguration_states
            .get(bundle_idx)
            .and_then(Option::as_ref)
            .map(|state| &state.active_members)
    }

    /// The deterministic reconfiguration history for one bundle, if configured.
    #[must_use]
    pub fn bundle_reconfiguration_history(
        &self,
        bundle_idx: usize,
    ) -> Option<&[ReconfigurationEvent]> {
        self.reconfiguration_states
            .get(bundle_idx)
            .and_then(Option::as_ref)
            .map(|state| state.history.as_slice())
    }

    /// Execute one deterministic multi-step reconfiguration plan atomically.
    ///
    /// # Errors
    ///
    /// Returns a `CompositionError` when any plan step is invalid or violates the admitted policy.
    pub fn execute_reconfiguration_plan(
        &mut self,
        bundle_idx: usize,
        plan: &ReconfigurationPlan,
    ) -> Result<ReconfigurationPlanExecution, CompositionError> {
        let bundle = self
            .bundles
            .get(bundle_idx)
            .ok_or(CompositionError::InvalidBundleIndex { bundle_idx })?;
        let Some(policy) = bundle.reconfiguration_policy.as_ref() else {
            return Err(CompositionError::ReconfigurationDisabled {
                artifact_id: bundle.certificate.artifact_id.clone(),
            });
        };
        if !policy.dynamic_membership {
            return Err(CompositionError::ReconfigurationDisabled {
                artifact_id: bundle.certificate.artifact_id.clone(),
            });
        }
        if plan.steps.is_empty() {
            return Err(CompositionError::InvalidReconfigurationPlan {
                artifact_id: bundle.certificate.artifact_id.clone(),
                reason: format!("plan `{}` must contain at least one step", plan.plan_id),
            });
        }

        let state = self
            .reconfiguration_states
            .get_mut(bundle_idx)
            .ok_or(CompositionError::InvalidBundleIndex { bundle_idx })?
            .as_mut()
            .ok_or_else(|| CompositionError::ReconfigurationDisabled {
                artifact_id: bundle.certificate.artifact_id.clone(),
            })?;
        let initial_members = state.active_members.iter().cloned().collect::<Vec<_>>();
        let mut simulated = state.clone();
        let mut phases = Vec::new();
        for step in &plan.steps {
            let (next_members, placements, transport_boundaries) =
                Self::validate_plan_step(&bundle.certificate.artifact_id, step)?;
            let event = Self::simulate_reconfiguration_transition(
                &bundle.certificate.artifact_id,
                policy,
                &mut simulated,
                next_members,
            )?;
            phases.push(ReconfigurationPhaseArtifact {
                step_id: step.step_id.clone(),
                event,
                placements,
                transport_boundaries,
            });
        }

        let execution = ReconfigurationPlanExecution {
            artifact_id: bundle.certificate.artifact_id.clone(),
            plan_id: plan.plan_id.clone(),
            initial_members,
            final_members: simulated.active_members.iter().cloned().collect(),
            phases,
        };
        simulated.plan_executions.push(execution.clone());
        *state = simulated;
        Ok(execution)
    }

    /// The deterministic reconfiguration plan executions for one bundle, if configured.
    #[must_use]
    pub fn bundle_reconfiguration_plan_executions(
        &self,
        bundle_idx: usize,
    ) -> Option<&[ReconfigurationPlanExecution]> {
        self.reconfiguration_states
            .get(bundle_idx)
            .and_then(Option::as_ref)
            .map(|state| state.plan_executions.as_slice())
    }

    /// Export a deterministic snapshot of the reconfiguration state for one bundle.
    #[must_use]
    pub fn bundle_reconfiguration_snapshot(
        &self,
        bundle_idx: usize,
    ) -> Option<ReconfigurationRuntimeSnapshot> {
        self.reconfiguration_states
            .get(bundle_idx)
            .and_then(Option::as_ref)
            .map(Self::snapshot_from_state)
    }

    /// Restore a previously exported reconfiguration snapshot for one admitted bundle.
    ///
    /// # Errors
    ///
    /// Returns a `CompositionError` when the snapshot is inconsistent with the admitted policy.
    pub fn restore_bundle_reconfiguration_snapshot(
        &mut self,
        bundle_idx: usize,
        snapshot: ReconfigurationRuntimeSnapshot,
    ) -> Result<(), CompositionError> {
        let bundle = self
            .bundles
            .get(bundle_idx)
            .ok_or(CompositionError::InvalidBundleIndex { bundle_idx })?;
        if bundle.reconfiguration_policy.is_none() {
            return Err(CompositionError::ReconfigurationDisabled {
                artifact_id: bundle.certificate.artifact_id.clone(),
            });
        }
        let state = self
            .reconfiguration_states
            .get_mut(bundle_idx)
            .ok_or(CompositionError::InvalidBundleIndex { bundle_idx })?
            .as_mut()
            .ok_or_else(|| CompositionError::ReconfigurationDisabled {
                artifact_id: bundle.certificate.artifact_id.clone(),
            })?;
        Self::restore_snapshot_into_state(&bundle.certificate.artifact_id, state, snapshot)
    }

    /// Access underlying ProtocolMachine.
    #[must_use]
    pub fn machine(&self) -> &ProtocolMachine {
        &self.machine
    }

    fn refresh_usage(&mut self) {
        self.usage.session_count = self.machine.session_count();
        self.usage.coroutine_count = self.machine.coroutine_count();
        self.usage.protocol_count = self.bundles.len();
    }

    fn assert_budget(&self, bundle_idx: usize) -> Result<(), CompositionError> {
        let per_coro = self.usage.bytes_per_coroutine;
        let per_sess = self.usage.bytes_per_session;
        let artifact_id = self
            .bundles
            .get(bundle_idx)
            .map(|b| b.certificate.artifact_id.clone())
            .unwrap_or_else(|| format!("bundle/{bundle_idx}"));
        if per_coro > self.budget.max_bytes_per_coroutine {
            return Err(CompositionError::BudgetExceeded {
                artifact_id,
                reason: "bytes_per_coroutine".to_string(),
            });
        }
        if per_sess > self.budget.max_bytes_per_session {
            return Err(CompositionError::BudgetExceeded {
                artifact_id,
                reason: "bytes_per_session".to_string(),
            });
        }
        Ok(())
    }

    fn require_capabilities(&self, bundle: &ProtocolBundle) -> Result<(), CompositionError> {
        let cert = &bundle.certificate;
        let caps = &cert.theorem_pack;
        let runtime_contracts = cert.runtime_contracts.as_ref();

        match enforce_protocol_machine_runtime_gates(self.machine.config(), runtime_contracts) {
            RuntimeGateResult::Admitted => {}
            RuntimeGateResult::RejectedMissingContracts => {
                return Err(CompositionError::MissingRuntimeContracts {
                    artifact_id: cert.artifact_id.clone(),
                });
            }
            RuntimeGateResult::RejectedUnsupportedDeterminismProfile => {
                return Err(CompositionError::MissingCapability {
                    artifact_id: cert.artifact_id.clone(),
                    capability: format!(
                        "determinism_profile::{:?}",
                        self.machine.config().determinism_mode
                    ),
                });
            }
        }

        let required_sched = match self.machine.config().sched_policy {
            SchedPolicy::Cooperative => SchedulerCapability::Cooperative,
            SchedPolicy::RoundRobin => SchedulerCapability::RoundRobin,
            SchedPolicy::Priority(_) => SchedulerCapability::Priority,
            SchedPolicy::ProgressAware => SchedulerCapability::ProgressAware,
        };
        if !caps.schedulers.contains(&required_sched) {
            return Err(CompositionError::MissingCapability {
                artifact_id: cert.artifact_id.clone(),
                capability: format!("scheduler::{required_sched:?}"),
            });
        }

        let required_det = match self.machine.config().determinism_mode {
            DeterminismMode::Full => DeterminismCapability::Full,
            DeterminismMode::ModuloEffects => DeterminismCapability::ModuloEffects,
            DeterminismMode::ModuloCommutativity => DeterminismCapability::ModuloCommutativity,
            DeterminismMode::Replay => DeterminismCapability::Replay,
        };
        if !caps.determinism.contains(&required_det) {
            return Err(CompositionError::MissingCapability {
                artifact_id: cert.artifact_id.clone(),
                capability: format!("determinism::{required_det:?}"),
            });
        }
        if !execution_profile_supported(
            &caps.execution_profile(),
            self.machine.config(),
            runtime_contracts,
        ) {
            return Err(CompositionError::MissingCapability {
                artifact_id: cert.artifact_id.clone(),
                capability: "execution_profile".to_string(),
            });
        }
        if !matches!(
            self.machine.config().output_condition_policy,
            OutputConditionPolicy::Disabled
        ) && !caps.output_condition_gating
        {
            return Err(CompositionError::MissingCapability {
                artifact_id: cert.artifact_id.clone(),
                capability: "output_condition_gating".to_string(),
            });
        }
        if let Some(policy) = &bundle.reconfiguration_policy {
            let Some(contracts) = runtime_contracts else {
                return Err(CompositionError::MissingRuntimeContracts {
                    artifact_id: cert.artifact_id.clone(),
                });
            };
            if !contracts
                .capabilities
                .contains(&crate::runtime_contracts::RuntimeCapability::PlacementRefinement)
            {
                return Err(CompositionError::MissingReconfigurationCapability {
                    artifact_id: cert.artifact_id.clone(),
                    capability: "reconfiguration::placement_refinement".to_string(),
                });
            }
            if policy.dynamic_membership
                && !contracts
                    .capabilities
                    .contains(&crate::runtime_contracts::RuntimeCapability::AutoscaleRepartition)
            {
                return Err(CompositionError::MissingReconfigurationCapability {
                    artifact_id: cert.artifact_id.clone(),
                    capability: "reconfiguration::dynamic_membership".to_string(),
                });
            }
            if policy.overlap_required
                && !contracts
                    .capabilities
                    .contains(&crate::runtime_contracts::RuntimeCapability::LiveMigration)
            {
                return Err(CompositionError::MissingReconfigurationCapability {
                    artifact_id: cert.artifact_id.clone(),
                    capability: "reconfiguration::overlap_required".to_string(),
                });
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use telltale_types::{GlobalType, Label, LocalTypeR};

    use super::*;
    use crate::coroutine::Value;
    use crate::effect::{EffectFailure, EffectResult};

    #[derive(Debug, Clone, Copy)]
    struct Noop;

    impl EffectHandler for Noop {
        fn handle_send(
            &self,
            _role: &str,
            _partner: &str,
            label: &str,
            _state: &[Value],
        ) -> EffectResult<Value> {
            EffectResult::success(Value::Str(label.to_string()))
        }

        fn handle_recv(
            &self,
            _role: &str,
            _partner: &str,
            _label: &str,
            _state: &mut Vec<Value>,
            _payload: &Value,
        ) -> EffectResult<()> {
            EffectResult::success(())
        }

        fn handle_choose(
            &self,
            _role: &str,
            _partner: &str,
            labels: &[String],
            _state: &[Value],
        ) -> EffectResult<String> {
            match labels.first().cloned() {
                Some(label) => EffectResult::success(label),
                None => EffectResult::failure(EffectFailure::invalid_input("no labels available")),
            }
        }

        fn step(&self, _role: &str, _state: &mut Vec<Value>) -> EffectResult<()> {
            EffectResult::success(())
        }
    }

    fn image(label: &str) -> Arc<CodeImage> {
        let mut local_types = BTreeMap::new();
        local_types.insert(
            "A".to_string(),
            LocalTypeR::send("B", Label::new(label), LocalTypeR::End),
        );
        local_types.insert(
            "B".to_string(),
            LocalTypeR::recv("A", Label::new(label), LocalTypeR::End),
        );
        let global = GlobalType::send("A", "B", Label::new(label), GlobalType::End);
        Arc::new(CodeImage::from_local_types(&local_types, &global))
    }

    #[test]
    fn proof_carrying_admission_rejects_missing_link_ok_full() {
        let mut runtime =
            ComposedRuntime::new(ProtocolMachineConfig::default(), MemoryBudget::default());
        let bad = ProtocolBundle::new(
            image("m"),
            CompositionCertificate {
                artifact_id: "cert/bad".to_string(),
                link_ok_full: false,
                theorem_pack: TheoremPackCapabilities::full(),
                runtime_contracts: None,
            },
        );
        assert!(matches!(
            runtime.admit_bundle(bad),
            Err(CompositionError::MissingCompatibilityProof { .. })
        ));
    }

    #[test]
    fn immutable_code_artifacts_are_arc_shared() {
        let shared = image("m");
        let mut runtime =
            ComposedRuntime::new(ProtocolMachineConfig::default(), MemoryBudget::default());
        let b1 = ProtocolBundle::new(
            Arc::clone(&shared),
            CompositionCertificate {
                artifact_id: "cert/1".to_string(),
                link_ok_full: true,
                theorem_pack: TheoremPackCapabilities::full(),
                runtime_contracts: None,
            },
        );
        let b2 = ProtocolBundle::new(
            Arc::clone(&shared),
            CompositionCertificate {
                artifact_id: "cert/2".to_string(),
                link_ok_full: true,
                theorem_pack: TheoremPackCapabilities::full(),
                runtime_contracts: None,
            },
        );
        runtime.admit_bundle(b1).expect("admit b1");
        runtime.admit_bundle(b2).expect("admit b2");
        assert!(
            Arc::strong_count(&shared) >= 3,
            "bundle admission should keep shared immutable artifacts in Arc"
        );
    }

    #[test]
    fn composed_execution_runs_and_usage_grows_monotonically() {
        let mut runtime =
            ComposedRuntime::new(ProtocolMachineConfig::default(), MemoryBudget::default());
        let b = ProtocolBundle::new(
            image("m"),
            CompositionCertificate {
                artifact_id: "cert/ok".to_string(),
                link_ok_full: true,
                theorem_pack: TheoremPackCapabilities::full(),
                runtime_contracts: None,
            },
        );
        runtime.admit_bundle(b).expect("admit");
        runtime
            .load_bundle_sessions(0, 8)
            .expect("load composed sessions");
        let usage_before = runtime.memory_usage().clone();
        assert!(usage_before.session_count >= 8);
        assert!(usage_before.coroutine_count >= 16);
        runtime.run(&Noop, 512).expect("composed run");
        let usage_after = runtime.memory_usage().clone();
        assert!(usage_after.session_count >= usage_before.session_count);
        assert!(usage_after.coroutine_count >= usage_before.coroutine_count);
    }

    #[test]
    fn admission_rejects_missing_scheduler_profile_capability() {
        let cfg = ProtocolMachineConfig {
            sched_policy: SchedPolicy::ProgressAware,
            ..ProtocolMachineConfig::default()
        };
        let mut runtime = ComposedRuntime::new(cfg, MemoryBudget::default());
        let bundle = ProtocolBundle::new(
            image("m"),
            CompositionCertificate {
                artifact_id: "cert/no-sched".to_string(),
                link_ok_full: true,
                theorem_pack: TheoremPackCapabilities {
                    determinism: vec![DeterminismCapability::Full],
                    schedulers: vec![SchedulerCapability::Cooperative],
                    output_condition_gating: true,
                },
                runtime_contracts: Some(RuntimeContracts::full()),
            },
        );

        let err = runtime
            .admit_bundle(bundle)
            .expect_err("should reject bundle");
        assert!(matches!(
            err,
            CompositionError::MissingCapability { capability, .. }
            if capability == "scheduler::ProgressAware"
        ));
    }

    #[test]
    fn admission_rejects_missing_determinism_capability() {
        let cfg = ProtocolMachineConfig {
            determinism_mode: DeterminismMode::ModuloCommutativity,
            ..ProtocolMachineConfig::default()
        };
        let mut runtime = ComposedRuntime::new(cfg, MemoryBudget::default());
        let bundle = ProtocolBundle::new(
            image("m"),
            CompositionCertificate {
                artifact_id: "cert/no-det".to_string(),
                link_ok_full: true,
                theorem_pack: TheoremPackCapabilities {
                    determinism: vec![DeterminismCapability::Full],
                    schedulers: vec![SchedulerCapability::Cooperative],
                    output_condition_gating: true,
                },
                runtime_contracts: Some(RuntimeContracts::full()),
            },
        );

        let err = runtime
            .admit_bundle(bundle)
            .expect_err("should reject bundle");
        assert!(matches!(
            err,
            CompositionError::MissingCapability { capability, .. }
            if capability == "determinism::ModuloCommutativity"
        ));
    }

    #[test]
    fn admission_rejects_missing_output_condition_capability() {
        let cfg = ProtocolMachineConfig {
            output_condition_policy: OutputConditionPolicy::AllowAll,
            ..ProtocolMachineConfig::default()
        };
        let mut runtime = ComposedRuntime::new(cfg, MemoryBudget::default());
        let bundle = ProtocolBundle::new(
            image("m"),
            CompositionCertificate {
                artifact_id: "cert/no-output-gate".to_string(),
                link_ok_full: true,
                theorem_pack: TheoremPackCapabilities {
                    determinism: vec![DeterminismCapability::Full],
                    schedulers: vec![SchedulerCapability::Cooperative],
                    output_condition_gating: false,
                },
                runtime_contracts: None,
            },
        );

        let err = runtime
            .admit_bundle(bundle)
            .expect_err("should reject bundle");
        assert!(matches!(
            err,
            CompositionError::MissingCapability { capability, .. }
            if capability == "execution_profile"
        ));
    }

    #[test]
    fn admission_accepts_when_required_capabilities_present() {
        let cfg = ProtocolMachineConfig {
            sched_policy: SchedPolicy::RoundRobin,
            determinism_mode: DeterminismMode::ModuloEffects,
            output_condition_policy: OutputConditionPolicy::PredicateAllowList(vec![
                "protocol_machine.observable_output".to_string(),
            ]),
            ..ProtocolMachineConfig::default()
        };
        let mut runtime = ComposedRuntime::new(cfg, MemoryBudget::default());
        let bundle = ProtocolBundle::new(
            image("m"),
            CompositionCertificate {
                artifact_id: "cert/full".to_string(),
                link_ok_full: true,
                theorem_pack: TheoremPackCapabilities::full(),
                runtime_contracts: Some(RuntimeContracts::full()),
            },
        );
        runtime
            .admit_bundle(bundle)
            .expect("bundle should be admitted");
    }

    #[test]
    fn admission_accepts_minimal_required_capabilities_without_full_parity() {
        let cfg = ProtocolMachineConfig::default();
        let mut runtime = ComposedRuntime::new(cfg, MemoryBudget::default());
        let bundle = ProtocolBundle::new(
            image("m"),
            CompositionCertificate {
                artifact_id: "cert/minimal-required".to_string(),
                link_ok_full: true,
                theorem_pack: TheoremPackCapabilities {
                    determinism: vec![DeterminismCapability::Full],
                    schedulers: vec![
                        SchedulerCapability::Cooperative,
                        SchedulerCapability::ProgressAware,
                    ],
                    output_condition_gating: true,
                },
                runtime_contracts: None,
            },
        );
        runtime
            .admit_bundle(bundle)
            .expect("minimal required capabilities should be sufficient");
    }

    #[test]
    fn admission_rejects_advanced_mode_without_runtime_contracts() {
        let cfg = ProtocolMachineConfig {
            sched_policy: SchedPolicy::RoundRobin,
            ..ProtocolMachineConfig::default()
        };
        let mut runtime = ComposedRuntime::new(cfg, MemoryBudget::default());
        let bundle = ProtocolBundle::new(
            image("m"),
            CompositionCertificate {
                artifact_id: "cert/no-runtime-contracts".to_string(),
                link_ok_full: true,
                theorem_pack: TheoremPackCapabilities::full(),
                runtime_contracts: None,
            },
        );
        let err = runtime
            .admit_bundle(bundle)
            .expect_err("advanced mode should reject missing runtime contracts");
        assert!(matches!(
            err,
            CompositionError::MissingRuntimeContracts { .. }
        ));
    }

    #[test]
    fn admission_rejects_replay_profile_without_mixed_profile_gate() {
        let cfg = ProtocolMachineConfig {
            determinism_mode: DeterminismMode::Replay,
            ..ProtocolMachineConfig::default()
        };
        let mut runtime = ComposedRuntime::new(cfg, MemoryBudget::default());
        let mut contracts = RuntimeContracts::full();
        contracts.can_use_mixed_determinism_profiles = false;
        let bundle = ProtocolBundle::new(
            image("m"),
            CompositionCertificate {
                artifact_id: "cert/no-mixed-profile-gate".to_string(),
                link_ok_full: true,
                theorem_pack: TheoremPackCapabilities::full(),
                runtime_contracts: Some(contracts),
            },
        );
        let err = runtime
            .admit_bundle(bundle)
            .expect_err("replay profile should require mixed-profile gate");
        assert!(matches!(
            err,
            CompositionError::MissingCapability { capability, .. }
            if capability == "determinism_profile::Replay"
        ));
    }

    #[test]
    fn admission_accepts_replay_profile_with_contracts_and_capability() {
        let cfg = ProtocolMachineConfig {
            determinism_mode: DeterminismMode::Replay,
            ..ProtocolMachineConfig::default()
        };
        let mut runtime = ComposedRuntime::new(cfg, MemoryBudget::default());
        let bundle = ProtocolBundle::new(
            image("m"),
            CompositionCertificate {
                artifact_id: "cert/replay-ok".to_string(),
                link_ok_full: true,
                theorem_pack: TheoremPackCapabilities::full(),
                runtime_contracts: Some(RuntimeContracts::full()),
            },
        );
        runtime
            .admit_bundle(bundle)
            .expect("replay profile should admit with matching contracts");
    }

    #[test]
    fn reconfiguration_requires_runtime_capabilities_at_admission() {
        let mut runtime =
            ComposedRuntime::new(ProtocolMachineConfig::default(), MemoryBudget::default());
        let mut contracts = RuntimeContracts::full();
        contracts
            .capabilities
            .remove(&crate::runtime_contracts::RuntimeCapability::AutoscaleRepartition);
        let bundle = ProtocolBundle::new(
            image("m"),
            CompositionCertificate {
                artifact_id: "cert/reconfig-missing-cap".to_string(),
                link_ok_full: true,
                theorem_pack: TheoremPackCapabilities::full(),
                runtime_contracts: Some(contracts),
            },
        )
        .with_reconfiguration_policy(ReconfigurationPolicy {
            dynamic_membership: true,
            overlap_required: true,
        });
        let err = runtime
            .admit_bundle(bundle)
            .expect_err("dynamic membership should require explicit runtime capability");
        assert!(matches!(
            err,
            CompositionError::MissingReconfigurationCapability { capability, .. }
            if capability == "reconfiguration::dynamic_membership"
        ));
    }

    #[test]
    fn reconfiguration_emits_deterministic_membership_events() {
        let mut runtime =
            ComposedRuntime::new(ProtocolMachineConfig::default(), MemoryBudget::default());
        let bundle = ProtocolBundle::new(
            image("m"),
            CompositionCertificate {
                artifact_id: "cert/reconfig-ok".to_string(),
                link_ok_full: true,
                theorem_pack: TheoremPackCapabilities::full(),
                runtime_contracts: Some(RuntimeContracts::full()),
            },
        )
        .with_reconfiguration_policy(ReconfigurationPolicy {
            dynamic_membership: true,
            overlap_required: true,
        });
        runtime.admit_bundle(bundle).expect("admit bundle");
        runtime
            .seed_bundle_membership(0, ["Alice", "Bob"])
            .expect("seed members");

        let event = runtime
            .reconfigure_bundle(0, ["Bob", "Carol"])
            .expect("reconfigure");
        assert_eq!(event.epoch, 1);
        assert_eq!(event.previous_members, vec!["Alice", "Bob"]);
        assert_eq!(event.next_members, vec!["Bob", "Carol"]);
        assert_eq!(event.added_members, vec!["Carol"]);
        assert_eq!(event.removed_members, vec!["Alice"]);
        assert!(event.overlap_preserved);
        assert_eq!(
            runtime
                .bundle_members(0)
                .expect("members after reconfiguration"),
            &BTreeSet::from(["Bob".to_string(), "Carol".to_string()])
        );
        assert_eq!(
            runtime
                .bundle_reconfiguration_history(0)
                .expect("history")
                .last()
                .expect("event in history"),
            &event
        );
    }

    #[test]
    fn reconfiguration_rejects_disjoint_membership_when_overlap_is_required() {
        let mut runtime =
            ComposedRuntime::new(ProtocolMachineConfig::default(), MemoryBudget::default());
        let bundle = ProtocolBundle::new(
            image("m"),
            CompositionCertificate {
                artifact_id: "cert/reconfig-overlap".to_string(),
                link_ok_full: true,
                theorem_pack: TheoremPackCapabilities::full(),
                runtime_contracts: Some(RuntimeContracts::full()),
            },
        )
        .with_reconfiguration_policy(ReconfigurationPolicy {
            dynamic_membership: true,
            overlap_required: true,
        });
        runtime.admit_bundle(bundle).expect("admit bundle");
        runtime
            .seed_bundle_membership(0, ["Alice", "Bob"])
            .expect("seed members");
        let err = runtime
            .reconfigure_bundle(0, ["Carol", "Dave"])
            .expect_err("overlap-required policy should reject disjoint membership");
        assert!(matches!(
            err,
            CompositionError::OverlapRequiredViolation { .. }
        ));
    }

    #[test]
    fn reconfiguration_history_is_stable_across_recreated_runtimes() {
        fn drive_history() -> Vec<ReconfigurationEvent> {
            let mut runtime =
                ComposedRuntime::new(ProtocolMachineConfig::default(), MemoryBudget::default());
            let bundle = ProtocolBundle::new(
                image("m"),
                CompositionCertificate {
                    artifact_id: "cert/reconfig-history".to_string(),
                    link_ok_full: true,
                    theorem_pack: TheoremPackCapabilities::full(),
                    runtime_contracts: Some(RuntimeContracts::full()),
                },
            )
            .with_reconfiguration_policy(ReconfigurationPolicy {
                dynamic_membership: true,
                overlap_required: true,
            });
            runtime.admit_bundle(bundle).expect("admit bundle");
            runtime
                .seed_bundle_membership(0, ["Alice", "Bob"])
                .expect("seed members");
            runtime
                .reconfigure_bundle(0, ["Bob", "Carol"])
                .expect("first reconfiguration");
            runtime
                .reconfigure_bundle(0, ["Carol", "Dave"])
                .expect("second reconfiguration");
            runtime
                .bundle_reconfiguration_history(0)
                .expect("reconfiguration history")
                .to_vec()
        }

        assert_eq!(drive_history(), drive_history());
    }

    #[test]
    fn reconfiguration_plan_executes_atomically_with_phase_artifacts() {
        let mut runtime =
            ComposedRuntime::new(ProtocolMachineConfig::default(), MemoryBudget::default());
        let bundle = ProtocolBundle::new(
            image("m"),
            CompositionCertificate {
                artifact_id: "cert/reconfig-plan".to_string(),
                link_ok_full: true,
                theorem_pack: TheoremPackCapabilities::full(),
                runtime_contracts: Some(RuntimeContracts::full()),
            },
        )
        .with_reconfiguration_policy(ReconfigurationPolicy {
            dynamic_membership: true,
            overlap_required: true,
        });
        runtime.admit_bundle(bundle).expect("admit bundle");
        runtime
            .seed_bundle_membership(0, ["Alice", "Bob"])
            .expect("seed members");

        let plan = ReconfigurationPlan {
            plan_id: "plan/blue-green".to_string(),
            steps: vec![
                ReconfigurationPlanStep {
                    step_id: "prepare".to_string(),
                    next_members: vec!["Bob".to_string(), "Carol".to_string(), "Dora".to_string()],
                    placements: vec![
                        PlacementObservation::local("Bob").with_region("eu_central_1"),
                        PlacementObservation::colocated("Carol", "Bob").with_region("eu_central_1"),
                        PlacementObservation::remote("Dora", "127.0.0.1:19821")
                            .with_region("us_east_1"),
                    ],
                },
                ReconfigurationPlanStep {
                    step_id: "cutover".to_string(),
                    next_members: vec!["Carol".to_string(), "Dora".to_string(), "Eve".to_string()],
                    placements: vec![
                        PlacementObservation::remote("Carol", "127.0.0.1:19822")
                            .with_region("us_east_1"),
                        PlacementObservation::remote("Dora", "127.0.0.1:19821")
                            .with_region("us_east_1"),
                        PlacementObservation::colocated("Eve", "Carol").with_region("us_east_1"),
                    ],
                },
            ],
        };

        let execution = runtime
            .execute_reconfiguration_plan(0, &plan)
            .expect("execute reconfiguration plan");
        assert_eq!(execution.plan_id, "plan/blue-green");
        assert_eq!(execution.initial_members, vec!["Alice", "Bob"]);
        assert_eq!(
            execution.final_members,
            vec!["Carol".to_string(), "Dora".to_string(), "Eve".to_string()]
        );
        assert_eq!(execution.phases.len(), 2);
        assert_eq!(execution.phases[0].event.epoch, 1);
        assert_eq!(execution.phases[1].event.epoch, 2);
        assert!(
            execution.phases[0]
                .transport_boundaries
                .iter()
                .any(|boundary| matches!(
                    boundary.boundary,
                    telltale_types::TransportBoundaryKind::SharedMemory
                )),
            "first phase should expose a colocated shared-memory boundary"
        );
        assert!(
            execution.phases[0]
                .transport_boundaries
                .iter()
                .any(|boundary| matches!(
                    boundary.boundary,
                    telltale_types::TransportBoundaryKind::Network
                )),
            "first phase should expose a remote network boundary"
        );
        assert_eq!(
            runtime
                .bundle_reconfiguration_history(0)
                .expect("history after plan")
                .len(),
            2
        );
        assert_eq!(
            runtime
                .bundle_reconfiguration_plan_executions(0)
                .expect("plan executions")
                .last(),
            Some(&execution)
        );
    }

    #[test]
    fn invalid_reconfiguration_plan_rejects_without_partial_commit() {
        let mut runtime =
            ComposedRuntime::new(ProtocolMachineConfig::default(), MemoryBudget::default());
        let bundle = ProtocolBundle::new(
            image("m"),
            CompositionCertificate {
                artifact_id: "cert/reconfig-plan-invalid".to_string(),
                link_ok_full: true,
                theorem_pack: TheoremPackCapabilities::full(),
                runtime_contracts: Some(RuntimeContracts::full()),
            },
        )
        .with_reconfiguration_policy(ReconfigurationPolicy {
            dynamic_membership: true,
            overlap_required: true,
        });
        runtime.admit_bundle(bundle).expect("admit bundle");
        runtime
            .seed_bundle_membership(0, ["Alice", "Bob"])
            .expect("seed members");

        let invalid_plan = ReconfigurationPlan {
            plan_id: "plan/invalid".to_string(),
            steps: vec![
                ReconfigurationPlanStep {
                    step_id: "prepare".to_string(),
                    next_members: vec!["Bob".to_string(), "Carol".to_string()],
                    placements: vec![
                        PlacementObservation::local("Bob"),
                        PlacementObservation::local("Carol"),
                    ],
                },
                ReconfigurationPlanStep {
                    step_id: "split-brain".to_string(),
                    next_members: vec!["Dora".to_string(), "Eve".to_string()],
                    placements: vec![
                        PlacementObservation::local("Dora"),
                        PlacementObservation::local("Eve"),
                    ],
                },
            ],
        };

        let err = runtime
            .execute_reconfiguration_plan(0, &invalid_plan)
            .expect_err("invalid overlap-breaking plan must reject atomically");
        assert!(matches!(
            err,
            CompositionError::OverlapRequiredViolation { .. }
        ));
        assert_eq!(
            runtime.bundle_members(0).expect("members after rejection"),
            &BTreeSet::from(["Alice".to_string(), "Bob".to_string()])
        );
        assert!(
            runtime
                .bundle_reconfiguration_history(0)
                .expect("history after rejection")
                .is_empty(),
            "failed plan must not partially commit history"
        );
        assert!(
            runtime
                .bundle_reconfiguration_plan_executions(0)
                .expect("plan executions after rejection")
                .is_empty(),
            "failed plan must not record a plan execution"
        );
    }

    #[test]
    fn reconfiguration_snapshot_restore_preserves_plan_execution_history() {
        fn configured_runtime(artifact_id: &str) -> ComposedRuntime {
            let mut runtime =
                ComposedRuntime::new(ProtocolMachineConfig::default(), MemoryBudget::default());
            let bundle = ProtocolBundle::new(
                image("m"),
                CompositionCertificate {
                    artifact_id: artifact_id.to_string(),
                    link_ok_full: true,
                    theorem_pack: TheoremPackCapabilities::full(),
                    runtime_contracts: Some(RuntimeContracts::full()),
                },
            )
            .with_reconfiguration_policy(ReconfigurationPolicy {
                dynamic_membership: true,
                overlap_required: true,
            });
            runtime.admit_bundle(bundle).expect("admit bundle");
            runtime
        }

        let mut baseline = configured_runtime("cert/reconfig-snapshot");
        baseline
            .seed_bundle_membership(0, ["Alice", "Bob"])
            .expect("seed baseline members");
        let first_plan = ReconfigurationPlan {
            plan_id: "plan/prefix".to_string(),
            steps: vec![ReconfigurationPlanStep {
                step_id: "prepare".to_string(),
                next_members: vec!["Bob".to_string(), "Carol".to_string()],
                placements: vec![
                    PlacementObservation::local("Bob").with_region("eu_central_1"),
                    PlacementObservation::remote("Carol", "127.0.0.1:19831")
                        .with_region("us_east_1"),
                ],
            }],
        };
        baseline
            .execute_reconfiguration_plan(0, &first_plan)
            .expect("execute first plan");
        let snapshot = serde_json::from_str::<ReconfigurationRuntimeSnapshot>(
            &serde_json::to_string(
                &baseline
                    .bundle_reconfiguration_snapshot(0)
                    .expect("snapshot after first plan"),
            )
            .expect("serialize snapshot"),
        )
        .expect("deserialize snapshot");

        let second_plan = ReconfigurationPlan {
            plan_id: "plan/suffix".to_string(),
            steps: vec![ReconfigurationPlanStep {
                step_id: "cutover".to_string(),
                next_members: vec!["Carol".to_string(), "Dora".to_string()],
                placements: vec![
                    PlacementObservation::remote("Carol", "127.0.0.1:19831")
                        .with_region("us_east_1"),
                    PlacementObservation::colocated("Dora", "Carol").with_region("us_east_1"),
                ],
            }],
        };
        let baseline_suffix = baseline
            .execute_reconfiguration_plan(0, &second_plan)
            .expect("execute second plan");
        let baseline_history = baseline
            .bundle_reconfiguration_history(0)
            .expect("baseline history")
            .to_vec();
        let baseline_executions = baseline
            .bundle_reconfiguration_plan_executions(0)
            .expect("baseline plan executions")
            .to_vec();

        let mut restored = configured_runtime("cert/reconfig-snapshot");
        restored
            .restore_bundle_reconfiguration_snapshot(0, snapshot)
            .expect("restore reconfiguration snapshot");
        let restored_suffix = restored
            .execute_reconfiguration_plan(0, &second_plan)
            .expect("execute suffix after restore");

        assert_eq!(restored_suffix, baseline_suffix);
        assert_eq!(
            restored
                .bundle_reconfiguration_history(0)
                .expect("restored history"),
            baseline_history.as_slice()
        );
        assert_eq!(
            restored
                .bundle_reconfiguration_plan_executions(0)
                .expect("restored plan executions"),
            baseline_executions.as_slice()
        );
    }
}
