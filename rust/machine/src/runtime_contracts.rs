//! Runtime admission and profile-gate contracts aligned with Lean surfaces.

use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};

use crate::determinism::DeterminismMode;
use crate::engine::ProtocolMachineConfig;
use crate::output_condition::OutputConditionPolicy;
use crate::scheduler::SchedPolicy;

/// ProtocolMachine admission result for advanced runtime mode checks.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum RuntimeAdmissionResult {
    /// Runtime mode is admitted.
    Admitted,
    /// Runtime mode requires contracts that were not supplied.
    RejectedMissingContracts,
}

/// Unified runtime gate result for admission + determinism profile enforcement.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum RuntimeGateResult {
    /// Runtime mode/profile is admitted.
    Admitted,
    /// Runtime mode requires contracts that were not supplied.
    RejectedMissingContracts,
    /// Determinism profile is not supported by provided artifacts/capabilities.
    RejectedUnsupportedDeterminismProfile,
}

/// How one transported theorem family participates in shipped assurance.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum TransportedTheoremUsageClass {
    /// Executed verifier/reporting surface treats this family as a black-box premise.
    BlackBoxPremiseOnly,
    /// This family materially influences a shipped runtime gate/guarantee surface.
    RuntimeCriticalInstantiatedPremise,
    /// This family is carried for documentation or background inventory only.
    DocumentationBackgroundOnly,
}

/// Ledger row for one transported theorem family and its admission relevance.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TransportedTheoremBoundaryEntry {
    /// Stable theorem-pack inventory key.
    pub key: String,
    /// Classification of how the family participates in shipped assurance.
    pub usage_class: TransportedTheoremUsageClass,
    /// Whether shipped Rust runtime admission consumes this family directly.
    pub consumed_by_rust_runtime_admission: bool,
    /// Whether Lean theorem-pack gate aliases consume this family directly.
    pub consumed_by_lean_runtime_gate: bool,
    /// Explicit assumption marker when the family is runtime-critical but not
    /// yet instantiated in shipped Rust runtime admission.
    pub assumption_boundary: Option<String>,
}

/// Reasons the transported-theorem ledger and runtime profile can be inconsistent.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TransportedTheoremBoundaryValidationError {
    /// Rust runtime admission consumes a theorem family that is not classified as
    /// runtime-critical in the boundary ledger.
    RustAdmissionKeyNotRuntimeCritical(String),
    /// A runtime-critical theorem consumed only by Lean lost its explicit
    /// assumption boundary marker.
    LeanOnlyRuntimeCriticalMissingAssumptionBoundary(String),
    /// A Rust-runtime-consumed theorem family is missing from the runtime
    /// execution profile eligibility set.
    RuntimeProfileMissingRustAdmissionKey(String),
    /// A Rust-runtime-consumed theorem family is present in the runtime profile
    /// but disabled.
    RuntimeProfileDisablesRustAdmissionKey(String),
    /// The runtime profile enables a theorem family that is not classified as a
    /// Rust-runtime-consumed theorem boundary entry.
    RuntimeProfileEnablesUnknownRustAdmissionKey(String),
}

/// Determinism artifact inventory used for runtime profile validation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DeterminismArtifacts {
    /// Full determinism support.
    pub full: bool,
    /// Determinism modulo effect traces support.
    pub modulo_effect_trace: bool,
    /// Determinism modulo commutativity support.
    pub modulo_commutativity: bool,
    /// Replay determinism support.
    pub replay: bool,
}

impl Default for DeterminismArtifacts {
    fn default() -> Self {
        Self {
            full: true,
            modulo_effect_trace: true,
            modulo_commutativity: true,
            replay: true,
        }
    }
}

/// Runtime capability admitted by theorem-pack/runtime contracts.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum RuntimeCapability {
    /// Live migration/runtime handoff support.
    LiveMigration,
    /// Autoscale repartition support.
    AutoscaleRepartition,
    /// Placement refinement support.
    PlacementRefinement,
    /// Relaxed reordering support.
    RelaxedReordering,
}

/// Fairness assumptions carried by a proof-carrying execution profile.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ProtocolMachineFairnessAssumption {
    /// Scheduler steps commute to the same semantic result.
    ScheduleConfluence,
    /// Live work is eventually scheduled.
    StarvationFreedom,
    /// Liveness-sensitive obligations receive fair scheduling treatment.
    LivenessFairness,
}

/// Admissibility classes carried by a proof-carrying execution profile.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ProtocolMachineAdmissibilityClass {
    /// Local protocol-machine envelope assumptions are admitted.
    LocalEnvelope,
    /// Sharded/distributed envelope assumptions are admitted.
    ShardedEnvelope,
    /// Protocol-envelope bridge assumptions are admitted.
    ProtocolEnvelopeBridge,
}

/// Escalation-window classes carried by a proof-carrying execution profile.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ProtocolMachineEscalationWindowClass {
    /// Progress contracts carry bounded escalation windows.
    ProgressContract,
    /// Admission complexity remains within the bounded proof envelope.
    AdmissionComplexity,
    /// Protocol-envelope bridge escalation windows are bounded.
    ProtocolBridge,
}

/// Proof-carrying execution profile aligned with the Lean theorem-pack layer.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProtocolMachineExecutionProfile {
    /// Fairness assumptions carried by the profile.
    pub fairness_assumptions: BTreeSet<ProtocolMachineFairnessAssumption>,
    /// Admissibility classes carried by the profile.
    pub admissibility_classes: BTreeSet<ProtocolMachineAdmissibilityClass>,
    /// Escalation-window classes carried by the profile.
    pub escalation_window_classes: BTreeSet<ProtocolMachineEscalationWindowClass>,
    /// Boolean theorem-pack eligibility inventory.
    pub theorem_pack_eligibility: Vec<(String, bool)>,
}

impl ProtocolMachineExecutionProfile {
    /// Full profile covering all currently modeled assumptions/classes.
    #[must_use]
    pub fn full() -> Self {
        Self {
            fairness_assumptions: [
                ProtocolMachineFairnessAssumption::ScheduleConfluence,
                ProtocolMachineFairnessAssumption::StarvationFreedom,
                ProtocolMachineFairnessAssumption::LivenessFairness,
            ]
            .into_iter()
            .collect(),
            admissibility_classes: [
                ProtocolMachineAdmissibilityClass::LocalEnvelope,
                ProtocolMachineAdmissibilityClass::ShardedEnvelope,
                ProtocolMachineAdmissibilityClass::ProtocolEnvelopeBridge,
            ]
            .into_iter()
            .collect(),
            escalation_window_classes: [
                ProtocolMachineEscalationWindowClass::ProgressContract,
                ProtocolMachineEscalationWindowClass::AdmissionComplexity,
                ProtocolMachineEscalationWindowClass::ProtocolBridge,
            ]
            .into_iter()
            .collect(),
            theorem_pack_eligibility: vec![
                ("protocol_machine_envelope_adherence".to_string(), true),
                ("protocol_machine_envelope_admission".to_string(), true),
                ("protocol_envelope_bridge".to_string(), true),
            ],
        }
    }

    fn eligibility(&self, key: &str) -> bool {
        self.theorem_pack_eligibility
            .iter()
            .find(|entry| entry.0 == key)
            .map(|entry| entry.1)
            .unwrap_or(false)
    }

    /// Whether this profile supports protocol-machine envelope adherence.
    #[must_use]
    pub fn supports_protocol_machine_envelope_adherence(&self) -> bool {
        self.eligibility("protocol_machine_envelope_adherence")
    }

    /// Whether this profile supports protocol-machine envelope admission.
    #[must_use]
    pub fn supports_protocol_machine_envelope_admission(&self) -> bool {
        self.eligibility("protocol_machine_envelope_admission")
    }

    /// Whether this profile supports the protocol-envelope bridge.
    #[must_use]
    pub fn supports_protocol_envelope_bridge(&self) -> bool {
        self.eligibility("protocol_envelope_bridge")
    }
}

/// Canonical transported-theorem boundary ledger for admission and guarantee surfaces.
#[must_use]
pub fn transported_theorem_boundary() -> Vec<TransportedTheoremBoundaryEntry> {
    let mut boundary = black_box_transported_theorem_entries();
    boundary.extend(runtime_critical_transported_theorem_entries());
    boundary.extend(documentation_background_transported_theorem_entries());
    boundary
}

fn boundary_entry(
    key: &str,
    usage_class: TransportedTheoremUsageClass,
    consumed_by_rust_runtime_admission: bool,
    consumed_by_lean_runtime_gate: bool,
    assumption_boundary: Option<&str>,
) -> TransportedTheoremBoundaryEntry {
    TransportedTheoremBoundaryEntry {
        key: key.to_string(),
        usage_class,
        consumed_by_rust_runtime_admission,
        consumed_by_lean_runtime_gate,
        assumption_boundary: assumption_boundary.map(str::to_string),
    }
}

fn black_box_transported_theorem_entries() -> Vec<TransportedTheoremBoundaryEntry> {
    use TransportedTheoremUsageClass::BlackBoxPremiseOnly;

    [
        "termination",
        "output_condition_soundness",
        "flp_lower_bound",
        "flp_impossibility",
        "cap_impossibility",
        "quorum_geometry_safety",
        "partial_synchrony_liveness",
        "responsiveness",
        "nakamoto_security",
        "reconfiguration_safety",
        "atomic_broadcast_ordering",
        "accountable_safety",
        "failure_detector_boundaries",
        "data_availability_retrievability",
        "coordination_characterization",
        "crdt_envelope_and_equivalence",
        "consensus_envelope",
        "failure_envelope",
        "effect_interface_bridge",
    ]
    .into_iter()
    .map(|key| boundary_entry(key, BlackBoxPremiseOnly, false, false, None))
    .collect()
}

fn runtime_critical_transported_theorem_entries() -> Vec<TransportedTheoremBoundaryEntry> {
    use TransportedTheoremUsageClass::RuntimeCriticalInstantiatedPremise;

    vec![
        boundary_entry(
            "byzantine_safety_characterization",
            RuntimeCriticalInstantiatedPremise,
            false,
            true,
            Some(
                "Lean theorem-pack gate only; Rust runtime admission does not currently consume this key.",
            ),
        ),
        boundary_entry(
            "protocol_machine_envelope_adherence",
            RuntimeCriticalInstantiatedPremise,
            true,
            true,
            None,
        ),
        boundary_entry(
            "protocol_machine_envelope_admission",
            RuntimeCriticalInstantiatedPremise,
            true,
            true,
            None,
        ),
        boundary_entry(
            "protocol_envelope_bridge",
            RuntimeCriticalInstantiatedPremise,
            true,
            true,
            None,
        ),
    ]
}

fn documentation_background_transported_theorem_entries() -> Vec<TransportedTheoremBoundaryEntry> {
    use TransportedTheoremUsageClass::DocumentationBackgroundOnly;

    [
        "classical_foster",
        "classical_maxweight",
        "classical_ldp",
        "classical_mean_field",
        "classical_heavy_traffic",
        "classical_mixing",
        "classical_fluid",
        "classical_concentration",
        "classical_littles_law",
        "classical_functional_clt",
    ]
    .into_iter()
    .map(|key| boundary_entry(key, DocumentationBackgroundOnly, false, false, None))
    .collect()
}

/// Runtime-critical transported theorem families.
#[must_use]
pub fn runtime_critical_transported_theorem_boundary() -> Vec<TransportedTheoremBoundaryEntry> {
    transported_theorem_boundary()
        .into_iter()
        .filter(|entry| {
            matches!(
                entry.usage_class,
                TransportedTheoremUsageClass::RuntimeCriticalInstantiatedPremise
            )
        })
        .collect()
}

/// Transported-theorem keys consumed by shipped Rust runtime admission.
#[must_use]
pub fn rust_runtime_critical_transport_theorem_keys() -> Vec<String> {
    runtime_critical_transported_theorem_boundary()
        .into_iter()
        .filter(|entry| entry.consumed_by_rust_runtime_admission)
        .map(|entry| entry.key)
        .collect()
}

/// Validate that the canonical transported-theorem ledger and shipped runtime
/// execution-profile keys stay in exact correspondence.
///
/// # Errors
///
/// Returns an error when the transported-theorem ledger and runtime profile
/// disagree about which theorem-pack keys are runtime-critical, enabled, or
/// guarded by an explicit assumption boundary.
pub fn validate_transported_theorem_boundary_consistency(
    boundary: &[TransportedTheoremBoundaryEntry],
    profile: &ProtocolMachineExecutionProfile,
) -> Result<(), TransportedTheoremBoundaryValidationError> {
    use TransportedTheoremBoundaryValidationError::{
        LeanOnlyRuntimeCriticalMissingAssumptionBoundary, RuntimeProfileDisablesRustAdmissionKey,
        RuntimeProfileEnablesUnknownRustAdmissionKey, RuntimeProfileMissingRustAdmissionKey,
        RustAdmissionKeyNotRuntimeCritical,
    };
    use TransportedTheoremUsageClass::RuntimeCriticalInstantiatedPremise;

    let rust_runtime_keys: BTreeSet<_> = boundary
        .iter()
        .filter(|entry| entry.consumed_by_rust_runtime_admission)
        .map(|entry| entry.key.as_str())
        .collect();
    let enabled_profile_keys: BTreeSet<_> = profile
        .theorem_pack_eligibility
        .iter()
        .filter_map(|(key, enabled)| enabled.then_some(key.as_str()))
        .collect();

    for entry in boundary {
        if entry.consumed_by_rust_runtime_admission
            && !matches!(entry.usage_class, RuntimeCriticalInstantiatedPremise)
        {
            return Err(RustAdmissionKeyNotRuntimeCritical(entry.key.clone()));
        }
        if matches!(entry.usage_class, RuntimeCriticalInstantiatedPremise)
            && !entry.consumed_by_rust_runtime_admission
            && entry.consumed_by_lean_runtime_gate
            && entry.assumption_boundary.is_none()
        {
            return Err(LeanOnlyRuntimeCriticalMissingAssumptionBoundary(
                entry.key.clone(),
            ));
        }
        if entry.consumed_by_rust_runtime_admission {
            match profile
                .theorem_pack_eligibility
                .iter()
                .find(|(key, _)| key == &entry.key)
            {
                None => return Err(RuntimeProfileMissingRustAdmissionKey(entry.key.clone())),
                Some((_, false)) => {
                    return Err(RuntimeProfileDisablesRustAdmissionKey(entry.key.clone()))
                }
                Some((_, true)) => {}
            }
        }
    }

    for key in enabled_profile_keys {
        if !rust_runtime_keys.contains(key) {
            return Err(RuntimeProfileEnablesUnknownRustAdmissionKey(
                key.to_string(),
            ));
        }
    }

    Ok(())
}

impl RuntimeCapability {
    const ALL: [Self; 4] = [
        Self::LiveMigration,
        Self::AutoscaleRepartition,
        Self::PlacementRefinement,
        Self::RelaxedReordering,
    ];

    const fn key(self) -> &'static str {
        match self {
            Self::LiveMigration => "live_migration",
            Self::AutoscaleRepartition => "autoscale_repartition",
            Self::PlacementRefinement => "placement_refinement",
            Self::RelaxedReordering => "relaxed_reordering",
        }
    }
}

/// Runtime contracts used for advanced-mode admission and capability gates.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RuntimeContracts {
    /// Determinism profile support artifacts.
    pub determinism_artifacts: DeterminismArtifacts,
    /// Whether mixed (non-full) determinism profiles are theorem-pack admitted.
    pub can_use_mixed_determinism_profiles: bool,
    /// Canonical capability set admitted by theorem-pack/runtime state.
    pub capabilities: BTreeSet<RuntimeCapability>,
    /// Proof-carrying execution profile aligned with Lean theorem-pack metadata.
    pub execution_profile: ProtocolMachineExecutionProfile,
}

impl RuntimeContracts {
    /// Contract payload enabling all currently supported advanced runtime switches.
    #[must_use]
    pub fn full() -> Self {
        Self {
            determinism_artifacts: DeterminismArtifacts::default(),
            can_use_mixed_determinism_profiles: true,
            capabilities: RuntimeCapability::ALL.into_iter().collect(),
            execution_profile: ProtocolMachineExecutionProfile::full(),
        }
    }
}

/// Build the canonical runtime execution profile for one config/contract pair.
#[must_use]
pub fn runtime_execution_profile(
    cfg: &ProtocolMachineConfig,
    contracts: Option<&RuntimeContracts>,
) -> ProtocolMachineExecutionProfile {
    let mut profile = ProtocolMachineExecutionProfile {
        fairness_assumptions: [ProtocolMachineFairnessAssumption::ScheduleConfluence]
            .into_iter()
            .collect(),
        admissibility_classes: [
            ProtocolMachineAdmissibilityClass::LocalEnvelope,
            ProtocolMachineAdmissibilityClass::ShardedEnvelope,
        ]
        .into_iter()
        .collect(),
        escalation_window_classes: [ProtocolMachineEscalationWindowClass::ProgressContract]
            .into_iter()
            .collect(),
        theorem_pack_eligibility: vec![
            ("protocol_machine_envelope_adherence".to_string(), true),
            (
                "protocol_machine_envelope_admission".to_string(),
                contracts.is_some(),
            ),
            (
                "protocol_envelope_bridge".to_string(),
                !matches!(cfg.output_condition_policy, OutputConditionPolicy::Disabled),
            ),
        ],
    };

    if !matches!(cfg.sched_policy, SchedPolicy::Cooperative) {
        profile
            .fairness_assumptions
            .insert(ProtocolMachineFairnessAssumption::StarvationFreedom);
    }
    if matches!(cfg.sched_policy, SchedPolicy::ProgressAware)
        || !matches!(cfg.output_condition_policy, OutputConditionPolicy::Disabled)
    {
        profile
            .fairness_assumptions
            .insert(ProtocolMachineFairnessAssumption::LivenessFairness);
    }
    if contracts.is_some() {
        profile
            .escalation_window_classes
            .insert(ProtocolMachineEscalationWindowClass::AdmissionComplexity);
    }
    if !matches!(cfg.output_condition_policy, OutputConditionPolicy::Disabled) {
        profile
            .admissibility_classes
            .insert(ProtocolMachineAdmissibilityClass::ProtocolEnvelopeBridge);
        profile
            .escalation_window_classes
            .insert(ProtocolMachineEscalationWindowClass::ProtocolBridge);
    }

    profile
}

/// Whether one proof-carrying execution profile supports the requested runtime config.
#[must_use]
pub fn execution_profile_supported(
    profile: &ProtocolMachineExecutionProfile,
    cfg: &ProtocolMachineConfig,
    contracts: Option<&RuntimeContracts>,
) -> bool {
    let required = runtime_execution_profile(cfg, contracts);
    let supports_adherence = required.supports_protocol_machine_envelope_adherence();
    let supports_admission = required.supports_protocol_machine_envelope_admission();
    let supports_bridge = required.supports_protocol_envelope_bridge();
    required
        .fairness_assumptions
        .into_iter()
        .all(|assumption| profile.fairness_assumptions.contains(&assumption))
        && required
            .admissibility_classes
            .into_iter()
            .all(|class| profile.admissibility_classes.contains(&class))
        && required
            .escalation_window_classes
            .into_iter()
            .all(|class| profile.escalation_window_classes.contains(&class))
        && (!supports_adherence || profile.supports_protocol_machine_envelope_adherence())
        && (!supports_admission || profile.supports_protocol_machine_envelope_admission())
        && (!supports_bridge || profile.supports_protocol_envelope_bridge())
}

fn sched_policy_requires_contracts(policy: &SchedPolicy) -> bool {
    !matches!(policy, SchedPolicy::Cooperative)
}

/// Whether protocol-machine config requires runtime contracts for admission.
#[must_use]
pub fn requires_protocol_machine_runtime_contracts(cfg: &ProtocolMachineConfig) -> bool {
    sched_policy_requires_contracts(&cfg.sched_policy) || cfg.speculation_enabled
}

/// Protocol-machine admission gate for advanced runtime modes.
#[must_use]
pub fn admit_protocol_machine_runtime(
    cfg: &ProtocolMachineConfig,
    contracts: Option<&RuntimeContracts>,
) -> RuntimeAdmissionResult {
    if requires_protocol_machine_runtime_contracts(cfg) && contracts.is_none() {
        RuntimeAdmissionResult::RejectedMissingContracts
    } else {
        RuntimeAdmissionResult::Admitted
    }
}

/// Check artifact support for one determinism profile.
#[must_use]
pub fn determinism_profile_supported(
    artifacts: &DeterminismArtifacts,
    profile: DeterminismMode,
) -> bool {
    match profile {
        DeterminismMode::Full => artifacts.full,
        DeterminismMode::ModuloEffects => artifacts.modulo_effect_trace,
        DeterminismMode::ModuloCommutativity => artifacts.modulo_commutativity,
        DeterminismMode::Replay => artifacts.replay,
    }
}

/// Runtime profile selection gate with mixed-profile capability checks.
#[must_use]
pub fn request_determinism_profile(
    contracts: &RuntimeContracts,
    profile: DeterminismMode,
) -> Option<DeterminismMode> {
    let supported = determinism_profile_supported(&contracts.determinism_artifacts, profile);
    if !supported {
        return None;
    }
    match profile {
        DeterminismMode::Full => Some(profile),
        DeterminismMode::ModuloEffects
        | DeterminismMode::ModuloCommutativity
        | DeterminismMode::Replay => contracts
            .can_use_mixed_determinism_profiles
            .then_some(profile),
    }
}

/// Unified runtime gate check for advanced-mode admission and profile support.
#[must_use]
pub fn enforce_protocol_machine_runtime_gates(
    cfg: &ProtocolMachineConfig,
    contracts: Option<&RuntimeContracts>,
) -> RuntimeGateResult {
    match admit_protocol_machine_runtime(cfg, contracts) {
        RuntimeAdmissionResult::RejectedMissingContracts => {
            RuntimeGateResult::RejectedMissingContracts
        }
        RuntimeAdmissionResult::Admitted => match contracts {
            Some(contracts) => {
                if request_determinism_profile(contracts, cfg.determinism_mode).is_some() {
                    RuntimeGateResult::Admitted
                } else {
                    RuntimeGateResult::RejectedUnsupportedDeterminismProfile
                }
            }
            None => {
                if matches!(cfg.determinism_mode, DeterminismMode::Full) {
                    RuntimeGateResult::Admitted
                } else {
                    RuntimeGateResult::RejectedUnsupportedDeterminismProfile
                }
            }
        },
    }
}

/// Runtime capability snapshot emitted at startup.
#[must_use]
pub fn runtime_capability_snapshot(contracts: &RuntimeContracts) -> Vec<(String, bool)> {
    RuntimeCapability::ALL
        .into_iter()
        .map(|capability| {
            (
                capability.key().to_string(),
                contracts.capabilities.contains(&capability),
            )
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn admission_requires_contracts_for_advanced_modes() {
        let mut cfg = ProtocolMachineConfig::default();
        assert_eq!(
            admit_protocol_machine_runtime(&cfg, None),
            RuntimeAdmissionResult::Admitted
        );

        cfg.speculation_enabled = true;
        assert_eq!(
            admit_protocol_machine_runtime(&cfg, None),
            RuntimeAdmissionResult::RejectedMissingContracts
        );
        assert_eq!(
            admit_protocol_machine_runtime(&cfg, Some(&RuntimeContracts::full())),
            RuntimeAdmissionResult::Admitted
        );
    }

    #[test]
    fn request_determinism_profile_obeys_artifacts_and_mixed_gate() {
        let mut contracts = RuntimeContracts::full();
        contracts.can_use_mixed_determinism_profiles = false;
        assert_eq!(
            request_determinism_profile(&contracts, DeterminismMode::Full),
            Some(DeterminismMode::Full)
        );
        assert_eq!(
            request_determinism_profile(&contracts, DeterminismMode::Replay),
            None
        );

        contracts.can_use_mixed_determinism_profiles = true;
        contracts.determinism_artifacts.replay = false;
        assert_eq!(
            request_determinism_profile(&contracts, DeterminismMode::Replay),
            None
        );
        contracts.determinism_artifacts.replay = true;
        assert_eq!(
            request_determinism_profile(&contracts, DeterminismMode::Replay),
            Some(DeterminismMode::Replay)
        );
    }

    #[test]
    #[allow(clippy::field_reassign_with_default)]
    fn unified_runtime_gate_combines_admission_and_profile_checks() {
        let mut cfg = ProtocolMachineConfig::default();
        cfg.speculation_enabled = true;
        assert_eq!(
            enforce_protocol_machine_runtime_gates(&cfg, None),
            RuntimeGateResult::RejectedMissingContracts
        );

        let mut contracts = RuntimeContracts::full();
        contracts.determinism_artifacts.replay = false;
        cfg.determinism_mode = DeterminismMode::Replay;
        assert_eq!(
            enforce_protocol_machine_runtime_gates(&cfg, Some(&contracts)),
            RuntimeGateResult::RejectedUnsupportedDeterminismProfile
        );

        contracts.determinism_artifacts.replay = true;
        assert_eq!(
            enforce_protocol_machine_runtime_gates(&cfg, Some(&contracts)),
            RuntimeGateResult::Admitted
        );
    }

    #[test]
    fn capability_snapshot_is_derived_from_canonical_capability_set() {
        let mut contracts = RuntimeContracts::full();
        contracts
            .capabilities
            .remove(&RuntimeCapability::RelaxedReordering);

        let snapshot = runtime_capability_snapshot(&contracts);
        assert_eq!(
            snapshot,
            vec![
                ("live_migration".to_string(), true),
                ("autoscale_repartition".to_string(), true),
                ("placement_refinement".to_string(), true),
                ("relaxed_reordering".to_string(), false),
            ]
        );
    }

    #[test]
    #[allow(clippy::field_reassign_with_default)]
    fn runtime_execution_profile_tracks_scheduler_and_bridge_requirements() {
        let mut cfg = ProtocolMachineConfig::default();
        cfg.sched_policy = SchedPolicy::ProgressAware;
        cfg.output_condition_policy = OutputConditionPolicy::AllowAll;

        let profile = runtime_execution_profile(&cfg, Some(&RuntimeContracts::full()));
        assert!(profile
            .fairness_assumptions
            .contains(&ProtocolMachineFairnessAssumption::LivenessFairness));
        assert!(profile
            .admissibility_classes
            .contains(&ProtocolMachineAdmissibilityClass::ProtocolEnvelopeBridge));
        assert!(profile.supports_protocol_envelope_bridge());
        assert!(execution_profile_supported(
            &ProtocolMachineExecutionProfile::full(),
            &cfg,
            Some(&RuntimeContracts::full())
        ));
    }

    #[test]
    fn transported_theorem_boundary_makes_rust_runtime_subset_exact() {
        let boundary = transported_theorem_boundary();
        let rust_runtime_keys = rust_runtime_critical_transport_theorem_keys();
        let profile = ProtocolMachineExecutionProfile::full();
        let profile_keys: Vec<_> = profile
            .theorem_pack_eligibility
            .iter()
            .map(|(key, _)| key.clone())
            .collect();

        assert_eq!(
            rust_runtime_keys, profile_keys,
            "shipped Rust runtime admission must consume exactly the classified runtime-critical theorem keys"
        );
        assert_eq!(
            validate_transported_theorem_boundary_consistency(&boundary, &profile),
            Ok(())
        );
        assert!(
            boundary.iter().any(|entry| {
                entry.key == "byzantine_safety_characterization"
                    && matches!(
                        entry.usage_class,
                        TransportedTheoremUsageClass::RuntimeCriticalInstantiatedPremise
                    )
                    && !entry.consumed_by_rust_runtime_admission
                    && entry.consumed_by_lean_runtime_gate
            }),
            "Lean-only runtime-critical theorem gates must remain explicit in the boundary ledger"
        );
    }

    #[test]
    fn transported_theorem_boundary_requires_instantiation_or_assumption_boundary() {
        for entry in runtime_critical_transported_theorem_boundary() {
            assert!(
                entry.consumed_by_rust_runtime_admission || entry.assumption_boundary.is_some(),
                "runtime-critical theorem {} must have a Rust instantiation path or an explicit assumption boundary",
                entry.key
            );
        }
    }

    #[test]
    fn transported_theorem_boundary_fail_closes_when_runtime_profile_key_drifts() {
        let boundary = transported_theorem_boundary();
        let mut profile = ProtocolMachineExecutionProfile::full();
        profile.theorem_pack_eligibility[0].0 = "protocol_machine_envelope_adherence_typo".into();

        assert_eq!(
            validate_transported_theorem_boundary_consistency(&boundary, &profile),
            Err(
                TransportedTheoremBoundaryValidationError::RuntimeProfileMissingRustAdmissionKey(
                    "protocol_machine_envelope_adherence".into()
                )
            )
        );
    }

    #[test]
    fn transported_theorem_boundary_fail_closes_when_runtime_profile_enables_unknown_key() {
        let boundary = transported_theorem_boundary();
        let mut profile = ProtocolMachineExecutionProfile::full();
        profile
            .theorem_pack_eligibility
            .push(("unknown_runtime_boundary".into(), true));

        assert_eq!(
            validate_transported_theorem_boundary_consistency(&boundary, &profile),
            Err(
                TransportedTheoremBoundaryValidationError::RuntimeProfileEnablesUnknownRustAdmissionKey(
                    "unknown_runtime_boundary".into()
                )
            )
        );
    }

    #[test]
    fn transported_theorem_boundary_fail_closes_when_runtime_classification_drifts() {
        let mut boundary = transported_theorem_boundary();
        let profile = ProtocolMachineExecutionProfile::full();
        let bridge_entry = boundary
            .iter_mut()
            .find(|entry| entry.key == "protocol_envelope_bridge")
            .expect("canonical boundary should classify protocol_envelope_bridge");
        bridge_entry.usage_class = TransportedTheoremUsageClass::BlackBoxPremiseOnly;

        assert_eq!(
            validate_transported_theorem_boundary_consistency(&boundary, &profile),
            Err(
                TransportedTheoremBoundaryValidationError::RustAdmissionKeyNotRuntimeCritical(
                    "protocol_envelope_bridge".into()
                )
            )
        );
    }

    #[test]
    fn transported_theorem_boundary_fail_closes_when_lean_only_runtime_critical_entry_loses_assumption_boundary(
    ) {
        let mut boundary = transported_theorem_boundary();
        let profile = ProtocolMachineExecutionProfile::full();
        let byzantine = boundary
            .iter_mut()
            .find(|entry| entry.key == "byzantine_safety_characterization")
            .expect("canonical boundary should classify byzantine_safety_characterization");
        byzantine.assumption_boundary = None;

        assert_eq!(
            validate_transported_theorem_boundary_consistency(&boundary, &profile),
            Err(
                TransportedTheoremBoundaryValidationError::LeanOnlyRuntimeCriticalMissingAssumptionBoundary(
                    "byzantine_safety_characterization".into()
                )
            )
        );
    }
}
