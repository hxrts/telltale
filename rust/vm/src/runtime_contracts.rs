//! Runtime admission and profile-gate contracts aligned with Lean surfaces.

use serde::{Deserialize, Serialize};

use crate::determinism::DeterminismMode;
use crate::scheduler::SchedPolicy;
use crate::vm::VMConfig;

/// VM admission result for advanced runtime mode checks.
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

/// Runtime contracts used for advanced-mode admission and capability gates.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RuntimeContracts {
    /// Determinism profile support artifacts.
    pub determinism_artifacts: DeterminismArtifacts,
    /// Whether mixed (non-full) determinism profiles are theorem-pack admitted.
    pub can_use_mixed_determinism_profiles: bool,
    /// Capability-gated runtime switches mirrored from theorem-pack API.
    pub live_migration: bool,
    /// Capability-gated runtime switches mirrored from theorem-pack API.
    pub autoscale_repartition: bool,
    /// Capability-gated runtime switches mirrored from theorem-pack API.
    pub placement_refinement: bool,
    /// Capability-gated runtime switches mirrored from theorem-pack API.
    pub relaxed_reordering: bool,
    /// Deterministic capability inventory emitted at startup.
    pub capability_inventory: Vec<(String, bool)>,
}

impl RuntimeContracts {
    /// Contract payload enabling all currently supported advanced runtime switches.
    #[must_use]
    pub fn full() -> Self {
        Self {
            determinism_artifacts: DeterminismArtifacts::default(),
            can_use_mixed_determinism_profiles: true,
            live_migration: true,
            autoscale_repartition: true,
            placement_refinement: true,
            relaxed_reordering: true,
            capability_inventory: vec![
                ("live_migration".to_string(), true),
                ("autoscale_repartition".to_string(), true),
                ("placement_refinement".to_string(), true),
                ("relaxed_reordering".to_string(), true),
            ],
        }
    }
}

fn sched_policy_requires_contracts(policy: &SchedPolicy) -> bool {
    !matches!(policy, SchedPolicy::Cooperative)
}

/// Whether VM config requires runtime contracts for admission.
#[must_use]
pub fn requires_vm_runtime_contracts(cfg: &VMConfig) -> bool {
    sched_policy_requires_contracts(&cfg.sched_policy) || cfg.speculation_enabled
}

/// VM admission gate for advanced runtime modes.
#[must_use]
pub fn admit_vm_runtime(
    cfg: &VMConfig,
    contracts: Option<&RuntimeContracts>,
) -> RuntimeAdmissionResult {
    if requires_vm_runtime_contracts(cfg) && contracts.is_none() {
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
pub fn enforce_vm_runtime_gates(
    cfg: &VMConfig,
    contracts: Option<&RuntimeContracts>,
) -> RuntimeGateResult {
    match admit_vm_runtime(cfg, contracts) {
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
    let mut snapshot = contracts.capability_inventory.clone();
    snapshot.push(("live_migration".to_string(), contracts.live_migration));
    snapshot.push((
        "autoscale_repartition".to_string(),
        contracts.autoscale_repartition,
    ));
    snapshot.push((
        "placement_refinement".to_string(),
        contracts.placement_refinement,
    ));
    snapshot.push((
        "relaxed_reordering".to_string(),
        contracts.relaxed_reordering,
    ));
    snapshot
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn admission_requires_contracts_for_advanced_modes() {
        let mut cfg = VMConfig::default();
        assert_eq!(
            admit_vm_runtime(&cfg, None),
            RuntimeAdmissionResult::Admitted
        );

        cfg.speculation_enabled = true;
        assert_eq!(
            admit_vm_runtime(&cfg, None),
            RuntimeAdmissionResult::RejectedMissingContracts
        );
        assert_eq!(
            admit_vm_runtime(&cfg, Some(&RuntimeContracts::full())),
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
        let mut cfg = VMConfig::default();
        cfg.speculation_enabled = true;
        assert_eq!(
            enforce_vm_runtime_gates(&cfg, None),
            RuntimeGateResult::RejectedMissingContracts
        );

        let mut contracts = RuntimeContracts::full();
        contracts.determinism_artifacts.replay = false;
        cfg.determinism_mode = DeterminismMode::Replay;
        assert_eq!(
            enforce_vm_runtime_gates(&cfg, Some(&contracts)),
            RuntimeGateResult::RejectedUnsupportedDeterminismProfile
        );

        contracts.determinism_artifacts.replay = true;
        assert_eq!(
            enforce_vm_runtime_gates(&cfg, Some(&contracts)),
            RuntimeGateResult::Admitted
        );
    }
}
