//! Typed invariant-claims schema for proof-oriented protocol bundles.

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};
use serde_json::Value;
use telltale_types::{GlobalType, LocalTypeR};

use crate::export::{global_to_json, local_to_json};

/// Schema version for protocol-bundle payloads.
pub const PROTOCOL_BUNDLE_SCHEMA_VERSION: &str = "protocol_bundle.v1";

#[must_use]
pub fn default_protocol_bundle_schema_version() -> String {
    PROTOCOL_BUNDLE_SCHEMA_VERSION.to_string()
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub enum SchedulerKind {
    #[default]
    Cooperative,
    RoundRobin,
    Priority,
    ProgressAware,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub enum FaultModel {
    #[default]
    Crash,
    Byzantine,
    Hybrid,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub enum TimingModel {
    #[default]
    Asynchronous,
    PartialSynchrony,
    Synchronous,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub enum ConsistencyLevel {
    #[default]
    Linearizable,
    Sequential,
    Eventual,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub enum AvailabilityLevel {
    #[default]
    Total,
    BoundedDegradation,
    BestEffort,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub enum PartitionModel {
    #[default]
    None,
    CrashOnly,
    NetworkSplit,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub enum QuorumSystemKind {
    #[default]
    Majority,
    Weighted,
    Flexible,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct LivenessConfig {
    pub scheduler: SchedulerKind,
    pub fairness_k: Option<usize>,
    pub progress_required: bool,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct FLPConfig {
    pub crash_bound: usize,
    pub requires_determinism: bool,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct CAPConfig {
    pub consistency: ConsistencyLevel,
    pub availability: AvailabilityLevel,
    pub partition_model: PartitionModel,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct QuorumGeometryConfig {
    pub quorum_system: QuorumSystemKind,
    pub n: usize,
    pub quorum_size: usize,
    pub intersection_size: usize,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct PartialSynchronyConfig {
    pub timing: TimingModel,
    pub delta_bound: Option<usize>,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct ResponsivenessConfig {
    pub leader_based: bool,
    pub requires_stable_period: bool,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct NakamotoConfig {
    pub honest_fraction: f64,
    pub finality_depth: usize,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct ReconfigurationConfig {
    pub dynamic_membership: bool,
    pub overlap_required: bool,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct AtomicBroadcastConfig {
    pub total_order: bool,
    pub valid_delivery: bool,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct DistributedClaims {
    #[serde(default)]
    pub fault_model: FaultModel,
    pub flp: Option<FLPConfig>,
    pub cap: Option<CAPConfig>,
    pub quorum_geometry: Option<QuorumGeometryConfig>,
    pub partial_synchrony: Option<PartialSynchronyConfig>,
    pub responsiveness: Option<ResponsivenessConfig>,
    pub nakamoto: Option<NakamotoConfig>,
    pub reconfiguration: Option<ReconfigurationConfig>,
    pub atomic_broadcast: Option<AtomicBroadcastConfig>,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct FosterConfig {
    pub enabled: bool,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct MaxWeightConfig {
    pub enabled: bool,
    pub slack: Option<f64>,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct LDPConfig {
    pub enabled: bool,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct MeanFieldConfig {
    pub enabled: bool,
    pub population_size: Option<usize>,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct HeavyTrafficConfig {
    pub enabled: bool,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct MixingConfig {
    pub enabled: bool,
    pub mixing_time_bound: Option<usize>,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct FluidConfig {
    pub enabled: bool,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct ConcentrationConfig {
    pub enabled: bool,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct LittlesLawConfig {
    pub enabled: bool,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct FunctionalCLTConfig {
    pub enabled: bool,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct ClassicalClaims {
    pub foster: Option<FosterConfig>,
    pub max_weight: Option<MaxWeightConfig>,
    pub ldp: Option<LDPConfig>,
    pub mean_field: Option<MeanFieldConfig>,
    pub heavy_traffic: Option<HeavyTrafficConfig>,
    pub mixing: Option<MixingConfig>,
    pub fluid: Option<FluidConfig>,
    pub concentration: Option<ConcentrationConfig>,
    pub littles_law: Option<LittlesLawConfig>,
    pub functional_clt: Option<FunctionalCLTConfig>,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct InvariantClaims {
    #[serde(default = "crate::schema::default_schema_version")]
    pub schema_version: String,
    pub liveness: Option<LivenessConfig>,
    #[serde(default)]
    pub distributed: DistributedClaims,
    #[serde(default)]
    pub classical: ClassicalClaims,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ProtocolBundle {
    #[serde(default = "default_protocol_bundle_schema_version")]
    pub schema_version: String,
    pub global_type: Value,
    pub local_types: BTreeMap<String, Value>,
    pub claims: InvariantClaims,
}

/// Export a typed protocol bundle for Lean-side verification entrypoints.
#[must_use]
pub fn export_protocol_bundle(
    global: &GlobalType,
    local_types: &BTreeMap<String, LocalTypeR>,
    claims: InvariantClaims,
) -> ProtocolBundle {
    let local_types = local_types
        .iter()
        .map(|(role, local)| (role.clone(), local_to_json(local)))
        .collect();

    ProtocolBundle {
        schema_version: default_protocol_bundle_schema_version(),
        global_type: global_to_json(global),
        local_types,
        claims,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use telltale_types::{GlobalType, Label};

    #[test]
    fn test_export_protocol_bundle_includes_schema_and_claims() {
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let mut locals = BTreeMap::new();
        locals.insert(
            "A".to_string(),
            LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End),
        );
        locals.insert(
            "B".to_string(),
            LocalTypeR::recv("A", Label::new("msg"), LocalTypeR::End),
        );

        let claims = InvariantClaims {
            schema_version: crate::schema::default_schema_version(),
            liveness: Some(LivenessConfig {
                scheduler: SchedulerKind::RoundRobin,
                fairness_k: Some(2),
                progress_required: true,
            }),
            distributed: DistributedClaims {
                flp: Some(FLPConfig {
                    crash_bound: 1,
                    requires_determinism: true,
                }),
                ..DistributedClaims::default()
            },
            classical: ClassicalClaims {
                foster: Some(FosterConfig { enabled: true }),
                ..ClassicalClaims::default()
            },
        };

        let bundle = export_protocol_bundle(&global, &locals, claims);
        assert_eq!(bundle.schema_version, PROTOCOL_BUNDLE_SCHEMA_VERSION);
        assert_eq!(
            bundle.claims.schema_version,
            crate::schema::LEAN_BRIDGE_SCHEMA_VERSION
        );
        assert!(bundle.local_types.contains_key("A"));
        assert!(bundle.local_types.contains_key("B"));
    }
}
