#![allow(clippy::expect_used)]

use std::collections::BTreeMap;

use proptest::prelude::*;
use telltale_lean_bridge::invariants::AtomicBroadcastConfig;
use telltale_lean_bridge::{
    default_schema_version, export_protocol_bundle, AccountableSafetyConfig, AvailabilityLevel,
    ByzantineSafetyConfig, CAPConfig, CRDTConfig, ClassicalClaims, ConcentrationConfig,
    ConsensusEnvelopeConfig, ConsistencyLevel, CoordinationConfig, DataAvailabilityConfig,
    DistributedClaims, FLPConfig, FailureDetectorsConfig, FailureEnvelopeConfig, FluidConfig,
    FosterConfig, FunctionalCLTConfig, HeavyTrafficConfig, InvariantClaims, LDPConfig,
    LittlesLawConfig, MaxWeightConfig, MeanFieldConfig, MixingConfig, NakamotoConfig,
    PartialSynchronyConfig, PartitionModel, ProtocolBundle, ProtocolEnvelopeBridgeConfig,
    QuorumGeometryConfig, QuorumSystemKind, ReconfigurationConfig, ResponsivenessConfig,
    TimingModel, VMEnvelopeAdherenceConfig, VMEnvelopeAdmissionConfig,
};
use telltale_types::{FixedQ32, GlobalType, Label, LocalTypeR};

fn protocol_fixture() -> (GlobalType, BTreeMap<String, LocalTypeR>) {
    let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
    let mut local_types = BTreeMap::new();
    local_types.insert(
        "A".to_string(),
        LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End),
    );
    local_types.insert(
        "B".to_string(),
        LocalTypeR::recv("A", Label::new("msg"), LocalTypeR::End),
    );
    (global, local_types)
}

fn empty_claims() -> InvariantClaims {
    InvariantClaims {
        schema_version: default_schema_version(),
        liveness: None,
        distributed: DistributedClaims::default(),
        classical: ClassicalClaims::default(),
    }
}

fn roundtrip_claims(claims: InvariantClaims) -> InvariantClaims {
    let (global, local_types) = protocol_fixture();
    let bundle = export_protocol_bundle(&global, &local_types, claims);
    let json = serde_json::to_value(bundle).expect("protocol bundle should serialize");
    let decoded: ProtocolBundle =
        serde_json::from_value(json).expect("protocol bundle should deserialize");
    decoded.claims
}

fn distributed_slot_count(distributed: &DistributedClaims) -> usize {
    usize::from(distributed.flp.is_some())
        + usize::from(distributed.cap.is_some())
        + usize::from(distributed.quorum_geometry.is_some())
        + usize::from(distributed.partial_synchrony.is_some())
        + usize::from(distributed.responsiveness.is_some())
        + usize::from(distributed.nakamoto.is_some())
        + usize::from(distributed.reconfiguration.is_some())
        + usize::from(distributed.atomic_broadcast.is_some())
        + usize::from(distributed.accountable_safety.is_some())
        + usize::from(distributed.failure_detectors.is_some())
        + usize::from(distributed.data_availability.is_some())
        + usize::from(distributed.coordination.is_some())
        + usize::from(distributed.crdt.is_some())
        + usize::from(distributed.byzantine_safety.is_some())
        + usize::from(distributed.consensus_envelope.is_some())
        + usize::from(distributed.failure_envelope.is_some())
        + usize::from(distributed.vm_envelope_adherence.is_some())
        + usize::from(distributed.vm_envelope_admission.is_some())
        + usize::from(distributed.protocol_envelope_bridge.is_some())
}

fn classical_slot_count(classical: &ClassicalClaims) -> usize {
    usize::from(classical.foster.is_some())
        + usize::from(classical.max_weight.is_some())
        + usize::from(classical.ldp.is_some())
        + usize::from(classical.mean_field.is_some())
        + usize::from(classical.heavy_traffic.is_some())
        + usize::from(classical.mixing.is_some())
        + usize::from(classical.fluid.is_some())
        + usize::from(classical.concentration.is_some())
        + usize::from(classical.littles_law.is_some())
        + usize::from(classical.functional_clt.is_some())
}

fn arb_consistency_level() -> impl Strategy<Value = ConsistencyLevel> {
    prop_oneof![
        Just(ConsistencyLevel::Linearizable),
        Just(ConsistencyLevel::Sequential),
        Just(ConsistencyLevel::Eventual),
    ]
}

fn arb_availability_level() -> impl Strategy<Value = AvailabilityLevel> {
    prop_oneof![
        Just(AvailabilityLevel::Total),
        Just(AvailabilityLevel::BoundedDegradation),
        Just(AvailabilityLevel::BestEffort),
    ]
}

fn arb_partition_model() -> impl Strategy<Value = PartitionModel> {
    prop_oneof![
        Just(PartitionModel::None),
        Just(PartitionModel::CrashOnly),
        Just(PartitionModel::NetworkSplit),
    ]
}

fn arb_quorum_system_kind() -> impl Strategy<Value = QuorumSystemKind> {
    prop_oneof![
        Just(QuorumSystemKind::Majority),
        Just(QuorumSystemKind::Weighted),
        Just(QuorumSystemKind::Flexible),
    ]
}

fn arb_timing_model() -> impl Strategy<Value = TimingModel> {
    prop_oneof![
        Just(TimingModel::Asynchronous),
        Just(TimingModel::PartialSynchrony),
        Just(TimingModel::Synchronous),
    ]
}

fn ppm_to_fixed(ppm: u32) -> FixedQ32 {
    FixedQ32::from_ppm(ppm).expect("ppm in [0,1_000_000] should convert")
}

fn assert_single_distributed_slot(claims: &InvariantClaims) {
    assert_eq!(claims.schema_version, default_schema_version());
    assert_eq!(distributed_slot_count(&claims.distributed), 1);
    assert_eq!(classical_slot_count(&claims.classical), 0);
}

fn assert_single_classical_slot(claims: &InvariantClaims) {
    assert_eq!(claims.schema_version, default_schema_version());
    assert_eq!(distributed_slot_count(&claims.distributed), 0);
    assert_eq!(classical_slot_count(&claims.classical), 1);
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(16))]

    #[test]
    fn distributed_flp_roundtrip(crash_bound in 0usize..8, requires_determinism in any::<bool>()) {
        let mut claims = empty_claims();
        claims.distributed.flp = Some(FLPConfig { crash_bound, requires_determinism });
        let decoded = roundtrip_claims(claims);
        assert!(decoded.distributed.flp.is_some());
        assert_single_distributed_slot(&decoded);
    }

    #[test]
    fn distributed_cap_roundtrip(
        consistency in arb_consistency_level(),
        availability in arb_availability_level(),
        partition_model in arb_partition_model(),
    ) {
        let mut claims = empty_claims();
        claims.distributed.cap = Some(CAPConfig { consistency, availability, partition_model });
        let decoded = roundtrip_claims(claims);
        assert!(decoded.distributed.cap.is_some());
        assert_single_distributed_slot(&decoded);
    }

    #[test]
    fn distributed_quorum_geometry_roundtrip(
        quorum_system in arb_quorum_system_kind(),
        n in 1usize..64,
        quorum_size in 1usize..64,
        intersection_size in 0usize..64
    ) {
        let mut claims = empty_claims();
        claims.distributed.quorum_geometry = Some(QuorumGeometryConfig {
            quorum_system,
            n,
            quorum_size,
            intersection_size,
        });
        let decoded = roundtrip_claims(claims);
        assert!(decoded.distributed.quorum_geometry.is_some());
        assert_single_distributed_slot(&decoded);
    }

    #[test]
    fn distributed_partial_synchrony_roundtrip(
        timing in arb_timing_model(),
        delta_bound in prop::option::of(0usize..128),
    ) {
        let mut claims = empty_claims();
        claims.distributed.partial_synchrony = Some(PartialSynchronyConfig { timing, delta_bound });
        let decoded = roundtrip_claims(claims);
        assert!(decoded.distributed.partial_synchrony.is_some());
        assert_single_distributed_slot(&decoded);
    }

    #[test]
    fn distributed_responsiveness_roundtrip(leader_based in any::<bool>(), requires_stable_period in any::<bool>()) {
        let mut claims = empty_claims();
        claims.distributed.responsiveness = Some(ResponsivenessConfig { leader_based, requires_stable_period });
        let decoded = roundtrip_claims(claims);
        assert!(decoded.distributed.responsiveness.is_some());
        assert_single_distributed_slot(&decoded);
    }

    #[test]
    fn distributed_nakamoto_roundtrip(honest_fraction_ppm in 0u32..=1_000_000, finality_depth in 0usize..256) {
        let mut claims = empty_claims();
        claims.distributed.nakamoto = Some(NakamotoConfig {
            honest_fraction: ppm_to_fixed(honest_fraction_ppm),
            finality_depth,
        });
        let decoded = roundtrip_claims(claims);
        assert!(decoded.distributed.nakamoto.is_some());
        assert_single_distributed_slot(&decoded);
    }

    #[test]
    fn distributed_reconfiguration_roundtrip(dynamic_membership in any::<bool>(), overlap_required in any::<bool>()) {
        let mut claims = empty_claims();
        claims.distributed.reconfiguration = Some(ReconfigurationConfig { dynamic_membership, overlap_required });
        let decoded = roundtrip_claims(claims);
        assert!(decoded.distributed.reconfiguration.is_some());
        assert_single_distributed_slot(&decoded);
    }

    #[test]
    fn distributed_atomic_broadcast_roundtrip(total_order in any::<bool>(), valid_delivery in any::<bool>()) {
        let mut claims = empty_claims();
        claims.distributed.atomic_broadcast = Some(AtomicBroadcastConfig { total_order, valid_delivery });
        let decoded = roundtrip_claims(claims);
        assert!(decoded.distributed.atomic_broadcast.is_some());
        assert_single_distributed_slot(&decoded);
    }

    #[test]
    fn distributed_accountable_safety_roundtrip(enabled in any::<bool>()) {
        let mut claims = empty_claims();
        claims.distributed.accountable_safety = Some(AccountableSafetyConfig { enabled });
        let decoded = roundtrip_claims(claims);
        assert!(decoded.distributed.accountable_safety.is_some());
        assert_single_distributed_slot(&decoded);
    }

    #[test]
    fn distributed_failure_detectors_roundtrip(enabled in any::<bool>()) {
        let mut claims = empty_claims();
        claims.distributed.failure_detectors = Some(FailureDetectorsConfig { enabled });
        let decoded = roundtrip_claims(claims);
        assert!(decoded.distributed.failure_detectors.is_some());
        assert_single_distributed_slot(&decoded);
    }

    #[test]
    fn distributed_data_availability_roundtrip(enabled in any::<bool>()) {
        let mut claims = empty_claims();
        claims.distributed.data_availability = Some(DataAvailabilityConfig { enabled });
        let decoded = roundtrip_claims(claims);
        assert!(decoded.distributed.data_availability.is_some());
        assert_single_distributed_slot(&decoded);
    }

    #[test]
    fn distributed_coordination_roundtrip(enabled in any::<bool>()) {
        let mut claims = empty_claims();
        claims.distributed.coordination = Some(CoordinationConfig { enabled });
        let decoded = roundtrip_claims(claims);
        assert!(decoded.distributed.coordination.is_some());
        assert_single_distributed_slot(&decoded);
    }

    #[test]
    fn distributed_crdt_roundtrip(enabled in any::<bool>()) {
        let mut claims = empty_claims();
        claims.distributed.crdt = Some(CRDTConfig { enabled });
        let decoded = roundtrip_claims(claims);
        assert!(decoded.distributed.crdt.is_some());
        assert_single_distributed_slot(&decoded);
    }

    #[test]
    fn distributed_byzantine_safety_roundtrip(enabled in any::<bool>()) {
        let mut claims = empty_claims();
        claims.distributed.byzantine_safety = Some(ByzantineSafetyConfig { enabled });
        let decoded = roundtrip_claims(claims);
        assert!(decoded.distributed.byzantine_safety.is_some());
        assert_single_distributed_slot(&decoded);
    }

    #[test]
    fn distributed_consensus_envelope_roundtrip(enabled in any::<bool>()) {
        let mut claims = empty_claims();
        claims.distributed.consensus_envelope = Some(ConsensusEnvelopeConfig { enabled });
        let decoded = roundtrip_claims(claims);
        assert!(decoded.distributed.consensus_envelope.is_some());
        assert_single_distributed_slot(&decoded);
    }

    #[test]
    fn distributed_failure_envelope_roundtrip(enabled in any::<bool>()) {
        let mut claims = empty_claims();
        claims.distributed.failure_envelope = Some(FailureEnvelopeConfig { enabled });
        let decoded = roundtrip_claims(claims);
        assert!(decoded.distributed.failure_envelope.is_some());
        assert_single_distributed_slot(&decoded);
    }

    #[test]
    fn distributed_vm_envelope_adherence_roundtrip(enabled in any::<bool>()) {
        let mut claims = empty_claims();
        claims.distributed.vm_envelope_adherence = Some(VMEnvelopeAdherenceConfig { enabled });
        let decoded = roundtrip_claims(claims);
        assert!(decoded.distributed.vm_envelope_adherence.is_some());
        assert_single_distributed_slot(&decoded);
    }

    #[test]
    fn distributed_vm_envelope_admission_roundtrip(enabled in any::<bool>()) {
        let mut claims = empty_claims();
        claims.distributed.vm_envelope_admission = Some(VMEnvelopeAdmissionConfig { enabled });
        let decoded = roundtrip_claims(claims);
        assert!(decoded.distributed.vm_envelope_admission.is_some());
        assert_single_distributed_slot(&decoded);
    }

    #[test]
    fn distributed_protocol_envelope_bridge_roundtrip(enabled in any::<bool>()) {
        let mut claims = empty_claims();
        claims.distributed.protocol_envelope_bridge = Some(ProtocolEnvelopeBridgeConfig { enabled });
        let decoded = roundtrip_claims(claims);
        assert!(decoded.distributed.protocol_envelope_bridge.is_some());
        assert_single_distributed_slot(&decoded);
    }

    #[test]
    fn classical_foster_roundtrip(enabled in any::<bool>()) {
        let mut claims = empty_claims();
        claims.classical.foster = Some(FosterConfig { enabled });
        let decoded = roundtrip_claims(claims);
        assert!(decoded.classical.foster.is_some());
        assert_single_classical_slot(&decoded);
    }

    #[test]
    fn classical_max_weight_roundtrip(enabled in any::<bool>(), slack_ppm in prop::option::of(0u32..=1_000_000)) {
        let mut claims = empty_claims();
        claims.classical.max_weight = Some(MaxWeightConfig {
            enabled,
            slack: slack_ppm.map(ppm_to_fixed),
        });
        let decoded = roundtrip_claims(claims);
        assert!(decoded.classical.max_weight.is_some());
        assert_single_classical_slot(&decoded);
    }

    #[test]
    fn classical_ldp_roundtrip(enabled in any::<bool>()) {
        let mut claims = empty_claims();
        claims.classical.ldp = Some(LDPConfig { enabled });
        let decoded = roundtrip_claims(claims);
        assert!(decoded.classical.ldp.is_some());
        assert_single_classical_slot(&decoded);
    }

    #[test]
    fn classical_mean_field_roundtrip(enabled in any::<bool>(), population_size in prop::option::of(1usize..10_000)) {
        let mut claims = empty_claims();
        claims.classical.mean_field = Some(MeanFieldConfig { enabled, population_size });
        let decoded = roundtrip_claims(claims);
        assert!(decoded.classical.mean_field.is_some());
        assert_single_classical_slot(&decoded);
    }

    #[test]
    fn classical_heavy_traffic_roundtrip(enabled in any::<bool>()) {
        let mut claims = empty_claims();
        claims.classical.heavy_traffic = Some(HeavyTrafficConfig { enabled });
        let decoded = roundtrip_claims(claims);
        assert!(decoded.classical.heavy_traffic.is_some());
        assert_single_classical_slot(&decoded);
    }

    #[test]
    fn classical_mixing_roundtrip(enabled in any::<bool>(), mixing_time_bound in prop::option::of(0usize..10_000)) {
        let mut claims = empty_claims();
        claims.classical.mixing = Some(MixingConfig { enabled, mixing_time_bound });
        let decoded = roundtrip_claims(claims);
        assert!(decoded.classical.mixing.is_some());
        assert_single_classical_slot(&decoded);
    }

    #[test]
    fn classical_fluid_roundtrip(enabled in any::<bool>()) {
        let mut claims = empty_claims();
        claims.classical.fluid = Some(FluidConfig { enabled });
        let decoded = roundtrip_claims(claims);
        assert!(decoded.classical.fluid.is_some());
        assert_single_classical_slot(&decoded);
    }

    #[test]
    fn classical_concentration_roundtrip(enabled in any::<bool>()) {
        let mut claims = empty_claims();
        claims.classical.concentration = Some(ConcentrationConfig { enabled });
        let decoded = roundtrip_claims(claims);
        assert!(decoded.classical.concentration.is_some());
        assert_single_classical_slot(&decoded);
    }

    #[test]
    fn classical_littles_law_roundtrip(enabled in any::<bool>()) {
        let mut claims = empty_claims();
        claims.classical.littles_law = Some(LittlesLawConfig { enabled });
        let decoded = roundtrip_claims(claims);
        assert!(decoded.classical.littles_law.is_some());
        assert_single_classical_slot(&decoded);
    }

    #[test]
    fn classical_functional_clt_roundtrip(enabled in any::<bool>()) {
        let mut claims = empty_claims();
        claims.classical.functional_clt = Some(FunctionalCLTConfig { enabled });
        let decoded = roundtrip_claims(claims);
        assert!(decoded.classical.functional_clt.is_some());
        assert_single_classical_slot(&decoded);
    }
}
