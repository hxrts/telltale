//! Tier 5: negative test fixtures (invalid invariant claims).

use telltale_bridge::{
    AvailabilityLevel, CAPConfig, DistributedClaims, FLPConfig, InvariantClaims, LivenessConfig,
    PartitionModel, ProtocolEnvelopeBridgeConfig, ProtocolMachineEnvelopeAdherenceConfig,
    ProtocolMachineEnvelopeAdmissionConfig, QuorumGeometryConfig, QuorumSystemKind, SchedulerKind,
    TimingModel,
};

use super::{tier1_minimal, ProtocolFixture};

#[must_use]
pub fn bad_quorum() -> ProtocolFixture {
    tier1_minimal::ping_pong().with_claims(InvariantClaims {
        distributed: DistributedClaims {
            quorum_geometry: Some(QuorumGeometryConfig {
                quorum_system: QuorumSystemKind::Majority,
                n: 4,
                quorum_size: 2,
                intersection_size: 0,
            }),
            cap: Some(CAPConfig {
                consistency: telltale_bridge::ConsistencyLevel::Linearizable,
                availability: AvailabilityLevel::Total,
                partition_model: PartitionModel::NetworkSplit,
            }),
            ..DistributedClaims::default()
        },
        ..InvariantClaims::default()
    })
}

#[must_use]
pub fn deadlock() -> ProtocolFixture {
    tier1_minimal::chain().with_claims(InvariantClaims {
        liveness: Some(LivenessConfig {
            scheduler: SchedulerKind::Cooperative,
            fairness_k: None,
            progress_required: true,
        }),
        distributed: DistributedClaims {
            flp: Some(FLPConfig {
                crash_bound: 1,
                requires_determinism: true,
            }),
            ..DistributedClaims::default()
        },
        ..InvariantClaims::default()
    })
}

#[must_use]
pub fn unbounded_wait() -> ProtocolFixture {
    tier1_minimal::ping_pong().with_claims(InvariantClaims {
        liveness: Some(LivenessConfig {
            scheduler: SchedulerKind::RoundRobin,
            fairness_k: None,
            progress_required: true,
        }),
        distributed: DistributedClaims {
            partial_synchrony: Some(telltale_bridge::PartialSynchronyConfig {
                timing: TimingModel::Asynchronous,
                delta_bound: None,
            }),
            responsiveness: Some(telltale_bridge::ResponsivenessConfig {
                leader_based: false,
                requires_stable_period: false,
            }),
            ..DistributedClaims::default()
        },
        ..InvariantClaims::default()
    })
}

#[must_use]
pub fn bridge_without_admission() -> ProtocolFixture {
    tier1_minimal::ping_pong().with_claims(InvariantClaims {
        distributed: DistributedClaims {
            protocol_machine_envelope_adherence: Some(ProtocolMachineEnvelopeAdherenceConfig {
                enabled: true,
            }),
            protocol_machine_envelope_admission: Some(ProtocolMachineEnvelopeAdmissionConfig {
                enabled: false,
            }),
            protocol_envelope_bridge: Some(ProtocolEnvelopeBridgeConfig { enabled: true }),
            ..DistributedClaims::default()
        },
        ..InvariantClaims::default()
    })
}
