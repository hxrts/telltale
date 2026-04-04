//! Machine-checkable transport contract profile tests.
#![cfg(not(target_arch = "wasm32"))]
#![allow(clippy::unwrap_used)]

use telltale_runtime::{
    validate_transport_contract_profile, validated_transport_contract_profile,
    InMemoryChannelTransport, Location, RoleName, Topology, TransportContractTier,
    TransportFactory, TransportType,
};

#[test]
fn documented_first_party_transport_profiles_are_machine_checkable() {
    let in_memory = validated_transport_contract_profile::<InMemoryChannelTransport>().unwrap();
    assert_eq!(in_memory.tier, TransportContractTier::FirstPartyRuntime);
    assert_eq!(
        in_memory.operational.transport_type,
        TransportType::InMemory
    );
    assert!(in_memory.semantics.deterministic_for_regression);
}

#[test]
fn topology_transport_factory_selects_validated_contract_profiles() {
    let local_topology = Topology::builder()
        .local_role(RoleName::from_static("Alice"))
        .local_role(RoleName::from_static("Bob"))
        .build();
    let local_profile = TransportFactory::contract_profile_for_topology(
        &local_topology,
        &RoleName::from_static("Alice"),
    )
    .unwrap();
    validate_transport_contract_profile(&local_profile).unwrap();
    assert_eq!(local_profile.transport_name, "InMemoryChannelTransport");

    let remote_topology = Topology::builder()
        .remote_role(
            RoleName::from_static("Alice"),
            telltale_runtime::TopologyEndpoint::new("127.0.0.1:21901").unwrap(),
        )
        .remote_role(
            RoleName::from_static("Bob"),
            telltale_runtime::TopologyEndpoint::new("127.0.0.1:21902").unwrap(),
        )
        .build();
    let remote_profile = TransportFactory::contract_profile_for_topology(
        &remote_topology,
        &RoleName::from_static("Alice"),
    )
    .unwrap();
    validate_transport_contract_profile(&remote_profile).unwrap();
    assert_eq!(
        remote_profile.operational.transport_type,
        TransportType::Tcp
    );
    assert!(matches!(
        remote_topology
            .get_location(&RoleName::from_static("Bob"))
            .unwrap(),
        Location::Remote(_)
    ));
}
