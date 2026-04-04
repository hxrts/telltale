//! Transport contract profile validation tests.
#![allow(clippy::unwrap_used)]

use telltale_runtime::{
    validated_transport_contract_profile, TransportContractTier, TransportType,
};
use telltale_transport::{TcpTransport, TcpTransportConfig};

#[test]
fn tcp_transport_contract_profile_is_validated() {
    let profile = validated_transport_contract_profile::<TcpTransport>().unwrap();
    assert_eq!(profile.tier, TransportContractTier::FirstPartyRuntime);
    assert_eq!(profile.operational.transport_type, TransportType::Tcp);
    assert!(profile.semantics.explicit_readiness_errors);

    let config =
        TcpTransportConfig::new("Alice", "127.0.0.1:25001").with_peer("Bob", "127.0.0.1:25002");
    let transport = TcpTransport::new(config);
    assert_eq!(transport.role(), "Alice");
}
