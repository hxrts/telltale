//! Demonstrate how reference TCP transport contracts participate in theorem admission.
//!
//! This example does not open sockets. It shows the configuration-to-contract
//! boundary used by a demo or integration test: PSK TCP can satisfy theorem
//! requirements for authenticated protocol origins, while trusted-network TCP
//! cannot.

use std::collections::BTreeMap;
use std::sync::Arc;

use telltale_machine::runtime::loader::CodeImage;
use telltale_machine::{
    ComposedRuntime, CompositionCertificate, CompositionError, MemoryBudget, ProtocolMachineConfig,
    RuntimeContracts, TheoremPackCapabilities,
};
use telltale_transport::TcpTransportConfig;
use telltale_types::{GlobalType, Label, LocalTypeR};

fn demo_image(label: &str) -> Arc<CodeImage> {
    let mut local_types = BTreeMap::new();
    local_types.insert(
        "Alice".to_string(),
        LocalTypeR::send("Bob", Label::new(label), LocalTypeR::End),
    );
    local_types.insert(
        "Bob".to_string(),
        LocalTypeR::recv("Alice", Label::new(label), LocalTypeR::End),
    );
    let global = GlobalType::send("Alice", "Bob", Label::new(label), GlobalType::End);
    Arc::new(CodeImage::from_local_types(&local_types, &global))
}

fn certificate_with_transport_contract(
    artifact_id: &str,
    config: &TcpTransportConfig,
) -> CompositionCertificate {
    CompositionCertificate {
        artifact_id: artifact_id.to_string(),
        link_ok_full: true,
        theorem_pack: TheoremPackCapabilities::full(),
        runtime_contracts: Some(
            RuntimeContracts::full()
                .with_transport_contracts([config.runtime_transport_contract()]),
        ),
    }
}

fn admit_demo_bundle(certificate: CompositionCertificate) -> Result<(), CompositionError> {
    let mut runtime =
        ComposedRuntime::new(ProtocolMachineConfig::default(), MemoryBudget::default());
    let bundle = telltale_machine::ProtocolBundle::new(demo_image("hello"), certificate);
    runtime.admit_bundle(bundle)?;
    Ok(())
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let psk_config = TcpTransportConfig::new("Alice", "127.0.0.1:8080")
        .with_preshared_key([7u8; 32])
        .with_peer("Bob", "127.0.0.1:8081");
    admit_demo_bundle(certificate_with_transport_contract(
        "demo/psk-transport",
        &psk_config,
    ))?;

    let trusted_network_config = TcpTransportConfig::new("Alice", "127.0.0.1:8080")
        .allow_unauthenticated_for_trusted_network()
        .with_peer("Bob", "127.0.0.1:8081");
    let rejection = admit_demo_bundle(certificate_with_transport_contract(
        "demo/trusted-network-transport",
        &trusted_network_config,
    ));

    assert!(matches!(
        rejection,
        Err(CompositionError::UnsatisfiedTransportContract {
            transport_name,
            requirement: "authenticated_peers",
            ..
        }) if transport_name == "TcpTransport"
    ));

    Ok(())
}
