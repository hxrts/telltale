#![cfg(not(target_arch = "wasm32"))]
#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

use std::fs;
use std::path::Path;
use std::process::Command;

use quote::format_ident;
use telltale_runtime::ast::{
    annotation::Annotations, Branch, Choreography, MessageType, NonEmptyVec, Protocol, Role,
};
use telltale_runtime::compiler::codegen::{generate_topology_integration, InlineTopology};
use telltale_runtime::{RoleName, TopologyBuilder, TopologyEndpoint};
use tempfile::tempdir;

fn role(name: &str) -> Role {
    Role::new(format_ident!("{name}")).expect("valid role")
}

fn message(name: &str) -> MessageType {
    MessageType {
        name: format_ident!("{name}"),
        type_annotation: None,
        payload: None,
    }
}

fn round_trip_topology_module() -> String {
    let alice = role("Alice");
    let bob = role("Bob");
    let choreography = Choreography {
        name: format_ident!("TopologyRoundTrip"),
        namespace: None,
        roles: vec![alice.clone(), bob.clone()],
        protocol: Protocol::Send {
            from: alice,
            to: bob,
            message: message("Ping"),
            continuation: Box::new(Protocol::End),
            annotations: Annotations::new(),
            from_annotations: Annotations::new(),
            to_annotations: Annotations::new(),
        },
        attrs: Default::default(),
    };
    generate_topology_integration(&choreography, &[]).to_string()
}

fn capacity_topology_module() -> String {
    let buyer = role("Buyer");
    let seller = role("Seller");
    let choreography = Choreography {
        name: format_ident!("TopologyCapacity"),
        namespace: None,
        roles: vec![buyer.clone(), seller.clone()],
        protocol: Protocol::Choice {
            role: seller.clone(),
            branches: NonEmptyVec::from_head_tail(
                Branch {
                    label: format_ident!("Accept"),
                    guard: None,
                    protocol: Protocol::Send {
                        from: seller.clone(),
                        to: buyer.clone(),
                        message: message("Confirmation"),
                        continuation: Box::new(Protocol::End),
                        annotations: Annotations::new(),
                        from_annotations: Annotations::new(),
                        to_annotations: Annotations::new(),
                    },
                },
                vec![
                    Branch {
                        label: format_ident!("Reject"),
                        guard: None,
                        protocol: Protocol::Send {
                            from: seller.clone(),
                            to: buyer.clone(),
                            message: message("Rejection"),
                            continuation: Box::new(Protocol::End),
                            annotations: Annotations::new(),
                            from_annotations: Annotations::new(),
                            to_annotations: Annotations::new(),
                        },
                    },
                    Branch {
                        label: format_ident!("Defer"),
                        guard: None,
                        protocol: Protocol::Send {
                            from: seller,
                            to: buyer,
                            message: message("Deferred"),
                            continuation: Box::new(Protocol::End),
                            annotations: Annotations::new(),
                            from_annotations: Annotations::new(),
                            to_annotations: Annotations::new(),
                        },
                    },
                ],
            ),
            annotations: Annotations::new(),
        },
        attrs: Default::default(),
    };
    generate_topology_integration(&choreography, &[]).to_string()
}

fn named_topology_module() -> String {
    let alice = role("Alice");
    let bob = role("Bob");
    let choreography = Choreography {
        name: format_ident!("TopologyNamed"),
        namespace: None,
        roles: vec![alice.clone(), bob.clone()],
        protocol: Protocol::Send {
            from: alice,
            to: bob,
            message: message("Ping"),
            continuation: Box::new(Protocol::End),
            annotations: Annotations::new(),
            from_annotations: Annotations::new(),
            to_annotations: Annotations::new(),
        },
        attrs: Default::default(),
    };
    let edge = InlineTopology {
        name: "Edge".to_string(),
        topology: TopologyBuilder::new()
            .local_role(RoleName::from_static("Alice"))
            .remote_role(
                RoleName::from_static("Bob"),
                TopologyEndpoint::new("127.0.0.1:19901").expect("valid endpoint"),
            )
            .build(),
    };
    generate_topology_integration(&choreography, &[edge]).to_string()
}

fn write_temp_crate(root: &Path) {
    let runtime_path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .canonicalize()
        .expect("runtime manifest dir");
    let workspace_root = runtime_path
        .parent()
        .and_then(Path::parent)
        .expect("workspace root");
    let cargo_toml = format!(
        r#"[package]
name = "generated-topology-public-path-smoke"
version = "0.1.0"
edition = "2021"

[dependencies]
telltale-runtime = {{ path = "{}" }}
tokio = {{ version = "1.35", features = ["macros", "rt-multi-thread"] }}
"#,
        runtime_path.display()
    );
    fs::write(root.join("Cargo.toml"), cargo_toml).expect("write Cargo.toml");
    fs::copy(workspace_root.join("Cargo.lock"), root.join("Cargo.lock"))
        .expect("copy workspace Cargo.lock");
    fs::create_dir_all(root.join("src")).expect("create src");

    let round_trip = round_trip_topology_module();
    let capacity = capacity_topology_module();
    let named = named_topology_module();
    let lib = format!(
        r#"
use telltale_runtime::RoleName;

pub mod TopologyRoundTrip {{
    use super::*;

    #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Ord, PartialOrd)]
    pub enum Role {{
        Alice,
        Bob,
    }}

    impl Role {{
        pub fn role_name(&self) -> RoleName {{
            match self {{
                Self::Alice => RoleName::from_static("Alice"),
                Self::Bob => RoleName::from_static("Bob"),
            }}
        }}
    }}

    {round_trip}
}}

pub mod TopologyCapacity {{
    use super::*;

    #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Ord, PartialOrd)]
    pub enum Role {{
        Buyer,
        Seller,
    }}

    impl Role {{
        pub fn role_name(&self) -> RoleName {{
            match self {{
                Self::Buyer => RoleName::from_static("Buyer"),
                Self::Seller => RoleName::from_static("Seller"),
            }}
        }}
    }}

    {capacity}
}}

pub mod TopologyNamed {{
    use super::*;

    #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Ord, PartialOrd)]
    pub enum Role {{
        Alice,
        Bob,
    }}

    impl Role {{
        pub fn role_name(&self) -> RoleName {{
            match self {{
                Self::Alice => RoleName::from_static("Alice"),
                Self::Bob => RoleName::from_static("Bob"),
            }}
        }}
    }}

    {named}
}}
"#
    );
    fs::write(root.join("src/lib.rs"), lib).expect("write lib.rs");

    fs::create_dir_all(root.join("tests")).expect("create tests dir");
    fs::write(
        root.join("tests/public_path.rs"),
        r#"
use generated_topology_public_path_smoke::{TopologyCapacity, TopologyNamed, TopologyRoundTrip};
use telltale_runtime::{
    ChannelCapacity, Location, RoleName, TopologyBuilder, TopologyEndpoint,
    TransportFactory, TransportType,
};

#[tokio::test]
async fn generated_helpers_execute_local_and_custom_topologies_end_to_end() {
    let local_alice = TopologyRoundTrip::topology::handler(TopologyRoundTrip::Role::Alice);
    let local_bob = TopologyRoundTrip::topology::handler(TopologyRoundTrip::Role::Bob);
    local_alice.initialize().await.expect("init local Alice");
    local_bob.initialize().await.expect("init local Bob");

    local_alice
        .send(&RoleName::from_static("Bob"), b"local-ping".to_vec())
        .await
        .expect("local helper send");
    assert_eq!(
        local_bob
            .recv(&RoleName::from_static("Alice"))
            .await
            .expect("local helper recv"),
        b"local-ping".to_vec()
    );

    let custom_topology = TopologyBuilder::new()
        .local_role(RoleName::from_static("Alice"))
        .remote_role(
            RoleName::from_static("Bob"),
            TopologyEndpoint::new("127.0.0.1:19001").unwrap(),
        )
        .build();
    let custom_alice =
        TopologyRoundTrip::topology::with_topology(custom_topology.clone(), TopologyRoundTrip::Role::Alice)
            .expect("custom helper alice");
    let custom_bob =
        TopologyRoundTrip::topology::with_topology(custom_topology.clone(), TopologyRoundTrip::Role::Bob)
            .expect("custom helper bob");
    custom_alice.initialize().await.expect("init custom Alice");
    custom_bob.initialize().await.expect("init custom Bob");

    custom_alice
        .send(&RoleName::from_static("Bob"), b"remote-ping".to_vec())
        .await
        .expect("custom helper send");
    assert_eq!(
        custom_bob
            .recv(&RoleName::from_static("Alice"))
            .await
            .expect("custom helper recv"),
        b"remote-ping".to_vec()
    );

    assert_eq!(
        TransportFactory::transport_for_location(
            &RoleName::from_static("Alice"),
            &RoleName::from_static("Bob"),
            &custom_topology,
        )
        .expect("transport intent"),
        TransportType::Tcp
    );
    assert!(
        TransportFactory::create(&custom_topology, &RoleName::from_static("Alice")).is_err(),
        "placeholder remote transport creation must fail closed"
    );
}

#[test]
fn generated_helpers_reject_invalid_topology_combinations_before_execution() {
    let missing_role = TopologyBuilder::new()
        .local_role(RoleName::from_static("Alice"))
        .build();
    let missing_role_error =
        match TopologyRoundTrip::topology::with_topology(missing_role, TopologyRoundTrip::Role::Alice) {
            Ok(_) => panic!("missing Bob should fail validation"),
            Err(err) => err,
        };
    assert!(missing_role_error.contains("Topology validation failed"));

    let insufficient_capacity = TopologyBuilder::new()
        .local_role(RoleName::from_static("Buyer"))
        .local_role(RoleName::from_static("Seller"))
        .channel_capacity(
            RoleName::from_static("Seller"),
            RoleName::from_static("Buyer"),
            ChannelCapacity::try_new(1).expect("1-bit capacity"),
        )
        .build();
    let insufficient_capacity_error = match TopologyCapacity::topology::with_topology(
        insufficient_capacity,
        TopologyCapacity::Role::Seller,
    ) {
        Ok(_) => panic!("three-way branch should reject one-bit capacity"),
        Err(err) => err,
    };
    assert!(
        insufficient_capacity_error.contains("InsufficientCapacity"),
        "unexpected error: {insufficient_capacity_error}"
    );

    let invalid_placement = TopologyBuilder::new()
        .local_role(RoleName::from_static("Alice"))
        .local_role(RoleName::from_static("Bob"))
        .separated(RoleName::from_static("Alice"), RoleName::from_static("Bob"))
        .build();
    let invalid_placement_error = match TopologyRoundTrip::topology::with_topology(
        invalid_placement,
        TopologyRoundTrip::Role::Alice,
    ) {
        Ok(_) => panic!("separated local roles should fail validation"),
        Err(err) => err,
    };
    assert!(
        invalid_placement_error.contains("ConstraintViolation"),
        "unexpected error: {invalid_placement_error}"
    );

    let invalid_pin = TopologyBuilder::new()
        .local_role(RoleName::from_static("Alice"))
        .local_role(RoleName::from_static("Bob"))
        .pinned(
            RoleName::from_static("Bob"),
            Location::Remote(TopologyEndpoint::new("127.0.0.1:19999").unwrap()),
        )
        .build();
    let invalid_pin_error = match TopologyRoundTrip::topology::with_topology(
        invalid_pin,
        TopologyRoundTrip::Role::Bob,
    ) {
        Ok(_) => panic!("invalid pinned location should fail validation"),
        Err(err) => err,
    };
    assert!(
        invalid_pin_error.contains("ConstraintViolation"),
        "unexpected error: {invalid_pin_error}"
    );

    let unsupported_region = TopologyBuilder::new()
        .local_role(RoleName::from_static("Alice"))
        .local_role(RoleName::from_static("Bob"))
        .region(
            RoleName::from_static("Alice"),
            telltale_runtime::Region::new("membership").expect("region"),
        )
        .build();
    let unsupported_region_error = match TopologyRoundTrip::topology::with_topology(
        unsupported_region,
        TopologyRoundTrip::Role::Alice,
    ) {
        Ok(_) => panic!("region constraints should fail closed until executable"),
        Err(err) => err,
    };
    assert!(
        unsupported_region_error.contains("not yet executable"),
        "unexpected error: {unsupported_region_error}"
    );
}

#[tokio::test]
async fn equivalent_local_and_transport_intent_topologies_preserve_protocol_outcome() {
    let local_alice = TopologyRoundTrip::topology::handler(TopologyRoundTrip::Role::Alice);
    let local_bob = TopologyRoundTrip::topology::handler(TopologyRoundTrip::Role::Bob);
    local_alice.initialize().await.unwrap();
    local_bob.initialize().await.unwrap();

    let transport_topology = TopologyBuilder::new()
        .remote_role(
            RoleName::from_static("Alice"),
            TopologyEndpoint::new("127.0.0.1:19101").unwrap(),
        )
        .remote_role(
            RoleName::from_static("Bob"),
            TopologyEndpoint::new("127.0.0.1:19102").unwrap(),
        )
        .build();
    let transport_alice = TopologyRoundTrip::topology::with_topology(
        transport_topology.clone(),
        TopologyRoundTrip::Role::Alice,
    )
    .unwrap();
    let transport_bob =
        TopologyRoundTrip::topology::with_topology(transport_topology, TopologyRoundTrip::Role::Bob)
            .unwrap();
    transport_alice.initialize().await.unwrap();
    transport_bob.initialize().await.unwrap();

    local_alice
        .send(&RoleName::from_static("Bob"), b"same-outcome".to_vec())
        .await
        .unwrap();
    transport_alice
        .send(&RoleName::from_static("Bob"), b"same-outcome".to_vec())
        .await
        .unwrap();

    assert_eq!(
        local_bob.recv(&RoleName::from_static("Alice")).await.unwrap(),
        transport_bob
            .recv(&RoleName::from_static("Alice"))
            .await
            .unwrap()
    );
}

#[tokio::test]
async fn generated_named_topology_helpers_execute_without_external_network() {
    let edge_alice = TopologyNamed::topology::topologies::edge_handler(TopologyNamed::Role::Alice)
        .expect("named topology alice");
    let edge_bob = TopologyNamed::topology::topologies::edge_handler(TopologyNamed::Role::Bob)
        .expect("named topology bob");
    edge_alice.initialize().await.expect("init named alice");
    edge_bob.initialize().await.expect("init named bob");

    assert_eq!(
        TransportFactory::transport_for_location(
            &RoleName::from_static("Alice"),
            &RoleName::from_static("Bob"),
            &TopologyNamed::topology::topologies::edge(),
        )
        .expect("named transport intent"),
        TransportType::Tcp
    );

    edge_alice
        .send(&RoleName::from_static("Bob"), b"named-ping".to_vec())
        .await
        .expect("named helper send");
    assert_eq!(
        edge_bob
            .recv(&RoleName::from_static("Alice"))
            .await
            .expect("named helper recv"),
        b"named-ping".to_vec()
    );
}
"#,
    )
    .expect("write public_path.rs");
}

#[test]
fn generated_topology_public_path_executes_end_to_end_in_a_temp_crate() {
    let temp = tempdir().expect("temp dir");
    write_temp_crate(temp.path());

    let output = Command::new("cargo")
        .arg("test")
        .arg("--offline")
        .arg("--manifest-path")
        .arg(temp.path().join("Cargo.toml"))
        .arg("--test")
        .arg("public_path")
        .arg("--")
        .arg("--nocapture")
        .arg("--test-threads=1")
        .output()
        .expect("run temp cargo test");

    assert!(
        output.status.success(),
        "temp generated-topology public-path test failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}
