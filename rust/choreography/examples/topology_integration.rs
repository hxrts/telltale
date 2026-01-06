//! Topology Integration Example
//!
//! This example demonstrates the topology integration for choreographic protocols,
//! showing how to:
//! - Create handlers with local-mode topology (for testing)
//! - Create handlers with custom topology (for distributed deployment)
//! - Use pre-configured topology constants
//!
//! Run with:
//! ```bash
//! cargo run --example topology_integration
//! ```

#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

use rumpsteak_aura_choreography::topology::{TopologyBuilder, TopologyHandler, TopologyMode};
use rumpsteak_aura_choreography::{Namespace, RoleName, TopologyEndpoint};

fn main() {
    println!("╔════════════════════════════════════════════════════════════╗");
    println!("║       Topology Integration for Choreographic Protocols     ║");
    println!("╚════════════════════════════════════════════════════════════╝\n");

    // Example 1: Local mode for testing
    println!("=== 1. Local Mode Handler ===");
    demonstrate_local_handler();

    // Example 2: Custom topology for distributed deployment
    println!("\n=== 2. Custom Topology Handler ===");
    demonstrate_custom_topology();

    // Example 3: Pre-configured topologies
    println!("\n=== 3. Pre-configured Topologies ===");
    demonstrate_preconfigured_topologies();

    // Example 4: Role validation
    println!("\n=== 4. Role Validation ===");
    demonstrate_role_validation();

    println!("\n╔════════════════════════════════════════════════════════════╗");
    println!("║       Topology integration complete!                        ║");
    println!("╚════════════════════════════════════════════════════════════╝");
}

/// Demonstrate creating a local-mode handler for testing
fn demonstrate_local_handler() {
    // In a generated protocol, this would be:
    // let handler = MyProtocol::topology::handler(Role::Alice);

    // For this example, we create the handler directly:
    let handler = TopologyHandler::local(RoleName::from_static("Alice"));

    println!("  Created handler for role: {}", handler.role());
    println!("  Topology mode: Local (all in-process)");
    println!(
        "  Handler location for 'Alice': {:?}",
        handler
            .get_location(&RoleName::from_static("Alice"))
            .unwrap()
    );
}

/// Demonstrate creating handlers with custom topology
fn demonstrate_custom_topology() {
    // Build a production topology
    let topology = TopologyBuilder::new()
        .local_role(RoleName::from_static("Alice"))
        .remote_role(
            RoleName::from_static("Bob"),
            TopologyEndpoint::new("192.168.1.10:8080").unwrap(),
        )
        .remote_role(
            RoleName::from_static("Carol"),
            TopologyEndpoint::new("192.168.1.11:8081").unwrap(),
        )
        .build();

    println!("  Topology configuration:");
    println!("    Alice:  local");
    println!("    Bob:    192.168.1.10:8080");
    println!("    Carol:  192.168.1.11:8081");

    // Create handler for Alice
    let handler = TopologyHandler::new(topology.clone(), RoleName::from_static("Alice"));
    println!("\n  Created handler for Alice");
    println!(
        "    Location of Alice: {:?}",
        handler
            .get_location(&RoleName::from_static("Alice"))
            .unwrap()
    );
    println!(
        "    Location of Bob:   {:?}",
        handler.get_location(&RoleName::from_static("Bob")).unwrap()
    );
    println!(
        "    Location of Carol: {:?}",
        handler
            .get_location(&RoleName::from_static("Carol"))
            .unwrap()
    );

    // Validate against known roles
    let valid_roles = vec![
        RoleName::from_static("Alice"),
        RoleName::from_static("Bob"),
        RoleName::from_static("Carol"),
    ];
    let validation = topology.validate(&valid_roles);
    println!("\n  Topology validation: {:?}", validation);
}

/// Demonstrate pre-configured topologies
fn demonstrate_preconfigured_topologies() {
    // Development topology - all local
    let dev_topology = TopologyBuilder::new().mode(TopologyMode::Local).build();

    println!("  Development topology:");
    println!("    Mode: {:?}", dev_topology.mode);
    println!("    All roles run in-process");

    // Production topology with specific deployments
    let prod_topology = TopologyBuilder::new()
        .mode(TopologyMode::PerRole)
        .remote_role(
            RoleName::from_static("Alice"),
            TopologyEndpoint::new("alice.prod.internal:8080").unwrap(),
        )
        .remote_role(
            RoleName::from_static("Bob"),
            TopologyEndpoint::new("bob.prod.internal:8081").unwrap(),
        )
        .remote_role(
            RoleName::from_static("Carol"),
            TopologyEndpoint::new("carol.prod.internal:8082").unwrap(),
        )
        .build();

    println!("\n  Production topology:");
    println!("    Mode: {:?}", prod_topology.mode);
    for (role, location) in &prod_topology.locations {
        println!("    {}: {:?}", role, location);
    }

    // Kubernetes topology
    let k8s_topology = TopologyBuilder::new()
        .mode(TopologyMode::Kubernetes(
            Namespace::new("my-namespace").unwrap(),
        ))
        .build();

    println!("\n  Kubernetes topology:");
    println!("    Mode: {:?}", k8s_topology.mode);
    println!("    Role discovery via Kubernetes services");
}

/// Demonstrate role validation
fn demonstrate_role_validation() {
    let valid_roles = vec![RoleName::from_static("Alice"), RoleName::from_static("Bob")];

    // Valid topology
    let valid_topology = TopologyBuilder::new()
        .local_role(RoleName::from_static("Alice"))
        .local_role(RoleName::from_static("Bob"))
        .build();

    let validation = valid_topology.validate(&valid_roles);
    println!("  Valid topology validation: {:?}", validation);

    // Invalid topology (references unknown role)
    let invalid_topology = TopologyBuilder::new()
        .local_role(RoleName::from_static("Alice"))
        .local_role(RoleName::from_static("UnknownRole"))
        .build();

    let validation = invalid_topology.validate(&valid_roles);
    println!("  Invalid topology validation: {:?}", validation);

    // Topology with constraints
    let constrained_topology = TopologyBuilder::new()
        .local_role(RoleName::from_static("Alice"))
        .local_role(RoleName::from_static("Bob"))
        .colocated(RoleName::from_static("Alice"), RoleName::from_static("Bob"))
        .build();

    println!("\n  Topology with constraints:");
    println!("    Constraint: Alice and Bob must be colocated");
    let validation = constrained_topology.validate(&valid_roles);
    println!("    Validation: {:?}", validation);
}

// ============================================================================
// Simulated Generated Code
// ============================================================================
//
// When using the choreography! macro with topology integration, the following
// code would be generated:
//
// ```rust
// pub mod topology {
//     use super::*;
//     use rumpsteak_aura_choreography::topology::{
//         Location, Topology, TopologyBuilder, TopologyHandler, TopologyMode,
//     };
//     use rumpsteak_aura_choreography::{Namespace, RoleName, TopologyEndpoint};
//
//     pub fn handler(role: Role) -> TopologyHandler {
//         TopologyHandler::local(role.role_name())
//     }
//
//     pub fn with_topology(topology: Topology, role: Role) -> Result<TopologyHandler, String> {
//         let roles = [RoleName::from_static("Alice"), RoleName::from_static("Bob")];
//
//         let validation = topology.validate(&roles);
//         if !validation.is_valid() {
//             return Err(format!("Topology validation failed: {:?}", validation));
//         }
//
//         Ok(TopologyHandler::new(topology, role.role_name()))
//     }
//
//     pub mod topologies {
//         use super::*;
//
//         /// Development topology (all local)
//         pub fn dev() -> Topology {
//             TopologyBuilder::new()
//                 .mode(TopologyMode::Local)
//                 .build()
//         }
//
//         pub fn dev_handler(role: Role) -> Result<TopologyHandler, String> {
//             with_topology(dev(), role)
//         }
//
//         /// Production topology
//         pub fn prod() -> Topology {
//             TopologyBuilder::new()
//                 .remote_role(
//                     RoleName::from_static("Alice"),
//                     TopologyEndpoint::new("alice.prod.internal:8080").unwrap(),
//                 )
//                 .remote_role(
//                     RoleName::from_static("Bob"),
//                     TopologyEndpoint::new("bob.prod.internal:8081").unwrap(),
//                 )
//                 .build()
//         }
//
//         pub fn prod_handler(role: Role) -> Result<TopologyHandler, String> {
//             with_topology(prod(), role)
//         }
//     }
// }
// ```
//
// Usage:
// ```rust
// // Local testing
// let handler = MyProtocol::topology::handler("Alice")?;
//
// // Pre-configured production
// let handler = MyProtocol::topology::topologies::prod_handler("Alice")?;
//
// // Custom topology
// let topology = Topology::builder()
//     .remote_role(
//         RoleName::from_static("Alice"),
//         TopologyEndpoint::new("custom-address:8080").unwrap(),
//     )
//     .build();
// let handler = MyProtocol::topology::with_topology(topology, "Alice")?;
// ```
