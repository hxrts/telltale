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
    // let handler = MyProtocol::topology::handler("Alice")?;

    // For this example, we create the handler directly:
    let handler = TopologyHandler::local("Alice");

    println!("  Created handler for role: {}", handler.role());
    println!("  Topology mode: Local (all in-process)");
    println!(
        "  Handler location for 'Alice': {:?}",
        handler.get_location("Alice")
    );
}

/// Demonstrate creating handlers with custom topology
fn demonstrate_custom_topology() {
    // Build a production topology
    let topology = TopologyBuilder::new()
        .local_role("Alice")
        .remote_role("Bob", "192.168.1.10:8080")
        .remote_role("Carol", "192.168.1.11:8081")
        .build();

    println!("  Topology configuration:");
    println!("    Alice:  local");
    println!("    Bob:    192.168.1.10:8080");
    println!("    Carol:  192.168.1.11:8081");

    // Create handler for Alice
    let handler = TopologyHandler::new(topology.clone(), "Alice");
    println!("\n  Created handler for Alice");
    println!("    Location of Alice: {:?}", handler.get_location("Alice"));
    println!("    Location of Bob:   {:?}", handler.get_location("Bob"));
    println!("    Location of Carol: {:?}", handler.get_location("Carol"));

    // Validate against known roles
    let valid_roles = vec!["Alice", "Bob", "Carol"];
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
        .remote_role("Alice", "alice.prod.internal:8080")
        .remote_role("Bob", "bob.prod.internal:8081")
        .remote_role("Carol", "carol.prod.internal:8082")
        .build();

    println!("\n  Production topology:");
    println!("    Mode: {:?}", prod_topology.mode);
    for (role, location) in &prod_topology.locations {
        println!("    {}: {:?}", role, location);
    }

    // Kubernetes topology
    let k8s_topology = TopologyBuilder::new()
        .mode(TopologyMode::Kubernetes("my-namespace".to_string()))
        .build();

    println!("\n  Kubernetes topology:");
    println!("    Mode: {:?}", k8s_topology.mode);
    println!("    Role discovery via Kubernetes services");
}

/// Demonstrate role validation
fn demonstrate_role_validation() {
    let valid_roles = vec!["Alice", "Bob"];

    // Valid topology
    let valid_topology = TopologyBuilder::new()
        .local_role("Alice")
        .local_role("Bob")
        .build();

    let validation = valid_topology.validate(&valid_roles);
    println!("  Valid topology validation: {:?}", validation);

    // Invalid topology (references unknown role)
    let invalid_topology = TopologyBuilder::new()
        .local_role("Alice")
        .local_role("UnknownRole")
        .build();

    let validation = invalid_topology.validate(&valid_roles);
    println!("  Invalid topology validation: {:?}", validation);

    // Topology with constraints
    let constrained_topology = TopologyBuilder::new()
        .local_role("Alice")
        .local_role("Bob")
        .colocated("Alice", "Bob")
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
//
//     const VALID_ROLES: &[&str] = &["Alice", "Bob"];
//
//     pub fn validate_role(role: &str) -> Result<(), String> {
//         if VALID_ROLES.contains(&role) {
//             Ok(())
//         } else {
//             Err(format!("Unknown role '{}' - valid roles are: {:?}", role, VALID_ROLES))
//         }
//     }
//
//     pub fn handler(role: impl Into<String>) -> Result<TopologyHandler, String> {
//         let role_str = role.into();
//         validate_role(&role_str)?;
//         Ok(TopologyHandler::local(role_str))
//     }
//
//     pub fn with_topology(
//         topology: Topology,
//         role: impl Into<String>,
//     ) -> Result<TopologyHandler, String> {
//         let role_str = role.into();
//         validate_role(&role_str)?;
//
//         let validation = topology.validate(VALID_ROLES);
//         if !validation.is_valid() {
//             return Err(format!("Topology validation failed: {:?}", validation));
//         }
//
//         Ok(TopologyHandler::new(topology, role_str))
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
//         pub fn dev_handler(role: impl Into<String>) -> Result<TopologyHandler, String> {
//             with_topology(dev(), role)
//         }
//
//         /// Production topology
//         pub fn prod() -> Topology {
//             TopologyBuilder::new()
//                 .remote_role("Alice", "alice.prod.internal:8080")
//                 .remote_role("Bob", "bob.prod.internal:8081")
//                 .build()
//         }
//
//         pub fn prod_handler(role: impl Into<String>) -> Result<TopologyHandler, String> {
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
//     .remote_role("Alice", "custom-address:8080")
//     .build();
// let handler = MyProtocol::topology::with_topology(topology, "Alice")?;
// ```
