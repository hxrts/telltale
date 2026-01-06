//! Example: Threshold Signatures with Role Families
//!
//! This example demonstrates:
//! - Runtime role family resolution with `resolve_family()` and `resolve_range()`
//! - Broadcasting messages to all members of a role family
//! - Collecting responses from a threshold of signers
//! - Topology-based role constraint validation

use rumpsteak_aura_choreography::effects::{LabelId, RoleId};
use rumpsteak_aura_choreography::identifiers::RoleName;
use rumpsteak_aura_choreography::runtime::adapter::ChoreographicAdapter;
use rumpsteak_aura_choreography::runtime::test_adapter::TestAdapter;
use rumpsteak_aura_choreography::topology::Topology;
use serde::{Deserialize, Serialize};

// ============================================================================
// Role and Label Definitions
// ============================================================================

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
enum Role {
    Coordinator,
    Signer(u32),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
enum Label {
    Sign,
    Aggregate,
}

impl LabelId for Label {
    fn as_str(&self) -> &'static str {
        match self {
            Label::Sign => "Sign",
            Label::Aggregate => "Aggregate",
        }
    }

    fn from_str(label: &str) -> Option<Self> {
        match label {
            "Sign" => Some(Label::Sign),
            "Aggregate" => Some(Label::Aggregate),
            _ => None,
        }
    }
}

impl RoleId for Role {
    type Label = Label;

    fn role_name(&self) -> RoleName {
        match self {
            Role::Coordinator => RoleName::from_static("Coordinator"),
            Role::Signer(_) => RoleName::from_static("Signer"),
        }
    }

    fn role_index(&self) -> Option<u32> {
        match self {
            Role::Signer(idx) => Some(*idx),
            _ => None,
        }
    }
}

// ============================================================================
// Message Types
// ============================================================================

#[derive(Debug, Clone, Serialize, Deserialize)]
struct SigningRequest {
    message_hash: Vec<u8>,
    session_id: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct PartialSignature {
    signer_id: u32,
    signature_share: Vec<u8>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct AggregatedSignature {
    signature: Vec<u8>,
    signers_used: Vec<u32>,
}

// ============================================================================
// Main Example
// ============================================================================

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("Threshold Signature Example");
    println!("============================\n");

    // Define topology with role constraints
    let topology_config = r#"
        topology ThresholdSignature for CryptoProtocol {
            Coordinator: localhost:8000

            role_constraints {
                Signer: min = 3, max = 10
            }
        }
    "#;

    let parsed = Topology::parse(topology_config)?;
    let topology = parsed.topology;
    println!("Loaded topology: {}", parsed.name);
    println!(
        "  Role constraint: Signer min={}, max={:?}",
        topology.get_family_constraint("Signer").unwrap().min,
        topology.get_family_constraint("Signer").unwrap().max
    );

    // Create 5 signers (satisfies constraint: 3 <= 5 <= 10)
    let signers: Vec<Role> = (0..5).map(Role::Signer).collect();
    let mut coordinator = TestAdapter::new(Role::Coordinator).with_family("Signer", signers);

    // Validate against topology constraints
    let signer_count = coordinator.family_size("Signer")?;
    topology.validate_family("Signer", signer_count)?;
    println!(
        "  Signers configured: {} (constraint satisfied)",
        signer_count
    );

    // Step 1: Coordinator broadcasts signing request to all signers
    println!("\nStep 1: Broadcasting signing request");
    let all_signers = coordinator.resolve_family("Signer")?;
    println!("  Resolved {} signers", all_signers.len());

    let request = SigningRequest {
        message_hash: vec![0xAB; 32],
        session_id: 12345,
    };
    coordinator.broadcast(&all_signers, request).await?;
    println!("  Broadcast complete");

    // Simulate signer responses (in a real system, each signer would respond)
    for i in 0..5 {
        let sig = PartialSignature {
            signer_id: i,
            signature_share: vec![i as u8; 64],
        };
        coordinator.queue_typed_message(Role::Signer(i), Role::Coordinator, sig);
    }

    // Step 2: Collect signatures from threshold (3 signers)
    println!("\nStep 2: Collecting threshold of signatures");
    let threshold = 3;
    let threshold_signers = coordinator.resolve_range("Signer", 0, threshold as u32)?;
    println!(
        "  Collecting from {} signers (threshold)",
        threshold_signers.len()
    );

    let partial_sigs: Vec<PartialSignature> = coordinator.collect(&threshold_signers).await?;
    println!("  Collected {} partial signatures:", partial_sigs.len());
    for sig in &partial_sigs {
        println!(
            "    - Signer {} contributed {} bytes",
            sig.signer_id,
            sig.signature_share.len()
        );
    }

    // Step 3: Aggregate and broadcast final signature
    println!("\nStep 3: Aggregating and broadcasting result");
    let aggregated = AggregatedSignature {
        signature: vec![0xFF; 96], // Combined BLS signature
        signers_used: partial_sigs.iter().map(|s| s.signer_id).collect(),
    };
    println!(
        "  Aggregated signature from signers: {:?}",
        aggregated.signers_used
    );

    // Broadcast final signature to all signers
    coordinator.broadcast(&all_signers, aggregated).await?;
    println!("  Final signature broadcast complete");

    println!("\nThreshold signature protocol completed successfully!");
    Ok(())
}
