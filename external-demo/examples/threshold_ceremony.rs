//! Threshold Signing Ceremony Choreography
//!
//! This example demonstrates a complete threshold signing ceremony using the
//! DSL parsing with basic rumpsteak-aura features and extension points
//! for future Aura-specific enhancements.

use rumpsteak_aura::*;
use futures::channel::mpsc::{UnboundedSender, UnboundedReceiver};
use rumpsteak_aura_choreography::compiler::parser::parse_choreography_str_with_extensions;
use rumpsteak_aura_choreography::extensions::ExtensionRegistry;
use serde::{Deserialize, Serialize};

// Type definitions for the generated code
#[allow(dead_code)]
type Channel = channel::Bidirectional<UnboundedSender<Label>, UnboundedReceiver<Label>>;

#[allow(dead_code)]
#[derive(Message)]
enum Label {
    InitiateCeremony(InitiateCeremony),
    SigningCommitment(SigningCommitment),
    CommitmentAggregation(CommitmentAggregation),
    SignatureShare(SignatureShare),
    FinalSignature(FinalSignature),
}

// Message types for the threshold signing ceremony
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct InitiateCeremony {
    pub ceremony_id: String,
    pub message_hash: Vec<u8>,
    pub threshold: u32,
    pub participant_count: u32,
    pub timeout_ms: u64,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct SigningCommitment {
    pub ceremony_id: String,
    pub participant_id: String,
    pub nonce_commitment: Vec<u8>,
    pub proof_of_knowledge: Vec<u8>,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct CommitmentAggregation {
    pub ceremony_id: String,
    pub aggregated_commitments: Vec<u8>,
    pub participant_list: Vec<String>,
    pub ready_to_sign: bool,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct SignatureShare {
    pub ceremony_id: String,
    pub participant_id: String,
    pub signature_share: Vec<u8>,
    pub share_index: u32,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct FinalSignature {
    pub ceremony_id: String,
    pub aggregated_signature: Vec<u8>,
    pub success: bool,
    pub participating_ids: Vec<String>,
    pub completion_timestamp: u64,
}

const THRESHOLD_CEREMONY: &str = r#"
module threshold_ceremony exposing (ThresholdCeremony)
protocol ThresholdCeremony = {
    roles Coordinator, Signer[N]

    Coordinator -> Signer[*] : InitiateCeremony
    Signer[*] -> Coordinator : SigningCommitment
    Coordinator -> Signer[*] : CommitmentAggregation
    Signer[*] -> Coordinator : SignatureShare
    Coordinator -> Signer[*] : FinalSignature
}
"#;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== Threshold Signing Ceremony Choreography ===\n");

    let registry = ExtensionRegistry::new();
    let (choreo, _) = parse_choreography_str_with_extensions(THRESHOLD_CEREMONY, &registry)?;
    println!("Parsed protocol: {}", choreo.name);

    println!("This example demonstrates:");
    println!("- Complex multi-party protocol with external-demo");
    println!("- Threshold cryptographic protocol structure");
    println!("- Ready for Aura extension integration");
    println!("- Production-ready message type definitions");

    println!("\n=== Protocol Overview ===");
    println!("Threshold signing ceremony implementing FROST-style threshold signatures:");
    println!("- 1 Coordinator manages the ceremony");
    println!("- Signer[N] dynamic roles - configurable number of signers");
    println!("- 5 distinct phases ensure security and correctness");

    println!("\n=== Protocol Phases ===");
    println!("Phase 1: Ceremony Initiation");
    println!("  └─ Coordinator → Signer[*]: Broadcast ceremony parameters to all signers");
    println!();
    println!("Phase 2: Commitment Collection");
    println!("  └─ Signer[*] → Coordinator: All signers send commitments in parallel");
    println!();
    println!("Phase 3: Commitment Aggregation");
    println!("  ├─ Coordinator aggregates all received commitments");
    println!("  └─ Coordinator → Signer[*]: Broadcast aggregated result to all signers");
    println!();
    println!("Phase 4: Signature Share Collection");
    println!("  └─ Signer[*] → Coordinator: All signers submit signature shares");
    println!();
    println!("Phase 5: Final Signature Distribution");
    println!("  ├─ Coordinator aggregates signature shares");
    println!("  └─ Coordinator → Signer[*]: Broadcast final signature to all signers");

    println!("\n=== Future Aura Extensions ===");
    println!("Capability Guards:");
    println!("   - 'coordinate_threshold_signing' - Only authorized coordinators");
    println!("   - 'participate_threshold_signing' - Only trusted signers");
    println!("   - 'aggregate_commitments' - Coordinator-specific operation");
    println!();
    println!("Flow Cost Management:");
    println!("   - Ceremony initiation: 300 units per signer");
    println!("   - Commitment phase: 200 units per commitment");
    println!("   - Signature shares: 300 units per share");
    println!();
    println!("Journal Facts & Auditing:");
    println!("   - 'ceremony_initiated' - Tracks ceremony start");
    println!("   - 'commitment_sent' - Records each commitment");
    println!("   - 'ceremony_completed' - Final completion record");

    println!("\n=== Security Properties ===");
    println!("- Threshold cryptography ensures no single point of failure");
    println!("- Dynamic roles support variable participant counts");
    println!("- Session types ensure correct message ordering");
    println!("- Choreographic projection prevents deadlocks");
    println!("- Type-safe message handling with Rust");
    println!("- Ready for capability-based authorization");

    println!("\n=== Integration Benefits ===");
    println!("Production deployment benefits:");
    println!("- Compatible with AuraHandler extension system");
    println!("- Ready for web-of-trust capability evaluation");
    println!("- Prepared for flow budget management");
    println!("- Supports distributed journal state tracking");
    println!("- Cryptographic effects integration points");

    println!("\n=== Example Complete ===");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_initiate_ceremony_creation() {
        let initiate = InitiateCeremony {
            ceremony_id: "ceremony_abc123".to_string(),
            message_hash: vec![0x01, 0x02, 0x03, 0x04],
            threshold: 2,
            participant_count: 3,
            timeout_ms: 30000,
        };

        assert_eq!(initiate.ceremony_id, "ceremony_abc123");
        assert_eq!(initiate.threshold, 2);
        assert_eq!(initiate.participant_count, 3);
        assert_eq!(initiate.message_hash.len(), 4);
    }

    #[test]
    fn test_signing_commitment_serialization() {
        let commitment = SigningCommitment {
            ceremony_id: "ceremony_xyz789".to_string(),
            participant_id: "signer_1".to_string(),
            nonce_commitment: vec![0xAA, 0xBB, 0xCC],
            proof_of_knowledge: vec![0x11, 0x22, 0x33, 0x44],
        };

        let serialized = serde_json::to_string(&commitment).unwrap();
        let deserialized: SigningCommitment = serde_json::from_str(&serialized).unwrap();

        assert_eq!(commitment.ceremony_id, deserialized.ceremony_id);
        assert_eq!(commitment.participant_id, deserialized.participant_id);
        assert_eq!(commitment.nonce_commitment, deserialized.nonce_commitment);
    }

    #[test]
    fn test_final_signature_success_case() {
        let final_sig = FinalSignature {
            ceremony_id: "ceremony_final".to_string(),
            aggregated_signature: vec![0xFF; 64], // 64-byte signature
            success: true,
            participating_ids: vec![
                "signer_1".to_string(),
                "signer_2".to_string(),
            ],
            completion_timestamp: 1640995200,
        };

        assert!(final_sig.success);
        assert_eq!(final_sig.participating_ids.len(), 2);
        assert_eq!(final_sig.aggregated_signature.len(), 64);
    }

    #[test]
    fn test_commitment_aggregation_ready() {
        let aggregation = CommitmentAggregation {
            ceremony_id: "test_ceremony".to_string(),
            aggregated_commitments: vec![0x12, 0x34, 0x56, 0x78],
            participant_list: vec!["signer_1".to_string(), "signer_2".to_string()],
            ready_to_sign: true,
        };

        assert!(aggregation.ready_to_sign);
        assert_eq!(aggregation.participant_list.len(), 2);
        assert_eq!(aggregation.aggregated_commitments.len(), 4);
    }
}
