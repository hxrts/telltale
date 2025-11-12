//! Example demonstrating namespaced choreographic protocols
//!
//! This example shows how multiple choreographies with different namespaces
//! can coexist in the same crate without conflicts.

use rumpsteak_aura_choreography_macros::choreography;

// Threshold signature ceremony protocol
mod threshold_ceremony {
    use super::*;
    
    choreography! {
        #[namespace = "threshold_ceremony"]
        ThresholdSignature {
            roles: Coordinator, Signers[*];
            
            // Coordinator initiates the signing process
            Coordinator -> Signers[*]: SigningRequest;
            
            // Signers respond with partial signatures
            Signers[0..threshold] -> Coordinator: PartialSignature;
            
            // Coordinator broadcasts the combined signature
            Coordinator -> Signers[*]: CompleteSignature;
        }
    }
}

// Key recovery protocol
mod recovery_protocol {
    use super::*;
    
    choreography! {
        #[namespace = "recovery"]
        KeyRecovery {
            roles: Requester, Guardians[*];
            
            // Requester initiates recovery
            Requester -> Guardians[*]: RecoveryRequest;
            
            // Guardians verify and provide shares
            Guardians[0..recovery_threshold] -> Requester: KeyShare;
            
            // Requester acknowledges successful recovery
            Requester -> Guardians[*]: RecoveryComplete;
        }
    }
}

// Consensus protocol
mod consensus_protocol {
    use super::*;
    
    choreography! {
        #[namespace = "consensus"]
        ByzantineFaultTolerant {
            roles: Leader, Replicas[*];
            
            // Prepare phase
            Leader -> Replicas[*]: PrepareRequest;
            Replicas[0..quorum] -> Leader: PrepareResponse;
            
            // Commit phase
            Leader -> Replicas[*]: CommitRequest;
            Replicas[0..quorum] -> Leader: CommitResponse;
        }
    }
}

fn main() {
    println!("Namespaced protocols example");
    println!("Three independent protocols with different namespaces:");
    println!("- threshold_ceremony::ThresholdSignature");
    println!("- recovery::KeyRecovery");
    println!("- consensus::ByzantineFaultTolerant");
    println!();
    println!("Each protocol is isolated in its own namespace,");
    println!("preventing naming conflicts and enabling modular design.");
}