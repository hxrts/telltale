//! Example demonstrating dynamic role count support
//!
//! This example shows different types of dynamic role parameterization
//! for protocols with runtime-determined participant counts.

use rumpsteak_aura_choreography_macros::choreography;

// Threshold signature protocol with runtime participant count
choreography! {
    #[namespace = "threshold_crypto"]
    ThresholdSignature {
        roles: Coordinator, Signers[*];
        
        // Coordinator broadcasts signing request to all signers
        [@phase = "request"]
        Coordinator -> Signers[*]: SigningRequest;
        
        // Only enough signers for threshold respond
        [@phase = "response"]
        Signers[0..threshold] -> Coordinator: PartialSignature;
        
        // Coordinator broadcasts final signature
        [@phase = "completion"]
        Coordinator -> Signers[*]: FinalSignature;
    }
}

// Consensus protocol with symbolic parameters
choreography! {
    #[namespace = "consensus"]
    PracticalByzantineFaultTolerance {
        roles: Primary, Backups[N];
        
        // Pre-prepare phase: Primary sends to all backups
        Primary -> Backups[*]: PrePrepare;
        
        // Prepare phase: Backups communicate among themselves
        Backups[i] -> Backups[*]: Prepare;
        
        // Commit phase: Backups respond to primary when consensus reached
        Backups[0..byzantine_threshold] -> Primary: Commit;
        
        // Primary confirms consensus
        Primary -> Backups[*]: CommitConfirmation;
    }
}

// Multi-party computation with range operations
choreography! {
    #[namespace = "secure_computation"]
    SecretSharing {
        roles: Dealer, Participants[*];
        
        // Dealer distributes secret shares
        [@security = "information_theoretic"]
        Dealer -> Participants[*]: SecretShare;
        
        // Participants verify shares among subset
        Participants[i] -> Participants[i+1..i+verification_window]: VerificationChallenge;
        
        // Subset responds with verification
        Participants[0..verification_count] -> Dealer: VerificationResponse;
        
        choice Dealer {
            accept: {
                Dealer -> Participants[*]: SharesAccepted;
            }
            reject: {
                Dealer -> Participants[*]: SharesRejected;
            }
        }
    }
}

// Load balancer with dynamic worker pool
choreography! {
    #[namespace = "load_balancing"]
    DynamicLoadBalancer {
        roles: LoadBalancer, Workers[*], HealthChecker;
        
        // Health checker monitors worker availability
        HealthChecker -> Workers[*]: HealthCheck;
        Workers[0..available_count] -> HealthChecker: HealthStatus;
        HealthChecker -> LoadBalancer: WorkerAvailability;
        
        // Load balancer distributes work
        LoadBalancer -> Workers[0..active_workers]: WorkUnit;
        
        // Workers process and respond
        Workers[i] -> LoadBalancer: WorkResult;
        
        loop (decides: LoadBalancer) {
            // Continuous load monitoring
            LoadBalancer -> HealthChecker: RequestHealthCheck;
            HealthChecker -> Workers[*]: PingCheck;
            Workers[0..responsive_count] -> HealthChecker: PongResponse;
            HealthChecker -> LoadBalancer: HealthReport;
        }
    }
}

fn main() {
    println!("Dynamic Role Count Support Example");
    println!("==================================");
    println!();
    
    println!("1. ThresholdSignature Protocol:");
    println!("   - Signers[*]: Runtime-determined number of signers");
    println!("   - Signers[0..threshold]: Only threshold number respond");
    println!("   - Enables flexible threshold cryptography");
    println!();
    
    println!("2. PracticalByzantineFaultTolerance:");
    println!("   - Backups[N]: Symbolic parameter for compile-time flexibility");
    println!("   - Backups[i] -> Backups[*]: Participant-to-all communication");
    println!("   - Supports variable Byzantine fault tolerance requirements");
    println!();
    
    println!("3. SecretSharing Protocol:");
    println!("   - Participants[i+1..i+verification_window]: Range expressions");
    println!("   - Participants[0..verification_count]: Subset selection");
    println!("   - Enables secure multi-party computation protocols");
    println!();
    
    println!("4. DynamicLoadBalancer:");
    println!("   - Workers[0..available_count]: Dynamic availability");
    println!("   - Workers[0..active_workers]: Runtime work distribution");
    println!("   - Demonstrates elastic scaling scenarios");
    println!();
    
    println!("Security Features:");
    println!("- Maximum role count: 10,000 (prevents overflow attacks)");
    println!("- Runtime bounds checking for all dynamic operations");
    println!("- Type-safe role parameter resolution");
    println!("- Comprehensive validation at compile and runtime");
}