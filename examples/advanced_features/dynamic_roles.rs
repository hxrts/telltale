//! Example demonstrating dynamic role count support.
//!
//! This example parses protocols using the DSL string parser so dynamic roles
//! and range expressions are fully supported.

use rumpsteak_aura_choreography::compiler::parser::parse_choreography_str;

const THRESHOLD_SIGNATURE: &str = r#"
module threshold_crypto exposing (ThresholdSignature)
protocol ThresholdSignature = {
    roles Coordinator, Signers[*]

    Coordinator -> Signers[*] : SigningRequest
    Signers[0..threshold] -> Coordinator : PartialSignature
    Coordinator -> Signers[*] : FinalSignature
}
"#;

const PBFT: &str = r#"
module consensus exposing (PracticalByzantineFaultTolerance)
protocol PracticalByzantineFaultTolerance = {
    roles Primary, Backups[N]

    Primary -> Backups[*] : PrePrepare
    Backups[i] -> Backups[*] : Prepare
    Backups[0..byzantine_threshold] -> Primary : Commit
    Primary -> Backups[*] : CommitConfirmation
}
"#;

const SECRET_SHARING: &str = r#"
module secure_computation exposing (SecretSharing)
protocol SecretSharing = {
    roles Dealer, Participants[*]

    Dealer -> Participants[*] : SecretShare
    Participants[i] -> Participants[i+1..i+verification_window] : VerificationChallenge
    Participants[0..verification_count] -> Dealer : VerificationResponse

    choice at Dealer {
        accept -> {
            Dealer -> Participants[*] : SharesAccepted
        }
        reject -> {
            Dealer -> Participants[*] : SharesRejected
        }
    }
}
"#;

const LOAD_BALANCER: &str = r#"
module load_balancing exposing (DynamicLoadBalancer)
protocol DynamicLoadBalancer = {
    roles LoadBalancer, Workers[*], HealthChecker

    HealthChecker -> Workers[*] : HealthCheck
    Workers[0..available_count] -> HealthChecker : HealthStatus
    HealthChecker -> LoadBalancer : WorkerAvailability

    LoadBalancer -> Workers[0..active_workers] : WorkUnit
    Workers[i] -> LoadBalancer : WorkResult

    loop decide by LoadBalancer {
        LoadBalancer -> HealthChecker : RequestHealthCheck
        HealthChecker -> Workers[*] : PingCheck
        Workers[0..responsive_count] -> HealthChecker : PongResponse
        HealthChecker -> LoadBalancer : HealthReport
    }
}
"#;

fn main() {
    println!("Dynamic Role Count Support Example");
    println!("==================================");

    for (name, src) in [
        ("ThresholdSignature", THRESHOLD_SIGNATURE),
        ("PracticalByzantineFaultTolerance", PBFT),
        ("SecretSharing", SECRET_SHARING),
        ("DynamicLoadBalancer", LOAD_BALANCER),
    ] {
        let choreo = parse_choreography_str(src).expect("Protocol should parse");
        println!("Parsed {} with {} roles", name, choreo.roles.len());
    }
}
