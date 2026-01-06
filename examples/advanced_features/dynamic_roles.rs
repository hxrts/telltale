//! Example demonstrating dynamic role count support.
//!
//! This example shows two aspects of dynamic roles:
//! 1. DSL parsing of protocols with wildcards and ranges
//! 2. Runtime resolution of role families using TestAdapter

use rumpsteak_aura_choreography::compiler::parser::parse_choreography_str;
use rumpsteak_aura_choreography::effects::{LabelId, RoleId};
use rumpsteak_aura_choreography::identifiers::RoleName;
use rumpsteak_aura_choreography::runtime::adapter::ChoreographicAdapter;
use rumpsteak_aura_choreography::runtime::test_adapter::TestAdapter;

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

// Role and Label types for runtime demonstration
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
enum SignerRole {
    Coordinator,
    Signer(u32),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
enum SignerLabel {
    Sign,
}

impl LabelId for SignerLabel {
    fn as_str(&self) -> &'static str {
        "Sign"
    }
    fn from_str(s: &str) -> Option<Self> {
        if s == "Sign" {
            Some(SignerLabel::Sign)
        } else {
            None
        }
    }
}

impl RoleId for SignerRole {
    type Label = SignerLabel;

    fn role_name(&self) -> RoleName {
        match self {
            SignerRole::Coordinator => RoleName::from_static("Coordinator"),
            SignerRole::Signer(_) => RoleName::from_static("Signer"),
        }
    }

    fn role_index(&self) -> Option<u32> {
        match self {
            SignerRole::Signer(idx) => Some(*idx),
            _ => None,
        }
    }
}

fn main() {
    println!("Dynamic Role Count Support Example");
    println!("==================================\n");

    // Part 1: DSL Parsing
    println!("Part 1: DSL Parsing");
    println!("-------------------");
    for (name, src) in [
        ("ThresholdSignature", THRESHOLD_SIGNATURE),
        ("PracticalByzantineFaultTolerance", PBFT),
        ("SecretSharing", SECRET_SHARING),
        ("DynamicLoadBalancer", LOAD_BALANCER),
    ] {
        let choreo = parse_choreography_str(src).expect("Protocol should parse");
        println!("  Parsed {} with {} roles", name, choreo.roles.len());
    }

    // Part 2: Runtime Resolution
    println!("\nPart 2: Runtime Resolution");
    println!("--------------------------");

    // Create adapter with 5 signers
    let signers: Vec<SignerRole> = (0..5).map(SignerRole::Signer).collect();
    let adapter = TestAdapter::new(SignerRole::Coordinator).with_family("Signer", signers);

    // Resolve all signers
    let all = adapter.resolve_family("Signer").expect("resolve_family");
    println!("  resolve_family(\"Signer\") -> {} roles", all.len());

    // Resolve a threshold subset (first 3 signers)
    let threshold = adapter
        .resolve_range("Signer", 0, 3)
        .expect("resolve_range");
    println!("  resolve_range(\"Signer\", 0, 3) -> {} roles", threshold.len());

    // Get family size
    let size = adapter.family_size("Signer").expect("family_size");
    println!("  family_size(\"Signer\") -> {}", size);

    println!("\nAll dynamic role operations completed successfully!");
}
