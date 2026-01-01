//! Example demonstrating namespaced choreographic protocols.
//!
//! This example parses multiple protocols with different module namespaces
//! and shows their qualified names.

use rumpsteak_aura_choreography::compiler::parser::parse_choreography_str;

const THRESHOLD_SIGNATURE: &str = r#"
module threshold_ceremony exposing (ThresholdSignature)
protocol ThresholdSignature = {
    roles Coordinator, Signers[*]

    Coordinator -> Signers[*] : SigningRequest
    Signers[0..threshold] -> Coordinator : PartialSignature
    Coordinator -> Signers[*] : CompleteSignature
}
"#;

const KEY_RECOVERY: &str = r#"
module recovery exposing (KeyRecovery)
protocol KeyRecovery = {
    roles Requester, Guardians[*]

    Requester -> Guardians[*] : RecoveryRequest
    Guardians[0..recovery_threshold] -> Requester : KeyShare
    Requester -> Guardians[*] : RecoveryComplete
}
"#;

const CONSENSUS: &str = r#"
module consensus exposing (ByzantineFaultTolerant)
protocol ByzantineFaultTolerant = {
    roles Leader, Replicas[*]

    Leader -> Replicas[*] : PrepareRequest
    Replicas[0..quorum] -> Leader : PrepareResponse

    Leader -> Replicas[*] : CommitRequest
    Replicas[0..quorum] -> Leader : CommitResponse
}
"#;

fn main() {
    let protocols = [
        parse_choreography_str(THRESHOLD_SIGNATURE).expect("threshold protocol should parse"),
        parse_choreography_str(KEY_RECOVERY).expect("recovery protocol should parse"),
        parse_choreography_str(CONSENSUS).expect("consensus protocol should parse"),
    ];

    println!("Namespaced protocols example");
    println!("Three independent protocols with different namespaces:");
    for choreo in protocols {
        println!("- {}", choreo.qualified_name());
    }
    println!();
    println!("Each protocol is isolated in its own namespace,");
    println!("preventing naming conflicts and enabling modular design.");
}
