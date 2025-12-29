#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

//! Comprehensive demonstration of new rumpsteak-aura choreography features
//!
//! This example demonstrates all the new functionality:
//! 1. Enhanced namespace support
//! 2. Multiple annotations system
//! 3. Dynamic role count support with overflow protection
//! 4. Range syntax for dynamic roles
//! 5. Role-level annotations
//! 6. Cross-feature integration

use rumpsteak_aura_choreography::compiler::parser::parse_choreography_str;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("╔════════════════════════════════════════════════════════════╗");
    println!("║       Rumpsteak Aura - New Features Demonstration          ║");
    println!("╚════════════════════════════════════════════════════════════╝");
    println!();

    demo_namespace_support()?;
    demo_multiple_annotations()?;
    demo_dynamic_roles()?;
    demo_range_syntax()?;
    demo_integration()?;

    println!("All new features demonstrated successfully!");
    Ok(())
}

fn demo_namespace_support() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== 1. Namespace Support ===");

    let protocol_a = r#"
        #[namespace = "authentication"]
        choreography LoginProtocol {
            roles: Client, Server, Database

            Client -> Server: LoginRequest
            Server -> Database: ValidateCredentials
            Database -> Server: ValidationResult
            Server -> Client: LoginResponse
        }
    "#;

    let protocol_b = r#"
        #[namespace = "payment"]
        choreography PaymentProtocol {
            roles: Client, Server, Database

            Client -> Server: PaymentRequest
            Server -> Database: ProcessPayment
            Database -> Server: PaymentResult
            Server -> Client: PaymentResponse
        }
    "#;

    let choreo_a = parse_choreography_str(protocol_a)?;
    let choreo_b = parse_choreography_str(protocol_b)?;

    println!("Parsed two protocols with same role names in different namespaces:");
    println!("   • Protocol A: {}", choreo_a.qualified_name());
    println!("   • Protocol B: {}", choreo_b.qualified_name());
    println!("   • No naming conflicts!");
    println!();

    Ok(())
}

fn demo_multiple_annotations() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== 2. Multiple Annotations Support ===");

    let protocol = r#"
        choreography AnnotatedProtocol {
            roles: Client, Server, Cache

            [@priority = "high", @timeout = 5000, @retry = 3]
            Client -> Server: ImportantRequest

            Server[@load_balance = "round_robin"] -> Cache[@ttl = 3600]: CacheQuery

            [@compress = "gzip", @encrypt = "aes256"]
            Cache -> Server: CachedData

            [@audit_log = "true", @alert_on_failure = "slack"]
            Server -> Client: Response
        }
    "#;

    let _choreo = parse_choreography_str(protocol)?;
    println!("Parsed protocol with multiple annotations:");
    println!("   • Statement-level annotations supported");
    println!("   • Role-level annotations supported");
    println!("   • Multiple annotations per statement supported");
    println!("   • Annotations parsed and stored successfully!");
    println!();

    Ok(())
}

fn demo_dynamic_roles() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== 3. Dynamic Roles Support ===");

    let protocol = r#"
        choreography DynamicWorkflow {
            roles: Coordinator, Workers[*], Database

            Coordinator -> Workers[*]: StartWork
            Workers[i] -> Database: QueryData
            Database -> Workers[i]: ResultData
            Workers[0..quorum] -> Coordinator: WorkComplete
        }
    "#;

    let choreo = parse_choreography_str(protocol)?;
    println!("Parsed dynamic role protocol:");

    for role in &choreo.roles {
        print!("   • {}: ", role.name);
        if role.is_dynamic() {
            println!("Dynamic role (runtime count)");
        } else if role.is_symbolic() {
            println!("Symbolic role (parameterized)");
        } else if role.is_parameterized() {
            println!("Parameterized role");
        } else {
            println!("Static role");
        }
    }

    println!();
    Ok(())
}

fn demo_range_syntax() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== 4. Range Syntax Support ===");

    let protocol = r#"
        choreography ConsensusProtocol {
            roles: Leader, Followers[N]

            Leader -> Followers[*]: PrepareRequest
            Followers[0..quorum] -> Leader: PrepareResponse
            Leader -> Followers[*]: CommitRequest
            Followers[majority..N] -> Leader: CommitResponse
        }
    "#;

    let _choreo = parse_choreography_str(protocol)?;
    println!("Parsed protocol with range syntax:");
    println!("   • Followers[*] - all followers");
    println!("   • Followers[0..quorum] - first 'quorum' followers");
    println!("   • Followers[majority..N] - from 'majority' to N followers");
    println!();

    Ok(())
}

fn demo_integration() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== 5. Cross-Feature Integration ===");

    let complex_protocol = r#"
        #[namespace = "distributed_consensus"]
        choreography ByzantineConsensus {
            roles: Leader, Followers[*], Auditor

            [@phase = "prepare", @byzantine_tolerance = "true"]
            Leader -> Followers[*]: PrepareRequest

            [@timeout = 10000, @min_responses = "2f+1"]
            Followers[0..byzantine_threshold] -> Leader: PrepareResponse

            [@phase = "commit", @audit_required = "true"]
            Leader -> Followers[*]: CommitRequest

            [@critical = "true", @consensus_threshold = "majority"]
            Followers[honest_majority] -> Leader: CommitResponse

            [@audit_log = "blockchain", @finality = "true"]
            Leader -> Auditor: ConsensusResult
        }
    "#;

    let choreo = parse_choreography_str(complex_protocol)?;

    println!("Parsed complex protocol with ALL features:");
    println!("   • Namespace: {}", choreo.qualified_name());
    println!("   • Roles: {} (including dynamic)", choreo.roles.len());
    println!(
        "   • Features: Annotations (yes), Dynamic Roles (yes), Ranges (yes), Namespaces (yes)"
    );
    println!("   • Successfully demonstrated all advanced features together");
    println!();

    Ok(())
}
