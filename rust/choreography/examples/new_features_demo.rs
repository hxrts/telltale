#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

//! Comprehensive demonstration of new rumpsteak-aura choreography features
//!
//! This example demonstrates all the new functionality:
//! 1. Module namespace support
//! 2. Choice syntax
//! 3. Dynamic role count support with overflow protection
//! 4. Range syntax for dynamic roles
//! 5. Cross-feature integration

use rumpsteak_aura_choreography::compiler::parser::parse_choreography_str;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("╔════════════════════════════════════════════════════════════╗");
    println!("║       Rumpsteak Aura - New Features Demonstration          ║");
    println!("╚════════════════════════════════════════════════════════════╝");
    println!();

    demo_namespace_support()?;
    demo_choice_syntax()?;
    demo_dynamic_roles()?;
    demo_range_syntax()?;
    demo_integration()?;

    println!("All new features demonstrated successfully!");
    Ok(())
}

fn demo_namespace_support() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== 1. Namespace Support ===");

    let protocol_a = r#"
        module authentication exposing (LoginProtocol)
        protocol LoginProtocol = {
            roles Client, Server, Database

            Client -> Server : LoginRequest
            Server -> Database : ValidateCredentials
            Database -> Server : ValidationResult
            Server -> Client : LoginResponse
        }
    "#;

    let protocol_b = r#"
        module payment exposing (PaymentProtocol)
        protocol PaymentProtocol = {
            roles Client, Server, Database

            Client -> Server : PaymentRequest
            Server -> Database : ProcessPayment
            Database -> Server : PaymentResult
            Server -> Client : PaymentResponse
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

fn demo_choice_syntax() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== 2. Choice Syntax ===");

    let protocol = r#"
        protocol ShoppingFlow = {
            roles Client, Server

            choice at Client {
                buy -> {
                    Client -> Server : Purchase
                }
                cancel -> {
                    Client -> Server : Cancel
                }
            }
        }
    "#;

    let _choreo = parse_choreography_str(protocol)?;
    println!("Parsed protocol with choice branches:");
    println!("   • Explicit decider role with 'choice at'");
    println!("   • Labelled branches with 'label -> {{ ... }}'");
    println!();

    Ok(())
}

fn demo_dynamic_roles() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== 3. Dynamic Roles Support ===");

    let protocol = r#"
        protocol DynamicWorkflow = {
            roles Coordinator, Workers[*], Database

            Coordinator -> Workers[*] : StartWork
            Workers[i] -> Database : QueryData
            Database -> Workers[i] : ResultData
            Workers[0..quorum] -> Coordinator : WorkComplete
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
        protocol ConsensusProtocol = {
            roles Leader, Followers[N]

            Leader -> Followers[*] : PrepareRequest
            Followers[0..quorum] -> Leader : PrepareResponse
            Leader -> Followers[*] : CommitRequest
            Followers[majority..N] -> Leader : CommitResponse
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
        module distributed_consensus exposing (ByzantineConsensus)
        protocol ByzantineConsensus = {
            roles Leader, Followers[*], Auditor

            Leader -> Followers[*] : PrepareRequest

            Followers[0..byzantine_threshold] -> Leader : PrepareResponse

            Leader -> Followers[*] : CommitRequest

            Followers[honest_majority] -> Leader : CommitResponse

            Leader -> Auditor : ConsensusResult
        }
    "#;

    let choreo = parse_choreography_str(complex_protocol)?;

    println!("Parsed complex protocol with multiple features:");
    println!("   • Namespace: {}", choreo.qualified_name());
    println!("   • Roles: {} (including dynamic)", choreo.roles.len());
    println!("   • Features: Dynamic Roles (yes), Ranges (yes), Namespaces (yes)");
    println!("   • Successfully demonstrated all advanced features together");
    println!();

    Ok(())
}
