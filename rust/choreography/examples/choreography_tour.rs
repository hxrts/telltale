#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

//! End-to-End Choreography Tour
//!
//! This example provides a comprehensive tour of telltale's choreographic
//! programming features, demonstrating the complete flow from DSL to local types:
//!
//! 1. Module namespace support - organize protocols in modules
//! 2. Choice syntax - branching with explicit decider roles
//! 3. Dynamic roles - runtime-determined participant counts
//! 4. Range syntax - address subsets of dynamic roles
//! 5. Cross-feature integration - combining all features
//! 6. **Projection** - DSL → Parse → Project to local session types

use telltale_choreography::compiler::parser::parse_choreography_str;
use telltale_choreography::compiler::projection::project;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("╔════════════════════════════════════════════════════════════╗");
    println!("║       Telltale - End-to-End Choreography Tour        ║");
    println!("╚════════════════════════════════════════════════════════════╝");
    println!();

    demo_namespace_support()?;
    demo_choice_syntax()?;
    demo_dynamic_roles()?;
    demo_range_syntax()?;
    demo_integration()?;
    demo_projection()?;

    println!("All features demonstrated successfully!");
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
        print!("   • {}: ", role.name());
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

fn demo_projection() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== 6. End-to-End: DSL → Parse → Project ===");

    // A simple protocol to demonstrate projection
    let protocol = r#"
        protocol RequestResponse = {
            roles Client, Server

            Client -> Server : Request
            Server -> Client : Response
        }
    "#;

    // Step 1: Parse the DSL
    let choreography = parse_choreography_str(protocol)?;
    println!("Step 1 - Parsed choreography: {}", choreography.name);
    println!(
        "   Roles: {:?}",
        choreography
            .roles
            .iter()
            .map(|r| r.name())
            .collect::<Vec<_>>()
    );

    // Step 2: Project to local types for each role
    println!("\nStep 2 - Project to local types:");
    for role in &choreography.roles {
        let local_type = project(&choreography, role)?;
        println!("\n   {} sees:", role.name());
        println!("   {:#?}", local_type);
    }

    // Show a more complex example with choice
    println!("\n--- Choice Protocol Projection ---");
    let choice_protocol = r#"
        protocol AuthFlow = {
            roles Client, Server

            Client -> Server : LoginRequest
            choice at Server {
                success -> {
                    Server -> Client : AuthToken
                }
                failure -> {
                    Server -> Client : AuthError
                }
            }
        }
    "#;

    let auth_choreo = parse_choreography_str(choice_protocol)?;
    println!("Parsed: {}", auth_choreo.name);

    for role in &auth_choreo.roles {
        let local_type = project(&auth_choreo, role)?;
        println!("\n   {} local type:", role.name());
        println!("   {:#?}", local_type);
    }

    println!();
    Ok(())
}
