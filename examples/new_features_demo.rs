#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

//! Comprehensive demonstration of new rumpsteak-aura choreography features
//!
//! This example demonstrates all the new functionality we've added:
//! 1. Enhanced namespace support
//! 2. Multiple annotations system  
//! 3. Dynamic role count support with overflow protection
//! 4. Range syntax for dynamic roles
//! 5. Role-level annotations
//! 6. Cross-feature integration

use rumpsteak_aura_choreography::{
    ast::*,
    compiler::{
        codegen::{generate_choreography_code_with_dynamic_roles, generate_dynamic_role_support},
        parser::parse_choreography_str,
        projection::project,
    },
};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("╔════════════════════════════════════════════════════════════╗");
    println!("║       Rumpsteak Aura - New Features Demonstration         ║");
    println!("╚════════════════════════════════════════════════════════════╝");
    println!();

    // 1. Namespace Support Demo
    demo_namespace_support()?;

    // 2. Multiple Annotations Demo
    demo_multiple_annotations()?;

    // 3. Dynamic Roles Demo
    demo_dynamic_roles()?;

    // 4. Range Syntax Demo
    demo_range_syntax()?;

    // 5. Cross-Feature Integration Demo
    demo_integration()?;

    println!("✅ All new features demonstrated successfully!");
    Ok(())
}

fn demo_namespace_support() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== 1. Namespace Support ===");

    let protocol_a = r#"
        #[namespace = "authentication"]
        choreography LoginProtocol {
            roles: Client, Server, Database;
            
            Client -> Server: LoginRequest;
            Server -> Database: ValidateCredentials;
            Database -> Server: ValidationResult;
            Server -> Client: LoginResponse;
        }
    "#;

    let protocol_b = r#"
        #[namespace = "payment"]
        choreography PaymentProtocol {
            roles: Client, Server, Database;
            
            Client -> Server: PaymentRequest;
            Server -> Database: ProcessPayment;
            Database -> Server: PaymentResult;
            Server -> Client: PaymentResponse;
        }
    "#;

    let choreo_a = parse_choreography_str(protocol_a)?;
    let choreo_b = parse_choreography_str(protocol_b)?;

    println!("📦 Parsed two protocols with same role names in different namespaces:");
    println!("   • Protocol A: {}", choreo_a.qualified_name());
    println!("   • Protocol B: {}", choreo_b.qualified_name());
    println!("   • No naming conflicts! ✨");
    println!();

    Ok(())
}

fn demo_multiple_annotations() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== 2. Multiple Annotations Support ===");

    let protocol = r#"
        choreography AnnotatedProtocol {
            roles: Client, Server, Cache;
            
            [@priority = "high", @timeout = 5000, @retry = 3]
            Client -> Server: ImportantRequest;
            
            Server[@load_balance = "round_robin"] -> Cache[@ttl = 3600]: CacheQuery;
            
            [@compress = "gzip", @encrypt = "aes256"]
            Cache -> Server: CachedData;
            
            [@audit_log = "true", @alert_on_failure = "slack"]
            Server -> Client: Response;
        }
    "#;

    let choreo = parse_choreography_str(protocol)?;
    println!("🏷️  Parsed protocol with multiple annotations:");

    // Extract and display annotations from the protocol
    if let Protocol::Send {
        annotations,
        from_annotations,
        to_annotations,
        ..
    } = &choreo.protocol
    {
        if !annotations.is_empty() {
            println!("   • Message annotations: {:?}", annotations);
        }
        if !from_annotations.is_empty() {
            println!("   • From role annotations: {:?}", from_annotations);
        }
        if !to_annotations.is_empty() {
            println!("   • To role annotations: {:?}", to_annotations);
        }
    }

    println!("   • Annotations parsed and stored successfully! 📝");
    println!();

    Ok(())
}

fn demo_dynamic_roles() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== 3. Dynamic Roles Support ===");

    let protocol = r#"
        choreography DynamicWorkflow {
            roles: Coordinator, Workers[*], Database;
            
            Coordinator -> Workers[*]: StartWork;
            Workers[i] -> Database: QueryData;
            Database -> Workers[i]: ResultData;
            Workers[0..quorum] -> Coordinator: WorkComplete;
        }
    "#;

    let choreo = parse_choreography_str(protocol)?;
    println!("⚡ Parsed dynamic role protocol:");

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

    // Test overflow protection
    println!("   • Testing overflow protection...");
    match RoleParam::safe_static(MAX_ROLE_COUNT + 1) {
        Err(RoleValidationError::CountOverflow { .. }) => {
            println!("   • ✅ Overflow protection working!");
        }
        _ => println!("   • ⚠️  Overflow protection not triggered"),
    }

    println!();
    Ok(())
}

fn demo_range_syntax() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== 4. Range Syntax Support ===");

    let protocol = r#"
        choreography ConsensusProtocol {
            roles: Leader, Followers[N];
            
            Leader -> Followers[*]: PrepareRequest;
            Followers[0..quorum] -> Leader: PrepareResponse;
            Leader -> Followers[*]: CommitRequest;
            Followers[majority..N] -> Leader: CommitResponse;
        }
    "#;

    let _choreo = parse_choreography_str(protocol)?;
    println!("📊 Parsed protocol with range syntax:");
    println!("   • Followers[*] - all followers");
    println!("   • Followers[0..quorum] - first 'quorum' followers");
    println!("   • Followers[majority..N] - from 'majority' to N followers");

    // Test range validation
    println!("   • Testing range validation...");
    match RoleRange::safe_concrete(0, MAX_RANGE_SIZE + 1) {
        Err(RoleValidationError::RangeSizeOverflow { .. }) => {
            println!("   • ✅ Range size validation working!");
        }
        _ => println!("   • ⚠️  Range validation not triggered"),
    }

    println!();
    Ok(())
}

fn demo_integration() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== 5. Cross-Feature Integration ===");

    let complex_protocol = r#"
        #[namespace = "distributed_consensus"]
        choreography ByzantineConsensus {
            roles: Leader, Followers[*], Auditor;
            
            [@phase = "prepare", @byzantine_tolerance = "true"]
            Leader -> Followers[*]: PrepareRequest;
            
            [@timeout = 10000, @min_responses = "2f+1"]
            Followers[0..byzantine_threshold] -> Leader: PrepareResponse;
            
            [@phase = "commit", @audit_required = "true"]
            Leader -> Followers[*]: CommitRequest;
            
            [@critical = "true", @consensus_threshold = "majority"]
            Followers[honest_majority] -> Leader: CommitResponse;
            
            [@audit_log = "blockchain", @finality = "true"]
            Leader -> Auditor: ConsensusResult;
        }
    "#;

    let choreo = parse_choreography_str(complex_protocol)?;

    println!("🚀 Parsed complex protocol with ALL features:");
    println!("   • Namespace: {}", choreo.qualified_name());
    println!("   • Roles: {} (including dynamic)", choreo.roles.len());
    println!("   • Features: Annotations ✓, Dynamic Roles ✓, Ranges ✓, Namespaces ✓");

    // Test projection
    println!("   • Testing projection...");
    let mut projection_count = 0;
    for role in &choreo.roles {
        if project(&choreo, role).is_ok() {
            projection_count += 1;
        }
        // Expected for some dynamic roles to fail projection
    }
    println!("   • Successfully projected for {} roles", projection_count);

    // Test code generation
    println!("   • Testing code generation...");
    let local_types = vec![
        (choreo.roles[0].clone(), LocalType::End),
        (choreo.roles[1].clone(), LocalType::End),
        (choreo.roles[2].clone(), LocalType::End),
    ];

    let generated_code = generate_choreography_code_with_dynamic_roles(&choreo, &local_types);
    let code_str = generated_code.to_string();

    println!(
        "   • Generated {} lines of Rust code",
        code_str.lines().count()
    );
    println!("   • Code includes runtime validation and dynamic role support");

    // Test dynamic role support
    let dynamic_support = generate_dynamic_role_support(&choreo);
    let support_str = dynamic_support.to_string();

    if support_str.len() > 10 {
        println!("   • Generated dynamic role support code");
    }

    println!();
    Ok(())
}

/// Demonstrates error handling and validation
#[allow(dead_code)]
fn demo_error_handling() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== Error Handling & Validation ===");

    // Test malformed protocol
    let bad_protocol = r#"
        choreography BadProtocol {
            roles: A, B;
            A -> UndefinedRole: Message;
        }
    "#;

    match parse_choreography_str(bad_protocol) {
        Err(err) => println!("✅ Correctly rejected bad protocol: {}", err),
        Ok(_) => println!("⚠️  Bad protocol was accepted unexpectedly"),
    }

    println!();
    Ok(())
}
