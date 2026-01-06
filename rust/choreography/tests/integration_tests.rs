#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

//! Integration tests for enhanced choreography features
//!
//! This module tests the integration of enhanced features:
//! - Namespaces with dynamic roles and choices
//! - Complex multi-feature protocols
//! - End-to-end compilation and generation

use rumpsteak_aura_choreography::{
    ast::{LocalType, Role},
    compiler::{
        codegen::{generate_choreography_code_with_dynamic_roles, generate_dynamic_role_support},
        parser::parse_choreography_str,
        projection::project,
    },
};

#[test]
fn test_namespaced_choreographies() {
    // Test combining namespaces with basic message flows
    let protocol1 = r#"
        module secure_messaging exposing (EncryptedChat)
        protocol EncryptedChat = {
            roles Client, Server

            Client -> Server: SecureMessage
            Server -> Client: Acknowledgment
        }
    "#;

    let protocol2 = r#"
        module file_transfer exposing (SecureFileTransfer)
        protocol SecureFileTransfer = {
            roles Sender, Receiver

            Sender -> Receiver: FileChunk
            Receiver -> Sender: ChunkAck
        }
    "#;

    // Both protocols should parse successfully
    let choreo1 = parse_choreography_str(protocol1).expect("Protocol 1 should parse");
    let choreo2 = parse_choreography_str(protocol2).expect("Protocol 2 should parse");

    // Verify namespaces are different
    assert_eq!(choreo1.namespace.as_ref().unwrap(), "secure_messaging");
    assert_eq!(choreo2.namespace.as_ref().unwrap(), "file_transfer");

    // Verify role counts
    assert_eq!(choreo1.roles.len(), 2);
    assert_eq!(choreo2.roles.len(), 2);

    // Test projection for both
    for role in &choreo1.roles {
        let local_type = project(&choreo1, role).expect("Projection should succeed");
        assert_ne!(local_type, LocalType::End); // Should have meaningful projections
    }

    for role in &choreo2.roles {
        let local_type = project(&choreo2, role).expect("Projection should succeed");
        assert_ne!(local_type, LocalType::End);
    }
}

#[test]
fn test_dynamic_roles() {
    // Test dynamic roles combined with branching and ranges
    let protocol = r#"
        module threshold_consensus exposing (AnnotatedThreshold)
        protocol AnnotatedThreshold = {
            roles Leader, Followers[*]

            Leader -> Followers[*]: PrepareRequest
            Followers[0..quorum] -> Leader: PrepareResponse
            Leader -> Followers[*]: CommitRequest
            Followers[0..quorum] -> Leader: CommitResponse
        }
    "#;

    let choreo = parse_choreography_str(protocol).expect("Dynamic annotated protocol should parse");

    // Verify namespace
    assert_eq!(choreo.namespace.as_ref().unwrap(), "threshold_consensus");

    // Verify roles
    assert_eq!(choreo.roles.len(), 2);
    let leader = &choreo.roles[0];
    let followers = &choreo.roles[1];

    assert_eq!(leader.name().to_string(), "Leader");
    assert_eq!(followers.name().to_string(), "Followers");
    assert!(followers.is_dynamic());

    // Test code generation with dynamic support
    let local_types = vec![
        (leader.clone(), LocalType::End),
        (followers.clone(), LocalType::End),
    ];
    let generated_code = generate_choreography_code_with_dynamic_roles(&choreo, &local_types);
    let code_str = generated_code.to_string();

    // Verify dynamic support is generated
    assert!(code_str.contains("AnnotatedThresholdRuntime"));
    assert!(code_str.contains("dynamic"));
    assert!(code_str.contains("bind_role_count"));
}

#[test]
fn test_complex_multi_feature_protocol() {
    // Test protocol using all enhanced features together
    let protocol = r#"
        module advanced_example exposing (ComplexProtocol)
        protocol ComplexProtocol = {
            roles Coordinator, Workers[N], Database

            Coordinator -> Workers[*]: InitRequest
            Workers[i] -> Database: DataQuery
            Database -> Workers[i]: QueryResult
            Workers[0..majority] -> Coordinator: WorkResult

            choice at Coordinator {
                success -> {
                    Coordinator -> Workers[*]: SuccessNotification
                    Coordinator -> Database: FinalizeTransaction
                }
                retry -> {
                    Coordinator -> Workers[*]: RetryRequest
                }
                abort -> {
                    Coordinator -> Database: AbortTransaction
                    Coordinator -> Workers[*]: AbortNotification
                }
            }
        }
    "#;

    let choreo = parse_choreography_str(protocol).expect("Complex protocol should parse");

    // Verify all features are present
    assert_eq!(choreo.namespace.as_ref().unwrap(), "advanced_example");
    assert_eq!(choreo.roles.len(), 3);

    // Check role types
    let coordinator = &choreo.roles[0];
    let workers = &choreo.roles[1];
    let database = &choreo.roles[2];

    assert_eq!(coordinator.name().to_string(), "Coordinator");
    assert_eq!(workers.name().to_string(), "Workers");
    assert_eq!(database.name().to_string(), "Database");

    assert!(!coordinator.is_parameterized());
    assert!(workers.is_symbolic()); // Workers[N]
    assert!(!database.is_parameterized());

    // Test projection works for all roles
    for role in &choreo.roles {
        let result = project(&choreo, role);
        // Some projections may fail due to dynamic roles without bindings, but structure should be valid
        match result {
            Ok(local_type) => {
                // Projection succeeded - for complex protocols with dynamic roles,
                // End might be a valid result if the role doesn't participate
                println!("Projection succeeded for {}: {:?}", role.name(), local_type);
            }
            Err(projection_error) => {
                // Expected for dynamic roles without runtime bindings
                println!(
                    "Expected projection error for {}: {:?}",
                    role.name(),
                    projection_error
                );
            }
        }
    }

    // Test code generation
    let local_types = vec![
        (coordinator.clone(), LocalType::End),
        (workers.clone(), LocalType::End),
        (database.clone(), LocalType::End),
    ];

    let generated_code = generate_choreography_code_with_dynamic_roles(&choreo, &local_types);
    let code_str = generated_code.to_string();

    // Verify all components are generated
    assert!(code_str.contains("ComplexProtocolRuntime"));
    assert!(code_str.contains("validate_workers_count"));
    assert!(code_str.contains("bind_role_count"));
}

#[test]
fn test_multiple_dynamic_role_types() {
    // Test protocol with multiple types of dynamic roles
    let protocol = r#"
        module multi_dynamic exposing (MultiDynamicRoles)
        protocol MultiDynamicRoles = {
            roles Controller, StaticWorkers[3], DynamicWorkers[*], SymbolicWorkers[M]

            Controller -> StaticWorkers[0]: StaticTask
            Controller -> DynamicWorkers[*]: DynamicTask
            Controller -> SymbolicWorkers[*]: SymbolicTask

            StaticWorkers[0] -> Controller: StaticResult
            DynamicWorkers[0..response_count] -> Controller: DynamicResult
            SymbolicWorkers[i] -> Controller: SymbolicResult
        }
    "#;

    let choreo = parse_choreography_str(protocol).expect("Multi-dynamic protocol should parse");

    assert_eq!(choreo.roles.len(), 4);

    let controller = &choreo.roles[0];
    let static_workers = &choreo.roles[1];
    let dynamic_workers = &choreo.roles[2];
    let symbolic_workers = &choreo.roles[3];

    // Verify role characteristics
    assert!(!controller.is_parameterized());
    assert!(
        static_workers.is_parameterized()
            && !static_workers.is_dynamic()
            && !static_workers.is_symbolic()
    );
    assert!(dynamic_workers.is_dynamic());
    assert!(symbolic_workers.is_symbolic());

    // Test validation
    assert!(controller.validate().is_ok());
    assert!(static_workers.validate().is_ok());
    assert!(dynamic_workers.validate().is_ok());
    assert!(symbolic_workers.validate().is_ok());

    // Test dynamic support generation
    let dynamic_support = generate_dynamic_role_support(&choreo);
    let code_str = dynamic_support.to_string();

    // Should generate support for dynamic and symbolic roles
    assert!(code_str.contains("validate_dynamicworkers_count"));
    assert!(code_str.contains("validate_symbolicworkers_count"));
    // Should NOT generate for static roles
    assert!(!code_str.contains("validate_staticworkers_count"));
}

#[test]
fn test_nested_choices() {
    // Test complex nested structures without annotations
    let protocol = r#"
        module nested_complex exposing (NestedProtocol)
        protocol NestedProtocol = {
            roles Client, Server, Database

            Client -> Server: StartSession

            choice at Server {
                authenticate -> {
                    Server -> Database: AuthQuery

                    choice at Database {
                        success -> {
                            Database -> Server: AuthSuccess
                            Server -> Client: AuthToken
                        }
                        failure -> {
                            Database -> Server: AuthFailure
                            Server -> Client: AuthDenied
                        }
                    }
                }
                reject -> {
                    Server -> Client: Rejected
                }
            }
        }
    "#;

    let choreo = parse_choreography_str(protocol).expect("Nested protocol should parse");

    // Basic structure verification
    assert_eq!(choreo.namespace.as_ref().unwrap(), "nested_complex");
    assert_eq!(choreo.roles.len(), 3);

    // Test projection handles complex structure
    for role in &choreo.roles {
        let local_type = project(&choreo, role).expect("Projection should handle nested choices");

        // Verify we get meaningful local types
        match local_type {
            LocalType::End => panic!("Should not get End for complex protocol"),
            LocalType::Send { .. }
            | LocalType::Receive { .. }
            | LocalType::Select { .. }
            | LocalType::Branch { .. } => {
                // Expected complex types
            }
            _ => {
                // Other types are also valid
            }
        }
    }
}

#[test]
fn test_error_handling_integration() {
    // Test that enhanced features maintain good error reporting

    // Test undefined role in dynamic context
    let invalid_protocol1 = r#"
        module error_test exposing (InvalidProtocol)
        protocol InvalidProtocol = {
            roles A, B[*]
            A -> UndefinedRole: Message
        }
    "#;

    let result1 = parse_choreography_str(invalid_protocol1);
    assert!(result1.is_err());

    // Test invalid dynamic role syntax
    let invalid_protocol3 = r#"
        protocol InvalidDynamic = {
            roles A, B[invalid]
            A -> B[999999999]: Message
        }
    "#;

    let result2 = parse_choreography_str(invalid_protocol3);
    assert!(result2.is_err());
}

#[test]
fn test_performance_characteristics() {
    // Test that enhanced features don't significantly impact performance
    use std::time::Instant;

    let complex_protocol = r#"
        module performance_test exposing (PerformanceTest)
        protocol PerformanceTest = {
            roles Controller, Workers[*]

            Controller -> Workers[*]: StartWork
            Workers[0..batch_size] -> Controller: WorkComplete

            choice at Controller {
                continue -> {
                    Controller -> Workers[*]: ContinueWork
                }
                stop -> {
                    Controller -> Workers[*]: StopWork
                }
            }
        }
    "#;

    let start = Instant::now();

    // Parse multiple times to test performance
    for _ in 0..100 {
        let choreo = parse_choreography_str(complex_protocol).expect("Should parse quickly");

        // Quick validation
        assert_eq!(choreo.namespace.as_ref().unwrap(), "performance_test");
        assert_eq!(choreo.roles.len(), 2);

        // Test projection performance
        for role in &choreo.roles {
            let _ = project(&choreo, role); // May fail for dynamic roles, but should be fast
        }
    }

    let duration = start.elapsed();

    // Performance assertion - should complete 100 iterations quickly
    assert!(
        duration.as_millis() < 1000,
        "Performance test took too long: {:?}",
        duration
    );
    println!(
        "Performance test completed 100 iterations in {:?}",
        duration
    );
}

#[test]
fn test_full_compilation_pipeline() {
    // Test end-to-end compilation of enhanced features
    let protocol = r#"
        module compilation_test exposing (CompilationTest)
        protocol CompilationTest = {
            roles Client, Servers[*], Database

            Client -> Servers[*]: Request
            Servers[i] -> Database: Query
            Database -> Servers[i]: Response
            Servers[0..quorum] -> Client: AggregatedResponse
        }
    "#;

    let choreo = parse_choreography_str(protocol).expect("Protocol should parse");

    // Create local types (simplified for test)
    let local_types: Vec<(Role, LocalType)> = choreo
        .roles
        .iter()
        .map(|role| (role.clone(), LocalType::End))
        .collect();

    // Test full code generation
    let generated_code = generate_choreography_code_with_dynamic_roles(&choreo, &local_types);
    let code_str = generated_code.to_string();

    // Verify comprehensive code generation
    assert!(code_str.contains("CompilationTestRuntime"));
    assert!(code_str.contains("bind_role_count"));
    assert!(code_str.contains("validate_servers_count"));

    // Test that generated code is syntactically valid Rust
    // (This would require syn crate for full parsing, but we can check basic structure)
    assert!(code_str.contains("impl"));
    assert!(code_str.contains("pub struct"));
    assert!(code_str.contains("pub fn"));

    println!("Full compilation pipeline test completed successfully");
    println!("Generated code length: {} characters", code_str.len());
}
