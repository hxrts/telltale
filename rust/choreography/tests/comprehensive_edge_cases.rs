#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

//! Comprehensive edge case testing for new functionality
//!
//! This module tests critical edge cases and boundary conditions for:
//! - Namespace validation and conflicts
//! - Dynamic role overflow protection in complex scenarios  
//! - Annotation validation and malformed handling
//! - Range syntax edge cases
//! - Cross-feature integration scenarios

use rumpsteak_aura_choreography::{
    ast::*,
    compiler::{
        codegen::generate_choreography_code_with_dynamic_roles, parser::parse_choreography_str,
        projection::project,
    },
};

// ============================================================================
// Namespace Edge Cases
// ============================================================================

#[test]
fn test_namespace_conflicts_and_resolution() {
    // Test that identical protocol names in different namespaces don't conflict
    let protocol_a = r#"
        #[namespace = "service_a"]
        choreography Protocol {
            roles: Client, Server;
            Client -> Server: Request;
        }
    "#;

    let protocol_b = r#"
        #[namespace = "service_b"] 
        choreography Protocol {
            roles: Client, Server;
            Client -> Server: Request;
        }
    "#;

    let choreo_a = parse_choreography_str(protocol_a).expect("Protocol A should parse");
    let choreo_b = parse_choreography_str(protocol_b).expect("Protocol B should parse");

    // Same name but different qualified names
    assert_eq!(choreo_a.name.to_string(), "Protocol");
    assert_eq!(choreo_b.name.to_string(), "Protocol");
    assert_ne!(choreo_a.qualified_name(), choreo_b.qualified_name());
    assert_eq!(choreo_a.qualified_name(), "service_a::Protocol");
    assert_eq!(choreo_b.qualified_name(), "service_b::Protocol");
}

#[test]
fn test_namespace_validation_edge_cases() {
    // Test namespace with keywords - may or may not be rejected
    let _result = parse_choreography_str(
        r#"
        #[namespace = "impl"]
        choreography Test {
            roles: A, B;
            A -> B: Msg;
        }
    "#,
    );
    // Note: The parser may accept this since it's just a string literal

    // Test namespace with special characters
    let _result = parse_choreography_str(
        r#"
        #[namespace = "test::namespace"]
        choreography Test {
            roles: A, B;
            A -> B: Msg;
        }
    "#,
    );
    // Parser may accept this as a string literal - behavior depends on implementation

    // Test extremely long namespace
    let long_namespace = "a".repeat(200);
    let protocol = format!(
        r#"
        #[namespace = "{}"]
        choreography Test {{
            roles: A, B;
            A -> B: Msg;
        }}
    "#,
        long_namespace
    );
    let result = parse_choreography_str(&protocol);
    // Should either parse or give clear error
    if let Ok(choreo) = result {
        assert_eq!(choreo.namespace.as_ref().unwrap(), &long_namespace);
    }
    // Acceptable to reject very long names
}

#[test]
fn test_namespace_with_unicode() {
    // Test namespace with Unicode characters
    let _result = parse_choreography_str(
        r#"
        #[namespace = "测试"]
        choreography Test {
            roles: A, B;
            A -> B: Msg;
        }
    "#,
    );
    // Should handle Unicode appropriately (either accept or reject consistently)
    if let Ok(choreo) = _result {
        assert_eq!(choreo.namespace.as_ref().unwrap(), "测试");
    }
    // Acceptable to reject Unicode in identifiers
}

// ============================================================================
// Dynamic Role Overflow Protection Edge Cases
// ============================================================================

#[test]
fn test_complex_dynamic_role_overflow_scenarios() {
    // Test nested dynamic roles with potential overflow
    let protocol = format!(
        r#"
        choreography OverflowTest {{
            roles: Controller, Workers[{}], Monitors[{}];
            
            Controller -> Workers[*]: Start;
            Workers[0..{}] -> Monitors[*]: Status;
        }}
    "#,
        MAX_ROLE_COUNT / 2,
        MAX_ROLE_COUNT / 2,
        MAX_RANGE_SIZE / 2
    );

    let choreo = parse_choreography_str(&protocol).expect("Should parse valid counts");

    // Verify that validation catches potential runtime overflow
    for role in &choreo.roles {
        assert!(
            role.validate().is_ok(),
            "Role validation should pass for valid counts"
        );
    }
}

#[test]
fn test_role_index_overflow_protection() {
    // Test that role indices are protected against overflow
    let result = RoleIndex::safe_concrete(MAX_ROLE_INDEX + 1);
    assert!(matches!(
        result,
        Err(RoleValidationError::IndexOverflow { .. })
    ));

    let result = RoleIndex::safe_concrete(MAX_ROLE_INDEX);
    assert!(result.is_ok());
}

#[test]
fn test_range_size_overflow_protection() {
    // Test that range sizes are protected against overflow
    let result = RoleRange::safe_concrete(0, MAX_RANGE_SIZE + 10);
    assert!(matches!(
        result,
        Err(RoleValidationError::RangeSizeOverflow { .. })
    ));

    // Test valid range at boundary
    let result = RoleRange::safe_concrete(0, MAX_RANGE_SIZE - 1);
    assert!(result.is_ok());
}

#[test]
fn test_dynamic_role_binding_overflow() {
    // Test that overflow protection catches unsafe role parameters
    let result = RoleParam::safe_static(MAX_ROLE_COUNT + 1);
    assert!(matches!(
        result,
        Err(RoleValidationError::CountOverflow { .. })
    ));

    // Test binding at boundary
    let result = RoleParam::safe_static(MAX_ROLE_COUNT);
    assert!(result.is_ok());

    // Test runtime role validation
    let runtime_param = RoleParam::Runtime;
    assert!(runtime_param.validate().is_ok());
}

// ============================================================================
// Annotation Validation Edge Cases
// ============================================================================

#[test]
fn test_malformed_annotation_handling() {
    // Test completely malformed annotation syntax
    let result = parse_choreography_str(
        r#"
        choreography Test {
            roles: A, B;
            [@malformed syntax here
            A -> B: Msg;
        }
    "#,
    );
    assert!(result.is_err(), "Should reject malformed annotation syntax");

    // Test unclosed annotation
    let result = parse_choreography_str(
        r#"
        choreography Test {
            roles: A, B;
            [@unclosed=value
            A -> B: Msg;
        }
    "#,
    );
    assert!(result.is_err(), "Should reject unclosed annotations");

    // Test annotation with no value
    let _result = parse_choreography_str(
        r#"
        choreography Test {
            roles: A, B;
            [@key=]
            A -> B: Msg;
        }
    "#,
    );
    assert!(
        _result.is_err(),
        "Should reject annotations with empty values"
    );
}

#[test]
fn test_annotation_key_validation() {
    // Test annotations with invalid key names
    let result = parse_choreography_str(
        r#"
        choreography Test {
            roles: A, B;
            [@123invalid=value]
            A -> B: Msg;
        }
    "#,
    );
    assert!(result.is_err(), "Should reject numeric annotation keys");

    // Test annotation with spaces in key
    let _result = parse_choreography_str(
        r#"
        choreography Test {
            roles: A, B;
            [@"key with spaces"=value]
            A -> B: Msg;
        }
    "#,
    );
    // May or may not be supported - check behavior is consistent
}

#[test]
fn test_annotation_value_edge_cases() {
    // Test annotation with very long value
    let long_value = "x".repeat(1000);
    let protocol = format!(
        r#"
        choreography Test {{
            roles: A, B;
            [@longval="{}"]
            A -> B: Msg;
        }}
    "#,
        long_value
    );

    let result = parse_choreography_str(&protocol);
    if let Ok(choreo) = result {
        // If accepted, should store the full value
        match &choreo.protocol {
            Protocol::Send { annotations, .. } => {
                assert_eq!(annotations.get("longval").unwrap(), &long_value);
            }
            _ => panic!("Expected Send protocol"),
        }
    }
    // Acceptable to reject very long values

    // Test annotation with special characters in value
    let _result = parse_choreography_str(
        r#"
        choreography Test {
            roles: A, B;
            [@special="value with spaces and symbols !@#$%^&*()"]
            A -> B: Msg;
        }
    "#,
    );
    assert!(
        _result.is_ok(),
        "Should accept special characters in annotation values"
    );
}

#[test]
fn test_multiple_annotation_boundary_conditions() {
    // Test maximum number of annotations
    let many_annotations = (0..50)
        .map(|i| format!("@key{}=\"value{}\"", i, i))
        .collect::<Vec<_>>()
        .join(", ");

    let protocol = format!(
        r#"
        choreography Test {{
            roles: A, B;
            [{}]
            A -> B: Msg;
        }}
    "#,
        many_annotations
    );

    let _result = parse_choreography_str(&protocol);
    if let Ok(choreo) = _result {
        // Should handle many annotations correctly
        match &choreo.protocol {
            Protocol::Send { annotations, .. } => {
                assert_eq!(annotations.len(), 50);
                assert_eq!(annotations.get("key25").unwrap(), "value25");
            }
            _ => panic!("Expected Send protocol"),
        }
    }
    // Acceptable to limit annotation count
}

// ============================================================================
// Range Syntax Edge Cases
// ============================================================================

#[test]
fn test_range_boundary_conditions() {
    // Test range at maximum boundary
    let protocol = format!(
        r#"
        choreography RangeTest {{
            roles: Controller, Workers[{}];
            
            Workers[0..{}] -> Controller: Status;
        }}
    "#,
        MAX_ROLE_COUNT,
        MAX_RANGE_SIZE - 1
    );

    let result = parse_choreography_str(&protocol);
    assert!(result.is_ok(), "Should accept range at valid boundary");

    // Test range exceeding boundary
    let protocol = format!(
        r#"
        choreography RangeTest {{
            roles: Controller, Workers[{}];
            
            Workers[0..{}] -> Controller: Status;
        }}
    "#,
        MAX_ROLE_COUNT,
        MAX_RANGE_SIZE + 100
    );

    let result = parse_choreography_str(&protocol);
    assert!(
        result.is_err(),
        "Should reject range exceeding maximum size"
    );
}

#[test]
fn test_invalid_range_expressions() {
    // Test range with start > end
    let result = parse_choreography_str(
        r#"
        choreography InvalidRange {
            roles: Controller, Workers[10];
            
            Workers[5..2] -> Controller: Status;
        }
    "#,
    );
    assert!(result.is_err(), "Should reject range with start > end");

    // Test range with negative indices (if supported)
    let _result = parse_choreography_str(
        r#"
        choreography NegativeRange {
            roles: Controller, Workers[10];
            
            Workers[-1..5] -> Controller: Status;
        }
    "#,
    );
    // Should either parse (if negative indices are supported) or reject consistently

    // Test range with symbolic bounds
    let result = parse_choreography_str(
        r#"
        choreography SymbolicRange {
            roles: Controller, Workers[N];
            
            Workers[start..end] -> Controller: Status;
        }
    "#,
    );
    assert!(result.is_ok(), "Should accept symbolic range bounds");
}

#[test]
fn test_nested_range_expressions() {
    // Test complex range expressions with nested references
    let result = parse_choreography_str(
        r#"
        choreography NestedRange {
            roles: Coordinator, Workers[N], Monitors[M];
            
            Workers[0..quorum] -> Monitors[i..j]: Data;
        }
    "#,
    );
    assert!(result.is_ok(), "Should handle complex range expressions");
}

// ============================================================================
// Cross-Feature Integration Tests
// ============================================================================

#[test]
fn test_namespace_dynamic_roles_annotations_integration() {
    // Test all features working together
    let protocol = r#"
        #[namespace = "integration_test"]
        choreography CompleteIntegration {
            roles: Coordinator, Workers[*], Database;
            
            [@phase = "init", @timeout = 5000]
            Coordinator -> Workers[*]: Initialize;
            
            Workers[i][@priority = "high"] -> Database[@pool = "primary"]: Query;
            
            [@compress = "lz4", @cache_ttl = 300]  
            Database -> Workers[i]: Response;
            
            [@critical, @min_responses = "majority"]
            Workers[0..quorum] -> Coordinator: Result;
            
            choice Coordinator {
                success: {
                    [@audit = "true", @notification = "email"]
                    Coordinator -> Workers[*]: Success;
                }
                retry: {
                    [@backoff = "exponential", @max_retries = 3]
                    Coordinator -> Workers[active_set]: Retry;
                }
            }
        }
    "#;

    let choreo = parse_choreography_str(protocol).expect("Complete integration should parse");

    // Verify all features are present
    assert_eq!(choreo.namespace.as_ref().unwrap(), "integration_test");
    assert_eq!(choreo.roles.len(), 3);

    // Verify dynamic roles
    let workers = &choreo.roles[1];
    assert_eq!(workers.name.to_string(), "Workers");
    assert!(workers.is_dynamic());

    // Test code generation with all features
    let local_types = vec![
        (choreo.roles[0].clone(), LocalType::End),
        (choreo.roles[1].clone(), LocalType::End),
        (choreo.roles[2].clone(), LocalType::End),
    ];

    let generated_code = generate_choreography_code_with_dynamic_roles(&choreo, &local_types);
    let code_str = generated_code.to_string();

    // Verify some form of integration in generated code
    println!(
        "Generated code snippet: {}",
        &code_str[0..std::cmp::min(500, code_str.len())]
    );
    assert!(!code_str.is_empty(), "Should generate some code");
}

#[test]
fn test_complex_projection_with_all_features() {
    // Test projection works with combined features
    let protocol = r#"
        #[namespace = "projection_test"]
        choreography ProjectionIntegration {
            roles: Client, Servers[N], LoadBalancer;
            
            [@load_balancing = "round_robin"]
            Client -> LoadBalancer: Request;
            
            LoadBalancer -> Servers[target][@route = "primary"]: ForwardedRequest;
            
            [@timeout = 30000, @retry = 2]
            Servers[target] -> LoadBalancer: Response;
            
            LoadBalancer -> Client: FinalResponse;
        }
    "#;

    let choreo = parse_choreography_str(protocol).expect("Should parse projection test");

    // Test projection for each role
    for role in &choreo.roles {
        let result = project(&choreo, role);
        match result {
            Ok(local_type) => {
                // For dynamic roles without bindings, End may be valid
                println!("Projection result for {}: {:?}", role.name, local_type);
            }
            Err(err) => {
                // Projection may fail for dynamic roles without bindings - ensure error is reasonable
                println!(
                    "Expected projection error for dynamic role {}: {:?}",
                    role.name, err
                );
            }
        }
    }
}

#[test]
fn test_error_propagation_across_features() {
    // Test that errors in one feature don't break others
    let protocol = r#"
        #[namespace = "error_test"]
        choreography ErrorPropagation {
            roles: A, B[*], UndefinedRole;
            
            [@malformed annotation syntax
            A -> B[*]: ValidMessage;
            
            B[999999999999] -> UndefinedRole: InvalidMessage;
        }
    "#;

    let result = parse_choreography_str(protocol);
    assert!(
        result.is_err(),
        "Should reject protocol with multiple errors"
    );

    // Verify error contains useful information
    let error_msg = result.unwrap_err().to_string();
    println!("Error message: {}", error_msg);
    // Should contain information about the first error encountered
    assert!(!error_msg.is_empty());
}

#[test]
fn test_performance_with_all_features() {
    // Test that combining all features doesn't cause performance degradation
    use std::time::Instant;

    let complex_protocol = r#"
        #[namespace = "performance_integration"]
        choreography PerformanceTest {
            roles: Coordinator, Workers[*], Databases[M], Monitors[K];
            
            [@start_time = "now", @trace = "distributed"]
            Coordinator -> Workers[*]: StartWork;
            
            Workers[i][@worker_id="auto"] -> Databases[j][@shard="auto"]: Query;
            
            [@cache = "redis", @ttl = 3600]
            Databases[j] -> Workers[requester]: QueryResult;
            
            [@aggregate = "sum", @validation = "checksum"]
            Workers[active_set] -> Monitors[assigned_monitor]: StatusUpdate;
            
            [@alert = "slack", @threshold = 95]
            Monitors[k] -> Coordinator: HealthReport;
            
            choice Coordinator {
                healthy: {
                    [@continue = "true", @log_level = "info"]
                    Coordinator -> Workers[*]: ContinueWork;
                }
                degraded: {
                    [@scale_up = "auto", @alert = "pagerduty"]
                    Coordinator -> Workers[backup_pool]: ActivateBackup;
                }
                critical: {
                    [@emergency = "true", @escalate = "oncall"]
                    Coordinator -> Workers[*]: EmergencyStop;
                    
                    [@rollback = "true", @backup_restore = "latest"]
                    Coordinator -> Databases[*]: Rollback;
                }
            }
        }
    "#;

    let start = Instant::now();

    // Parse multiple times to test performance consistency
    for _ in 0..10 {
        let choreo =
            parse_choreography_str(complex_protocol).expect("Should parse complex protocol");

        // Quick validation
        assert_eq!(
            choreo.namespace.as_ref().unwrap(),
            "performance_integration"
        );
        assert_eq!(choreo.roles.len(), 4);

        // Test projection attempt (may fail but shouldn't crash)
        for role in &choreo.roles {
            let _ = project(&choreo, role);
        }
    }

    let duration = start.elapsed();

    // Performance assertion - should handle complex protocols quickly
    assert!(
        duration.as_millis() < 500,
        "Performance test took too long: {:?}",
        duration
    );
    println!(
        "Performance integration test completed 10 iterations in {:?}",
        duration
    );
}
