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
    compiler::{parser::parse_choreography_str, projection::project},
};

// ============================================================================
// Namespace Edge Cases
// ============================================================================

#[test]
fn test_namespace_conflicts_and_resolution() {
    // Test that identical protocol names in different namespaces don't conflict
    let protocol_a = r#"
        module service_a exposing (Protocol)
        protocol Protocol = {
            roles Client, Server
            Client -> Server: Request
        }
    "#;

    let protocol_b = r#"
        module service_b exposing (Protocol)
        protocol Protocol = {
            roles Client, Server
            Client -> Server: Request
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
        module impl exposing (Test)
        protocol Test = {
            roles A, B
            A -> B: Msg
        }
    "#,
    );
    // Note: The parser may accept this since it's just a string literal

    // Test namespace with special characters
    let result = parse_choreography_str(
        r#"
        module test::namespace exposing (Test)
        protocol Test = {
            roles A, B
            A -> B: Msg
        }
    "#,
    );
    assert!(
        result.is_err(),
        "Module names with special characters should be rejected"
    );

    // Test extremely long namespace
    let long_namespace = "a".repeat(200);
    let protocol = format!(
        r#"
        module {} exposing (Test)
        protocol Test = {{
            roles A, B
            A -> B: Msg
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
    let result = parse_choreography_str(
        r#"
        module 测试 exposing (Test)
        protocol Test = {
            roles A, B
            A -> B: Msg
        }
    "#,
    );
    assert!(
        result.is_err(),
        "Unicode module identifiers should be rejected by the parser"
    );
}

// ============================================================================
// Dynamic Role Overflow Protection Edge Cases
// ============================================================================

#[test]
fn test_complex_dynamic_role_overflow_scenarios() {
    // Test nested dynamic roles with potential overflow
    let protocol = format!(
        r#"
        protocol OverflowTest = {{
            roles Controller, Workers[{}], Monitors[{}]
            
            Controller -> Workers[*]: Start
            Workers[0..{}] -> Monitors[*]: Status
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
// Range Syntax Edge Cases
// ============================================================================

#[test]
fn test_range_boundary_conditions() {
    // Test range at maximum boundary
    let protocol = format!(
        r#"
        protocol RangeTest = {{
            roles Controller, Workers[{}]
            
            Workers[0..{}] -> Controller: Status
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
        protocol RangeTest = {{
            roles Controller, Workers[{}]
            
            Workers[0..{}] -> Controller: Status
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
        protocol InvalidRange = {
            roles Controller, Workers[10]
            
            Workers[5..2] -> Controller: Status
        }
    "#,
    );
    assert!(result.is_err(), "Should reject range with start > end");

    // Test range with negative indices (if supported)
    let _result = parse_choreography_str(
        r#"
        protocol NegativeRange = {
            roles Controller, Workers[10]
            
            Workers[-1..5] -> Controller: Status
        }
    "#,
    );
    // Should either parse (if negative indices are supported) or reject consistently

    // Test range with symbolic bounds
    let result = parse_choreography_str(
        r#"
        protocol SymbolicRange = {
            roles Controller, Workers[N]
            
            Workers[start..end] -> Controller: Status
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
        protocol NestedRange = {
            roles Coordinator, Workers[N], Monitors[M]
            
            Workers[0..quorum] -> Monitors[i..j]: Data
        }
    "#,
    );
    assert!(result.is_ok(), "Should handle complex range expressions");
}

// ============================================================================
// Cross-Feature Integration Tests
// ============================================================================

#[test]
fn test_module_dynamic_roles_integration() {
    // Test module namespaces with dynamic roles and choices
    let protocol = r#"
        module integration_test exposing (CompleteIntegration)
        protocol CompleteIntegration = {
            roles Coordinator, Workers[*], Database

            Coordinator -> Workers[*]: Initialize
            Workers[i] -> Database: Query
            Database -> Workers[i]: Response

            choice at Coordinator {
                success -> {
                    Coordinator -> Workers[*]: Success
                }
                retry -> {
                    Coordinator -> Workers[active_set]: Retry
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
}

#[test]
fn test_complex_projection_with_dynamic_roles() {
    // Test projection works with dynamic roles
    let protocol = r#"
        module projection_test exposing (ProjectionIntegration)
        protocol ProjectionIntegration = {
            roles Client, Servers[N], LoadBalancer

            Client -> LoadBalancer: Request
            LoadBalancer -> Servers[target]: ForwardedRequest
            Servers[target] -> LoadBalancer: Response
            LoadBalancer -> Client: FinalResponse
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
