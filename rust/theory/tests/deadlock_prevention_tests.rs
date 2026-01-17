//! Deadlock Prevention Tests
//!
//! These tests verify that unguarded recursion (which can cause deadlocks/livelocks)
//! is properly rejected at all stages of the protocol pipeline:
//! 1. Type construction and validation
//! 2. Projection to local types
//! 3. Runtime execution (if it somehow gets through)
//!
//! This provides end-to-end verification that the guardedness enforcement
//! proven necessary in Lean actually prevents deadlock-prone protocols.

use rumpsteak_theory::{project, validate_global, validate_local, ValidationError};
use rumpsteak_types::{GlobalType, Label, LocalTypeR};

// ============================================================================
// Test 1: Direct Unguarded Recursion (μt. t)
// ============================================================================

#[test]
fn test_direct_unguarded_recursion_rejected() {
    // Attempt to create the most basic deadlock: μt. t
    // This would loop forever without making any progress
    let deadlock_protocol = GlobalType::mu("t", GlobalType::var("t"));

    // Step 1: Verify it fails basic well-formedness
    assert!(
        !deadlock_protocol.well_formed(),
        "Direct unguarded recursion should fail well_formed()"
    );

    // Step 2: Verify it fails guardedness check specifically
    assert!(
        !deadlock_protocol.is_guarded(),
        "μt. t should be detected as unguarded"
    );

    // Step 3: Verify validate_global rejects it
    let validation_result = validate_global(&deadlock_protocol);
    assert!(
        validation_result.is_err(),
        "validate_global should reject unguarded recursion"
    );

    // Verify the error is specifically about unguarded recursion
    match validation_result {
        Err(ValidationError::UnguardedRecursion) => {
            // Expected error type
        }
        Err(other) => panic!("Expected UnguardedRecursion error, got: {:?}", other),
        Ok(_) => panic!("Should not validate successfully"),
    }

    // Step 4: Verify that even if projection succeeds structurally,
    // the resulting local type is also ill-formed
    let projection_result = project(&deadlock_protocol, "A");

    // Projection may succeed structurally (μt.t projects to μt.t for any role)
    // But the result is also ill-formed
    if let Ok(local) = projection_result {
        assert!(
            !local.is_guarded(),
            "Projected local type should also be unguarded"
        );
        assert!(
            !local.well_formed(),
            "Projected local type should also be ill-formed"
        );
        assert!(
            validate_local(&local).is_err(),
            "Projected local type should fail validation"
        );
    }
    // Either way (projection fails OR projected type is ill-formed), the protocol is rejected
}

// ============================================================================
// Test 2: Nested Unguarded Recursion (μt. μs. t)
// ============================================================================

#[test]
fn test_nested_unguarded_recursion_rejected() {
    // Attempt to create nested unguarded recursion: μt. μs. t
    // This would also loop forever without observable actions
    let nested_deadlock = GlobalType::mu("t", GlobalType::mu("s", GlobalType::var("t")));

    assert!(
        !nested_deadlock.well_formed(),
        "Nested unguarded recursion should fail well_formed()"
    );

    assert!(
        !nested_deadlock.is_guarded(),
        "μt. μs. t should be detected as unguarded"
    );

    let validation_result = validate_global(&nested_deadlock);
    assert!(
        validation_result.is_err(),
        "validate_global should reject nested unguarded recursion"
    );

    match validation_result {
        Err(ValidationError::UnguardedRecursion) => {}
        Err(other) => panic!("Expected UnguardedRecursion error, got: {:?}", other),
        Ok(_) => panic!("Should not validate successfully"),
    }
}

// ============================================================================
// Test 3: Contrast with Guarded Recursion (Safe Protocol)
// ============================================================================

#[test]
fn test_guarded_recursion_accepted() {
    // Create a SAFE recursive protocol: μt. A → B: msg. t
    // This makes progress (sends a message) before recursing
    let safe_protocol = GlobalType::mu(
        "t",
        GlobalType::send("A", "B", Label::new("msg"), GlobalType::var("t")),
    );

    // This should pass all checks
    assert!(
        safe_protocol.is_guarded(),
        "Guarded recursion should pass guardedness check"
    );

    assert!(
        safe_protocol.well_formed(),
        "Guarded recursion should be well-formed"
    );

    assert!(
        validate_global(&safe_protocol).is_ok(),
        "validate_global should accept guarded recursion"
    );

    // Should be projectable
    let projection_a = project(&safe_protocol, "A");
    let projection_b = project(&safe_protocol, "B");

    assert!(
        projection_a.is_ok(),
        "Guarded protocol should project successfully for A"
    );
    assert!(
        projection_b.is_ok(),
        "Guarded protocol should project successfully for B"
    );

    // Verify projected local types are also well-formed and guarded
    let local_a = projection_a.unwrap();
    let local_b = projection_b.unwrap();

    assert!(
        local_a.is_guarded(),
        "Projected local type for A should be guarded"
    );
    assert!(
        local_a.well_formed(),
        "Projected local type should be well-formed"
    );
    assert!(
        validate_local(&local_a).is_ok(),
        "Projected type should validate"
    );

    assert!(
        local_b.is_guarded(),
        "Projected local type for B should be guarded"
    );
    assert!(
        local_b.well_formed(),
        "Projected local type should be well-formed"
    );
    assert!(
        validate_local(&local_b).is_ok(),
        "Projected type should validate"
    );
}

// ============================================================================
// Test 4: Local Type Unguarded Recursion
// ============================================================================

#[test]
fn test_local_unguarded_recursion_rejected() {
    // Attempt to create unguarded local recursion: μt. t
    let deadlock_local = LocalTypeR::mu("t", LocalTypeR::var("t"));

    assert!(
        !deadlock_local.is_guarded(),
        "Local μt. t should be detected as unguarded"
    );

    assert!(
        !deadlock_local.well_formed(),
        "Unguarded local type should fail well_formed()"
    );

    let validation_result = validate_local(&deadlock_local);
    assert!(
        validation_result.is_err(),
        "validate_local should reject unguarded recursion"
    );

    match validation_result {
        Err(ValidationError::UnguardedRecursion) => {}
        Err(other) => panic!("Expected UnguardedRecursion error, got: {:?}", other),
        Ok(_) => panic!("Should not validate successfully"),
    }
}

// ============================================================================
// Test 5: Multiple Unguarded Variants
// ============================================================================

#[test]
fn test_various_unguarded_patterns_all_rejected() {
    let unguarded_patterns = vec![
        (
            "direct recursion",
            GlobalType::mu("t", GlobalType::var("t")),
        ),
        (
            "nested mu outer ref",
            GlobalType::mu("t", GlobalType::mu("s", GlobalType::var("t"))),
        ),
        (
            "nested mu inner ref",
            GlobalType::mu("t", GlobalType::mu("s", GlobalType::var("s"))),
        ),
    ];

    for (name, protocol) in unguarded_patterns {
        assert!(!protocol.is_guarded(), "{} should be unguarded", name);
        assert!(
            !protocol.well_formed(),
            "{} should not be well-formed",
            name
        );
        assert!(
            validate_global(&protocol).is_err(),
            "{} should fail validation",
            name
        );

        // Projection may succeed structurally, but result is ill-formed
        if let Ok(local) = project(&protocol, "A") {
            assert!(
                !local.well_formed(),
                "{} projection should be ill-formed",
                name
            );
        }
    }
}

// ============================================================================
// Test 6: End-to-End Pipeline Verification
// ============================================================================

#[test]
fn test_deadlock_prevention_pipeline() {
    // This test simulates the full pipeline that a protocol goes through
    // and verifies that unguarded protocols are rejected at EVERY stage

    // Stage 1: Protocol Definition
    let unguarded_protocol = GlobalType::mu("t", GlobalType::var("t"));
    let guarded_protocol = GlobalType::mu(
        "t",
        GlobalType::send("A", "B", Label::new("ping"), GlobalType::var("t")),
    );

    // Stage 2: Well-formedness Check (type construction)
    assert!(
        !unguarded_protocol.well_formed(),
        "❌ Stage 2: Unguarded protocol rejected at well-formedness check"
    );
    assert!(
        guarded_protocol.well_formed(),
        "✅ Stage 2: Guarded protocol passes well-formedness check"
    );

    // Stage 3: Validation (before projection)
    assert!(
        validate_global(&unguarded_protocol).is_err(),
        "❌ Stage 3: Unguarded protocol rejected at validation"
    );
    assert!(
        validate_global(&guarded_protocol).is_ok(),
        "✅ Stage 3: Guarded protocol passes validation"
    );

    // Stage 4: Projection (to local types)
    // Projection may succeed structurally, but the result is ill-formed
    if let Ok(unguarded_local) = project(&unguarded_protocol, "A") {
        assert!(
            !unguarded_local.well_formed(),
            "❌ Stage 4: Projected unguarded type is ill-formed"
        );
    }

    let guarded_local = project(&guarded_protocol, "A");
    assert!(
        guarded_local.is_ok(),
        "✅ Stage 4: Guarded protocol can be projected"
    );

    // Stage 5: Local type validation
    if let Ok(local) = project(&guarded_protocol, "A") {
        assert!(
            local.is_guarded(),
            "✅ Stage 5: Projected local type is guarded"
        );
        assert!(
            local.well_formed(),
            "✅ Stage 5: Projected local type is well-formed"
        );
        assert!(
            validate_local(&local).is_ok(),
            "✅ Stage 5: Projected local type validates"
        );
    }

    println!("✅ All pipeline stages correctly reject unguarded protocols");
    println!("✅ All pipeline stages correctly accept guarded protocols");
}

// ============================================================================
// Test 7: Real-world Deadlock Scenario
// ============================================================================

#[test]
fn test_realistic_deadlock_scenario() {
    // Simulate a realistic mistake: trying to create an infinite ping-pong
    // without any base case (unguarded recursion)

    // WRONG: μt. t (would just loop forever)
    let wrong_infinite_loop = GlobalType::mu("t", GlobalType::var("t"));

    // RIGHT: μt. A → B: {ping: t, stop: end}
    // Has a guarded recursive case AND a base case
    let correct_ping_pong = GlobalType::mu(
        "t",
        GlobalType::comm(
            "A",
            "B",
            vec![
                (Label::new("ping"), GlobalType::var("t")),
                (Label::new("stop"), GlobalType::End),
            ],
        ),
    );

    // The wrong version should be rejected
    assert!(
        !wrong_infinite_loop.well_formed(),
        "Unguarded infinite loop should be rejected"
    );
    assert!(
        validate_global(&wrong_infinite_loop).is_err(),
        "Should not validate"
    );

    // The correct version should work
    assert!(
        correct_ping_pong.well_formed(),
        "Guarded ping-pong should be accepted"
    );
    assert!(
        validate_global(&correct_ping_pong).is_ok(),
        "Should validate successfully"
    );

    // Can project the correct version
    let local_a = project(&correct_ping_pong, "A");
    let local_b = project(&correct_ping_pong, "B");

    assert!(local_a.is_ok(), "Should project for role A");
    assert!(local_b.is_ok(), "Should project for role B");

    // Both projected types should be guarded
    assert!(
        local_a.unwrap().is_guarded(),
        "A's local type should be guarded"
    );
    assert!(
        local_b.unwrap().is_guarded(),
        "B's local type should be guarded"
    );
}

// ============================================================================
// Test 8: Verify Error Messages Are Helpful
// ============================================================================

#[test]
fn test_error_messages_are_informative() {
    let unguarded = GlobalType::mu("t", GlobalType::var("t"));

    let result = validate_global(&unguarded);
    assert!(result.is_err());

    let error = result.unwrap_err();
    let error_message = error.to_string();

    // Verify the error message mentions the key problem
    assert!(
        error_message.to_lowercase().contains("unguarded")
            || error_message.to_lowercase().contains("recursion")
            || error_message.to_lowercase().contains("guard"),
        "Error message should mention guardedness issue. Got: {}",
        error_message
    );
}

// ============================================================================
// Test 9: Batch Test Multiple Deadlock Patterns
// ============================================================================

#[test]
fn test_comprehensive_deadlock_rejection() {
    struct DeadlockTest {
        name: &'static str,
        protocol: GlobalType,
        should_be_rejected: bool,
    }

    let tests = vec![
        DeadlockTest {
            name: "μt. t (direct loop)",
            protocol: GlobalType::mu("t", GlobalType::var("t")),
            should_be_rejected: true,
        },
        DeadlockTest {
            name: "μt. μs. t (nested loop)",
            protocol: GlobalType::mu("t", GlobalType::mu("s", GlobalType::var("t"))),
            should_be_rejected: true,
        },
        DeadlockTest {
            name: "μt. A→B:msg.t (guarded)",
            protocol: GlobalType::mu(
                "t",
                GlobalType::send("A", "B", Label::new("msg"), GlobalType::var("t")),
            ),
            should_be_rejected: false,
        },
        DeadlockTest {
            name: "A→B:msg.end (no recursion)",
            protocol: GlobalType::send("A", "B", Label::new("msg"), GlobalType::End),
            should_be_rejected: false,
        },
    ];

    for test in &tests {
        let is_rejected = !test.protocol.well_formed();
        assert_eq!(
            is_rejected, test.should_be_rejected,
            "Test '{}' failed: expected rejected={}, got rejected={}",
            test.name, test.should_be_rejected, is_rejected
        );

        // Verify validation result matches
        let validation_rejected = validate_global(&test.protocol).is_err();
        assert_eq!(
            validation_rejected, test.should_be_rejected,
            "Test '{}' validation mismatch",
            test.name
        );
    }

    println!("✅ All {} deadlock pattern tests passed", tests.len());
}
