//! Tests validating merge semantics correspondence between Rust and Lean.
//!
//! These tests verify that the Rust merge implementation matches the behavior
//! defined in `lean/Telltale/Protocol/ProjectionR.lean`:
//!
//! - `merge_send_branches` ↔ Lean's `LocalTypeR.mergeSendSorted`
//! - `merge_recv_branches` ↔ Lean's `LocalTypeR.mergeRecvSorted`
//!
//! The key semantic difference:
//! - **Send merge**: Requires IDENTICAL label sets (fails if different)
//! - **Recv merge**: UNIONS label sets (succeeds with different labels)

#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

use serde_json::json;
use telltale_lean_bridge::{json_to_local, local_to_json, LeanRunner};
use telltale_theory::{can_merge, merge, project};
use telltale_types::{GlobalType, Label, LocalTypeR};

/// Helper macro to skip tests when Lean binary is unavailable.
macro_rules! skip_without_lean {
    () => {
        if !LeanRunner::is_available() {
            eprintln!("SKIPPED: Lean binary not available. Run `cd lean && lake build` to enable.");
            return;
        }
    };
}

// ============================================================================
// Rust Merge Semantics Tests (No Lean Required)
// ============================================================================

/// Test: Send merge with same labels succeeds.
/// Lean correspondence: `mergeSendSorted` returns `some` when labels match.
#[test]
fn test_send_merge_same_labels_succeeds() {
    let t1 = LocalTypeR::send("B", Label::new("x"), LocalTypeR::End);
    let t2 = LocalTypeR::send("B", Label::new("x"), LocalTypeR::End);

    let result = merge(&t1, &t2);
    assert!(result.is_ok(), "Send merge with same labels should succeed");

    let merged = result.unwrap();
    match merged {
        LocalTypeR::Send { partner, branches } => {
            assert_eq!(partner, "B");
            assert_eq!(branches.len(), 1);
            assert_eq!(branches[0].0.name, "x");
        }
        _ => panic!("Expected Send"),
    }
}

/// Test: Send merge with different labels fails.
/// Lean correspondence: `mergeSendSorted` returns `none` when labels differ.
#[test]
fn test_send_merge_different_labels_fails() {
    let t1 = LocalTypeR::send("B", Label::new("x"), LocalTypeR::End);
    let t2 = LocalTypeR::send("B", Label::new("y"), LocalTypeR::End);

    let result = merge(&t1, &t2);
    assert!(
        result.is_err(),
        "Send merge with different labels should fail (Lean: mergeSendSorted returns none)"
    );
}

/// Test: Recv merge with same labels succeeds.
/// Lean correspondence: `mergeRecvSorted` returns `some` when labels match.
#[test]
fn test_recv_merge_same_labels_succeeds() {
    let t1 = LocalTypeR::recv("A", Label::new("x"), LocalTypeR::End);
    let t2 = LocalTypeR::recv("A", Label::new("x"), LocalTypeR::End);

    let result = merge(&t1, &t2);
    assert!(result.is_ok(), "Recv merge with same labels should succeed");

    let merged = result.unwrap();
    match merged {
        LocalTypeR::Recv { partner, branches } => {
            assert_eq!(partner, "A");
            assert_eq!(branches.len(), 1);
            assert_eq!(branches[0].0.name, "x");
        }
        _ => panic!("Expected Recv"),
    }
}

/// Test: Recv merge with different labels succeeds and unions labels.
/// Lean correspondence: `mergeRecvSorted` unions labels from both sides.
#[test]
fn test_recv_merge_different_labels_unions() {
    let t1 = LocalTypeR::recv("A", Label::new("x"), LocalTypeR::End);
    let t2 = LocalTypeR::recv("A", Label::new("y"), LocalTypeR::End);

    let result = merge(&t1, &t2);
    assert!(
        result.is_ok(),
        "Recv merge with different labels should succeed (Lean: mergeRecvSorted unions labels)"
    );

    let merged = result.unwrap();
    match merged {
        LocalTypeR::Recv { partner, branches } => {
            assert_eq!(partner, "A");
            assert_eq!(branches.len(), 2);
            let labels: Vec<_> = branches
                .iter()
                .map(|(l, _vt, _c)| l.name.as_str())
                .collect();
            assert!(labels.contains(&"x"));
            assert!(labels.contains(&"y"));
        }
        _ => panic!("Expected Recv"),
    }
}

/// Test: Recv merge with overlapping labels unions and merges continuations.
/// Lean correspondence: shared labels have their continuations merged recursively.
#[test]
fn test_recv_merge_overlapping_labels() {
    let t1 = LocalTypeR::Recv {
        partner: "A".to_string(),
        branches: vec![
            (Label::new("x"), None, LocalTypeR::End),
            (Label::new("y"), None, LocalTypeR::End),
        ],
    };
    let t2 = LocalTypeR::Recv {
        partner: "A".to_string(),
        branches: vec![
            (Label::new("y"), None, LocalTypeR::End),
            (Label::new("z"), None, LocalTypeR::End),
        ],
    };

    let merged = merge(&t1, &t2).expect("Recv merge with overlapping labels should succeed");

    match merged {
        LocalTypeR::Recv { partner, branches } => {
            assert_eq!(partner, "A");
            assert_eq!(branches.len(), 3, "Should have x, y, z");
            let labels: Vec<_> = branches
                .iter()
                .map(|(l, _vt, _c)| l.name.as_str())
                .collect();
            assert!(labels.contains(&"x"));
            assert!(labels.contains(&"y"));
            assert!(labels.contains(&"z"));
        }
        _ => panic!("Expected Recv"),
    }
}

// ============================================================================
// Projection Merge Semantics Tests
// ============================================================================

/// Test: Non-participant projection fails when sends have different labels.
/// This tests the full projection → merge pipeline.
#[test]
fn test_projection_fails_for_incompatible_send_merge() {
    // A -> B: {l1. C -> B: x. end, l2. C -> B: y. end}
    // C is not involved in A->B choice but must send different labels
    let g = GlobalType::comm(
        "A",
        "B",
        vec![
            (
                Label::new("l1"),
                GlobalType::send("C", "B", Label::new("x"), GlobalType::End),
            ),
            (
                Label::new("l2"),
                GlobalType::send("C", "B", Label::new("y"), GlobalType::End),
            ),
        ],
    );

    let result = project(&g, "C");
    assert!(
        result.is_err(),
        "Projection should fail: C cannot send different labels based on unseen A->B choice"
    );
}

/// Test: Non-participant projection succeeds when sends have same labels.
#[test]
fn test_projection_succeeds_for_compatible_send_merge() {
    // A -> B: {l1. C -> B: msg. end, l2. C -> B: msg. end}
    // C sends the same message regardless of which branch
    let g = GlobalType::comm(
        "A",
        "B",
        vec![
            (
                Label::new("l1"),
                GlobalType::send("C", "B", Label::new("msg"), GlobalType::End),
            ),
            (
                Label::new("l2"),
                GlobalType::send("C", "B", Label::new("msg"), GlobalType::End),
            ),
        ],
    );

    let result = project(&g, "C");
    assert!(
        result.is_ok(),
        "Projection should succeed: C sends same label in both branches"
    );

    let local = result.unwrap();
    match local {
        LocalTypeR::Send { partner, branches } => {
            assert_eq!(partner, "B");
            assert_eq!(branches.len(), 1);
            assert_eq!(branches[0].0.name, "msg");
        }
        _ => panic!("Expected Send"),
    }
}

/// Test: Non-participant projection succeeds when recvs have different labels.
#[test]
fn test_projection_succeeds_for_recv_merge() {
    // A -> B: {l1. B -> C: x. end, l2. B -> C: y. end}
    // C receives from B in both branches with different labels
    let g = GlobalType::comm(
        "A",
        "B",
        vec![
            (
                Label::new("l1"),
                GlobalType::send("B", "C", Label::new("x"), GlobalType::End),
            ),
            (
                Label::new("l2"),
                GlobalType::send("B", "C", Label::new("y"), GlobalType::End),
            ),
        ],
    );

    let result = project(&g, "C");
    assert!(
        result.is_ok(),
        "Projection should succeed: C can receive any label from B"
    );

    let local = result.unwrap();
    match local {
        LocalTypeR::Recv { partner, branches } => {
            assert_eq!(partner, "B");
            assert_eq!(branches.len(), 2);
            let labels: Vec<_> = branches
                .iter()
                .map(|(l, _vt, _c)| l.name.as_str())
                .collect();
            assert!(labels.contains(&"x"));
            assert!(labels.contains(&"y"));
        }
        _ => panic!("Expected Recv"),
    }
}

// ============================================================================
// JSON Round-trip Tests
// ============================================================================

/// Test: Local type JSON export includes all merged recv branches.
#[test]
fn test_merged_recv_json_roundtrip() {
    let merged = LocalTypeR::Recv {
        partner: "A".to_string(),
        branches: vec![
            (Label::new("x"), None, LocalTypeR::End),
            (Label::new("y"), None, LocalTypeR::End),
        ],
    };

    let json = local_to_json(&merged);
    let parsed = json_to_local(&json).expect("Should parse merged type");

    // Verify structure matches
    match parsed {
        LocalTypeR::Recv { partner, branches } => {
            assert_eq!(partner, "A");
            assert_eq!(branches.len(), 2);
        }
        _ => panic!("Expected Recv"),
    }
}

// ============================================================================
// Lean Integration Tests (Require Lean Binary)
// ============================================================================

/// Test: Validate projection with Lean - compatible sends succeed.
#[test]
fn test_lean_validates_compatible_projection() {
    skip_without_lean!();

    // Build choreography JSON for: A -> B: {l1. C -> B: msg. end, l2. C -> B: msg. end}
    let choreo = json!({
        "roles": ["A", "B", "C"],
        "actions": [
            {"from": "A", "to": "B", "label": "l1"},
            {"from": "C", "to": "B", "label": "msg"},
            {"from": "A", "to": "B", "label": "l2"},
            {"from": "C", "to": "B", "label": "msg"}
        ]
    });

    // C's program: just sends msg to B
    let program = json!({
        "role": "C",
        "programs": [{
            "branch": null,
            "effects": [{"kind": "send", "partner": "B", "label": "msg"}]
        }]
    });

    let runner = LeanRunner::new().expect("Lean binary should exist");
    let result = runner
        .validate(&choreo, &program)
        .expect("Validation should not crash");

    // This should succeed because C sends the same message in both branches
    assert!(
        result.success,
        "Lean should validate compatible projection: {:?}",
        result
    );
}

/// Test: Validate that Lean accepts recv merge with different labels.
#[test]
fn test_lean_accepts_recv_merge_projection() {
    skip_without_lean!();

    // Build choreography JSON for: A -> B: {l1. B -> C: x. end, l2. B -> C: y. end}
    let choreo = json!({
        "roles": ["A", "B", "C"],
        "actions": [
            {"from": "A", "to": "B", "label": "l1"},
            {"from": "B", "to": "C", "label": "x"},
            {"from": "A", "to": "B", "label": "l2"},
            {"from": "B", "to": "C", "label": "y"}
        ]
    });

    // C's program: receives from B (could be x or y)
    let program = json!({
        "role": "C",
        "programs": [
            {
                "branch": "x",
                "effects": [{"kind": "recv", "partner": "B", "label": "x"}]
            },
            {
                "branch": "y",
                "effects": [{"kind": "recv", "partner": "B", "label": "y"}]
            }
        ]
    });

    let runner = LeanRunner::new().expect("Lean binary should exist");
    let result = runner
        .validate(&choreo, &program)
        .expect("Validation should not crash");

    // This should succeed because C can receive any label from B
    assert!(
        result.success,
        "Lean should validate recv merge projection: {:?}",
        result
    );
}

// ============================================================================
// can_merge Predicate Tests
// ============================================================================

#[test]
fn test_can_merge_send_same_label() {
    let t1 = LocalTypeR::send("B", Label::new("x"), LocalTypeR::End);
    let t2 = LocalTypeR::send("B", Label::new("x"), LocalTypeR::End);
    assert!(can_merge(&t1, &t2));
}

#[test]
fn test_can_merge_send_different_label_false() {
    let t1 = LocalTypeR::send("B", Label::new("x"), LocalTypeR::End);
    let t2 = LocalTypeR::send("B", Label::new("y"), LocalTypeR::End);
    assert!(!can_merge(&t1, &t2));
}

#[test]
fn test_can_merge_recv_different_label_true() {
    let t1 = LocalTypeR::recv("A", Label::new("x"), LocalTypeR::End);
    let t2 = LocalTypeR::recv("A", Label::new("y"), LocalTypeR::End);
    assert!(can_merge(&t1, &t2));
}

#[test]
fn test_can_merge_end() {
    assert!(can_merge(&LocalTypeR::End, &LocalTypeR::End));
}

#[test]
fn test_can_merge_end_send_false() {
    let send = LocalTypeR::send("B", Label::new("x"), LocalTypeR::End);
    assert!(!can_merge(&LocalTypeR::End, &send));
}

// ============================================================================
// Recursive Type Merge Tests
// ============================================================================

#[test]
fn test_recursive_merge_same_var() {
    // μt. !B{x.t} ⊔ μt. !B{x.t} = μt. !B{x.t}
    let t1 = LocalTypeR::mu(
        "t",
        LocalTypeR::send("B", Label::new("x"), LocalTypeR::var("t")),
    );
    let t2 = LocalTypeR::mu(
        "t",
        LocalTypeR::send("B", Label::new("x"), LocalTypeR::var("t")),
    );

    let result = merge(&t1, &t2);
    assert!(result.is_ok(), "Recursive types with same var should merge");
    assert_eq!(result.unwrap(), t1);
}

#[test]
fn test_recursive_merge_different_var_fails() {
    // μt. !B{x.t} ⊔ μs. !B{x.s} = ERROR
    let t1 = LocalTypeR::mu(
        "t",
        LocalTypeR::send("B", Label::new("x"), LocalTypeR::var("t")),
    );
    let t2 = LocalTypeR::mu(
        "s",
        LocalTypeR::send("B", Label::new("x"), LocalTypeR::var("s")),
    );

    let result = merge(&t1, &t2);
    assert!(
        result.is_err(),
        "Recursive types with different vars should fail"
    );
}

#[test]
fn test_recursive_send_different_labels_fails() {
    // μt. !B{x.t} ⊔ μt. !B{y.t} = ERROR (send labels differ)
    let t1 = LocalTypeR::mu(
        "t",
        LocalTypeR::send("B", Label::new("x"), LocalTypeR::var("t")),
    );
    let t2 = LocalTypeR::mu(
        "t",
        LocalTypeR::send("B", Label::new("y"), LocalTypeR::var("t")),
    );

    let result = merge(&t1, &t2);
    assert!(
        result.is_err(),
        "Recursive send types with different labels should fail"
    );
}

#[test]
fn test_recursive_recv_different_labels_succeeds() {
    // μt. ?A{x.t} ⊔ μt. ?A{y.t} = μt. ?A{x.t, y.t}
    let t1 = LocalTypeR::mu(
        "t",
        LocalTypeR::recv("A", Label::new("x"), LocalTypeR::var("t")),
    );
    let t2 = LocalTypeR::mu(
        "t",
        LocalTypeR::recv("A", Label::new("y"), LocalTypeR::var("t")),
    );

    let result = merge(&t1, &t2);
    assert!(
        result.is_ok(),
        "Recursive recv types with different labels should succeed"
    );

    let merged = result.unwrap();
    match merged {
        LocalTypeR::Mu { var, body } => {
            assert_eq!(var, "t");
            match body.as_ref() {
                LocalTypeR::Recv { partner, branches } => {
                    assert_eq!(partner, "A");
                    assert_eq!(branches.len(), 2);
                }
                _ => panic!("Expected Recv in body"),
            }
        }
        _ => panic!("Expected Mu"),
    }
}
