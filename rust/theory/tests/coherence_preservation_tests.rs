//! Coherence Preservation Tests
//!
//! Tests that verify coherence and well-formedness properties are preserved
//! across session type operations (projection, duality, merge).

use proptest::prelude::*;
use telltale_theory::{
    check_coherent, dual, merge, project, projectable, validate_global, validate_local,
    well_formedness::unique_labels_local,
};
use telltale_types::{GlobalType, Label, LocalTypeR};

// ============================================================================
// Helpers
// ============================================================================

/// Generate a well-formed global type with distinct labels.
fn well_formed_global(depth: usize) -> BoxedStrategy<GlobalType> {
    if depth == 0 {
        Just(GlobalType::End).boxed()
    } else {
        prop_oneof![
            // Simple send
            (any::<u8>(), any::<u8>(), well_formed_global(depth - 1)).prop_filter_map(
                "distinct roles",
                |(a, b, cont)| {
                    let sender = format!("Role{}", a % 4);
                    let receiver = format!("Role{}", b % 4);
                    if sender != receiver {
                        Some(GlobalType::send(sender, receiver, Label::new("msg"), cont))
                    } else {
                        None
                    }
                }
            ),
            // Binary choice with distinct labels
            (
                any::<u8>(),
                any::<u8>(),
                well_formed_global(depth - 1),
                well_formed_global(depth - 1)
            )
                .prop_filter_map("distinct roles for choice", |(a, b, c1, c2)| {
                    let sender = format!("Role{}", a % 4);
                    let receiver = format!("Role{}", b % 4);
                    if sender != receiver {
                        Some(GlobalType::comm(
                            sender,
                            receiver,
                            vec![(Label::new("yes"), c1), (Label::new("no"), c2)],
                        ))
                    } else {
                        None
                    }
                }),
            // Recursive type
            well_formed_global(depth - 1).prop_map(|body| {
                GlobalType::mu(
                    "t",
                    GlobalType::comm(
                        "A",
                        "B",
                        vec![
                            (Label::new("continue"), GlobalType::var("t")),
                            (Label::new("stop"), body),
                        ],
                    ),
                )
            }),
        ]
        .boxed()
    }
}

/// Generate a well-formed local type with distinct labels.
fn well_formed_local(depth: usize) -> BoxedStrategy<LocalTypeR> {
    if depth == 0 {
        Just(LocalTypeR::End).boxed()
    } else {
        prop_oneof![
            // Simple send
            (any::<u8>(), well_formed_local(depth - 1)).prop_map(|(p, cont)| {
                let partner = format!("Role{}", p % 4);
                LocalTypeR::send(partner, Label::new("msg"), cont)
            }),
            // Simple recv
            (any::<u8>(), well_formed_local(depth - 1)).prop_map(|(p, cont)| {
                let partner = format!("Role{}", p % 4);
                LocalTypeR::recv(partner, Label::new("msg"), cont)
            }),
            // Send choice
            (
                any::<u8>(),
                well_formed_local(depth - 1),
                well_formed_local(depth - 1)
            )
                .prop_map(|(p, c1, c2)| {
                    let partner = format!("Role{}", p % 4);
                    LocalTypeR::send_choice(
                        partner,
                        vec![(Label::new("left"), None, c1), (Label::new("right"), None, c2)],
                    )
                }),
            // Recv choice
            (
                any::<u8>(),
                well_formed_local(depth - 1),
                well_formed_local(depth - 1)
            )
                .prop_map(|(p, c1, c2)| {
                    let partner = format!("Role{}", p % 4);
                    LocalTypeR::recv_choice(
                        partner,
                        vec![(Label::new("left"), None, c1), (Label::new("right"), None, c2)],
                    )
                }),
        ]
        .boxed()
    }
}

// ============================================================================
// Property Tests
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    // -------------------------------------------------------------------------
    // Projection Preserves Well-Formedness
    // -------------------------------------------------------------------------

    /// If a global type is well-formed, its projection to any participating role
    /// should produce a well-formed local type.
    #[test]
    fn prop_projection_preserves_well_formedness(g in well_formed_global(3)) {
        // Skip if not well-formed (shouldn't happen with our generator)
        if validate_global(&g).is_err() {
            return Ok(());
        }

        // Get all roles from the global type
        let roles = g.roles();

        for role in &roles {
            match project(&g, role) {
                Ok(local) => {
                    // Projected type should be well-formed
                    let validation = validate_local(&local);
                    prop_assert!(
                        validation.is_ok(),
                        "Projection for role {} produced invalid local type: {:?}",
                        role,
                        validation
                    );
                }
                Err(_) => {
                    // Projection can fail for some types (e.g., non-mergeable branches)
                    // This is acceptable, as long as successful projections are valid
                }
            }
        }
    }

    /// If projection succeeds for all roles, coherence predicates should be consistent.
    #[test]
    fn prop_successful_projection_implies_consistency(g in well_formed_global(2)) {
        let roles = g.roles();
        let all_project_ok = roles.iter().all(|r| project(&g, r).is_ok());

        if all_project_ok {
            let bundle = check_coherent(&g);
            // If all projections succeed, size and action should pass
            prop_assert!(bundle.size, "All projections succeeded but size failed");
            prop_assert!(bundle.action, "All projections succeeded but action failed");
            // projectable should also be true if all projections succeed
            prop_assert!(bundle.projectable, "All projections succeeded but projectable returned false");
        }
    }

    /// Coherent types should be projectable for all roles.
    #[test]
    fn prop_coherent_implies_projectable(g in well_formed_global(2)) {
        let bundle = check_coherent(&g);

        if bundle.is_coherent() {
            let roles = g.roles();
            for role in &roles {
                let result = project(&g, role);
                prop_assert!(
                    result.is_ok(),
                    "Coherent type failed to project for role {}: {:?}",
                    role,
                    result
                );
            }
        }
    }

    // -------------------------------------------------------------------------
    // Duality Preserves Well-Formedness
    // -------------------------------------------------------------------------

    /// If a local type is well-formed, its dual should also be well-formed.
    #[test]
    fn prop_duality_preserves_well_formedness(lt in well_formed_local(3)) {
        if validate_local(&lt).is_err() {
            return Ok(());
        }

        let dual_type = dual(&lt);
        let validation = validate_local(&dual_type);

        prop_assert!(
            validation.is_ok(),
            "Dual of well-formed local type is not well-formed: {:?}",
            validation
        );
    }

    /// Duality preserves well-formedness (includes unique labels check).
    #[test]
    fn prop_duality_preserves_labels(lt in well_formed_local(3)) {
        if validate_local(&lt).is_err() {
            return Ok(());
        }

        let dual_type = dual(&lt);
        prop_assert!(
            validate_local(&dual_type).is_ok(),
            "Dual type validation failed"
        );
    }

    // -------------------------------------------------------------------------
    // Merge Preserves Well-Formedness
    // -------------------------------------------------------------------------

    /// If two local types with the same partner can be merged, the result is well-formed.
    #[test]
    fn prop_merge_preserves_well_formedness(
        lt1 in well_formed_local(2),
        lt2 in well_formed_local(2)
    ) {
        // Both inputs must be well-formed
        if validate_local(&lt1).is_err() || validate_local(&lt2).is_err() {
            return Ok(());
        }

        // Try to merge (may fail if types are incompatible)
        if let Ok(merged) = merge(&lt1, &lt2) {
            let validation = validate_local(&merged);
            prop_assert!(
                validation.is_ok(),
                "Merge of well-formed types produced invalid type: {:?}",
                validation
            );
        }
    }

    /// Merge preserves unique labels (if both inputs have unique labels).
    #[test]
    fn prop_merge_preserves_unique_labels(
        lt1 in well_formed_local(2),
        lt2 in well_formed_local(2)
    ) {
        if !unique_labels_local(&lt1) || !unique_labels_local(&lt2) {
            return Ok(());
        }

        if let Ok(merged) = merge(&lt1, &lt2) {
            prop_assert!(
                unique_labels_local(&merged),
                "Merged type has duplicate labels"
            );
        }
    }

    // -------------------------------------------------------------------------
    // Coherence Bundle Consistency
    // -------------------------------------------------------------------------

    /// A well-formed global type should have consistent coherence bundle values.
    #[test]
    fn prop_coherence_bundle_consistency(g in well_formed_global(3)) {
        let bundle = check_coherent(&g);

        // If all individual predicates pass, is_coherent should be true
        if bundle.linear && bundle.size && bundle.action
            && bundle.uniq_labels && bundle.projectable && bundle.good
        {
            prop_assert!(bundle.is_coherent());
        }

        // If is_coherent is false, at least one predicate must fail
        if !bundle.is_coherent() {
            prop_assert!(
                !bundle.linear || !bundle.size || !bundle.action
                    || !bundle.uniq_labels || !bundle.projectable || !bundle.good
            );
        }
    }

    /// Projection failure should be reflected in projectable check (one direction).
    /// Note: projectable() is a simplified check, so it may return true even when
    /// projection fails (false positive). But if projection succeeds for all roles,
    /// projectable should definitely return true.
    #[test]
    fn prop_projection_success_implies_projectable(g in well_formed_global(2)) {
        if !g.well_formed() {
            return Ok(());
        }

        let roles = g.roles();
        let all_project_ok = roles.iter().all(|r| project(&g, r).is_ok());

        if all_project_ok {
            // If all projections succeed, projectable should return true
            let is_projectable = projectable(&g);
            prop_assert!(
                is_projectable,
                "All roles projected successfully but projectable() returned false"
            );
        }
    }
}

// ============================================================================
// Deterministic Tests
// ============================================================================

#[test]
fn test_simple_send_projection_preserves_well_formedness() {
    let g = GlobalType::send("A", "B", Label::new("hello"), GlobalType::End);
    assert!(validate_global(&g).is_ok());

    let local_a = project(&g, "A").unwrap();
    let local_b = project(&g, "B").unwrap();

    assert!(validate_local(&local_a).is_ok());
    assert!(validate_local(&local_b).is_ok());
}

#[test]
fn test_choice_projection_preserves_well_formedness() {
    let g = GlobalType::comm(
        "A",
        "B",
        vec![
            (Label::new("accept"), GlobalType::End),
            (Label::new("reject"), GlobalType::End),
        ],
    );
    assert!(validate_global(&g).is_ok());

    let local_a = project(&g, "A").unwrap();
    let local_b = project(&g, "B").unwrap();

    assert!(validate_local(&local_a).is_ok());
    assert!(validate_local(&local_b).is_ok());
}

#[test]
fn test_three_party_projection_preserves_well_formedness() {
    // A -> B: req. B -> C: fwd. C -> B: resp. B -> A: result. end
    let g = GlobalType::send(
        "A",
        "B",
        Label::new("request"),
        GlobalType::send(
            "B",
            "C",
            Label::new("forward"),
            GlobalType::send(
                "C",
                "B",
                Label::new("response"),
                GlobalType::send("B", "A", Label::new("result"), GlobalType::End),
            ),
        ),
    );

    assert!(validate_global(&g).is_ok());

    for role in ["A", "B", "C"] {
        let local = project(&g, role).unwrap();
        assert!(
            validate_local(&local).is_ok(),
            "Projection for {} is not well-formed",
            role
        );
    }
}

#[test]
fn test_recursive_projection_preserves_well_formedness() {
    let g = GlobalType::mu(
        "t",
        GlobalType::comm(
            "A",
            "B",
            vec![
                (Label::new("continue"), GlobalType::var("t")),
                (Label::new("stop"), GlobalType::End),
            ],
        ),
    );

    assert!(validate_global(&g).is_ok());

    let local_a = project(&g, "A").unwrap();
    let local_b = project(&g, "B").unwrap();

    assert!(validate_local(&local_a).is_ok());
    assert!(validate_local(&local_b).is_ok());
}

#[test]
fn test_duality_preserves_well_formedness() {
    let lt = LocalTypeR::send(
        "B",
        Label::new("request"),
        LocalTypeR::recv("B", Label::new("response"), LocalTypeR::End),
    );

    assert!(validate_local(&lt).is_ok());

    let dual_type = dual(&lt);
    assert!(validate_local(&dual_type).is_ok());
}

#[test]
fn test_duality_preserves_unique_labels() {
    let lt = LocalTypeR::send_choice(
        "B",
        vec![
            (Label::new("opt1"), None, LocalTypeR::End),
            (Label::new("opt2"), None, LocalTypeR::End),
            (Label::new("opt3"), None, LocalTypeR::End),
        ],
    );

    assert!(validate_local(&lt).is_ok());
    let dual_type = dual(&lt);
    assert!(validate_local(&dual_type).is_ok());
}

#[test]
fn test_merge_identical_types() {
    let lt = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
    let merged = merge(&lt, &lt).unwrap();

    assert!(validate_local(&merged).is_ok());
    assert_eq!(merged, lt);
}

#[test]
fn test_merge_end_types() {
    let merged = merge(&LocalTypeR::End, &LocalTypeR::End).unwrap();
    assert!(validate_local(&merged).is_ok());
    assert_eq!(merged, LocalTypeR::End);
}

#[test]
fn test_coherent_simple_protocol() {
    let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
    let bundle = check_coherent(&g);

    assert!(bundle.linear);
    assert!(bundle.size);
    assert!(bundle.action);
    assert!(bundle.uniq_labels);
    assert!(bundle.projectable);
    assert!(bundle.good);
    assert!(bundle.is_coherent());
}

#[test]
fn test_incoherent_self_comm() {
    let g = GlobalType::send("A", "A", Label::new("msg"), GlobalType::End);
    let bundle = check_coherent(&g);

    assert!(!bundle.action);
    assert!(!bundle.is_coherent());
}

#[test]
fn test_incoherent_duplicate_labels() {
    let g = GlobalType::comm(
        "A",
        "B",
        vec![
            (Label::new("dup"), GlobalType::End),
            (Label::new("dup"), GlobalType::End),
        ],
    );
    let bundle = check_coherent(&g);

    assert!(!bundle.uniq_labels);
    assert!(!bundle.is_coherent());
}

#[test]
fn test_incoherent_empty_branches() {
    let g = GlobalType::Comm {
        sender: "A".to_string(),
        receiver: "B".to_string(),
        branches: vec![],
    };
    let bundle = check_coherent(&g);

    assert!(!bundle.size);
    assert!(!bundle.is_coherent());
}

#[test]
fn test_coherent_recursive_protocol() {
    let g = GlobalType::mu(
        "t",
        GlobalType::comm(
            "Server",
            "Client",
            vec![
                (
                    Label::new("data"),
                    GlobalType::send("Client", "Server", Label::new("ack"), GlobalType::var("t")),
                ),
                (Label::new("done"), GlobalType::End),
            ],
        ),
    );

    let bundle = check_coherent(&g);
    assert!(bundle.is_coherent());

    // Verify projection works for all roles
    for role in ["Server", "Client"] {
        assert!(project(&g, role).is_ok());
    }
}

#[test]
fn test_projection_of_coherent_type() {
    // A three-party protocol: A -> B: req. B -> C: fwd. C -> A: result. end
    let g = GlobalType::send(
        "A",
        "B",
        Label::new("request"),
        GlobalType::send(
            "B",
            "C",
            Label::new("forward"),
            GlobalType::send("C", "A", Label::new("result"), GlobalType::End),
        ),
    );

    assert!(check_coherent(&g).is_coherent());

    // All projections should be well-formed
    for role in ["A", "B", "C"] {
        let local = project(&g, role).unwrap();
        assert!(
            validate_local(&local).is_ok(),
            "Role {} projection not well-formed",
            role
        );
    }
}

#[test]
fn test_merge_branch_choices() {
    // Two sends with the same partner but different labels should merge
    let lt1 = LocalTypeR::send("B", Label::new("opt1"), LocalTypeR::End);
    let lt2 = LocalTypeR::send("B", Label::new("opt2"), LocalTypeR::End);

    // Merge may or may not succeed depending on merge semantics
    // The key property is: if it succeeds, result is well-formed
    if let Ok(merged) = merge(&lt1, &lt2) {
        assert!(validate_local(&merged).is_ok());
    }
}

#[test]
fn test_recursive_merge() {
    let lt = LocalTypeR::mu(
        "t",
        LocalTypeR::send("B", Label::new("msg"), LocalTypeR::var("t")),
    );

    // Merging identical recursive types should work
    let merged = merge(&lt, &lt).unwrap();
    assert!(validate_local(&merged).is_ok());
}
