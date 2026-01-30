//! Cross-validation tests for DSL and theory projection implementations.
//!
//! These tests verify that the DSL projection (choreography crate) produces
//! equivalent results to the theory projection (theory crate) for protocols
//! that are expressible in both systems.
//!
//! ## Test Strategy
//!
//! For each protocol in the common subset:
//! 1. Parse DSL → Choreography
//! 2. Project using DSL projection → LocalType
//! 3. Convert Choreography → GlobalType
//! 4. Project using theory projection → LocalTypeR
//! 5. Convert LocalType → LocalTypeR
//! 6. Compare results for structural equivalence
//!
//! ## Common Subset
//!
//! Features testable across both implementations:
//! - Linear protocols (sequences of send/recv)
//! - Binary and multi-way choices
//! - Recursive protocols
//! - Multi-party protocols (3+ roles)
//!
//! Features NOT tested (DSL-only):
//! - Dynamic roles, broadcasts, local choices, parallel, extensions

#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

use telltale_choreography::ast::{
    choreography_to_global, local_to_local_r, local_types_equivalent, Choreography, ConversionError,
};
use telltale_choreography::compiler::parser::parse_choreography_str;
use telltale_choreography::compiler::projection::project;
use telltale_theory::projection::project as theory_project;

/// Parse a DSL choreography string.
fn parse_choreography(input: &str) -> Choreography {
    parse_choreography_str(input).expect("Failed to parse choreography")
}

/// Find a role by name in a choreography.
fn find_role<'a>(
    choreography: &'a Choreography,
    name: &str,
) -> Option<&'a telltale_choreography::ast::Role> {
    choreography.roles.iter().find(|r| *r.name() == name)
}

/// Helper to run the cross-validation for a given DSL input and role.
fn validate_projection_equivalence(dsl_input: &str, role_name: &str) -> Result<(), String> {
    // Step 1: Parse DSL to Choreography
    let choreography = parse_choreography(dsl_input);

    // Find the role in the choreography
    let role = find_role(&choreography, role_name)
        .ok_or_else(|| format!("Role {} not found in choreography", role_name))?;

    // Step 2: Project using DSL projection
    let dsl_local =
        project(&choreography, role).map_err(|e| format!("DSL projection failed: {:?}", e))?;

    // Step 3: Convert Choreography to GlobalType
    let global = match choreography_to_global(&choreography) {
        Ok(g) => g,
        Err(ConversionError::UnsupportedFeature { feature, .. }) => {
            // Skip tests for DSL-only features
            return Err(format!("Skipped: {} is DSL-only feature", feature));
        }
        Err(e) => return Err(format!("GlobalType conversion failed: {:?}", e)),
    };

    // Step 4: Project using theory projection
    let theory_local = theory_project(&global, role_name)
        .map_err(|e| format!("Theory projection failed: {:?}", e))?;

    // Step 5: Convert DSL LocalType to LocalTypeR for comparison
    let dsl_local_r = local_to_local_r(&dsl_local)
        .map_err(|e| format!("LocalType conversion failed: {:?}", e))?;

    // Step 6: Compare results
    if local_types_equivalent(&dsl_local_r, &theory_local) {
        Ok(())
    } else {
        Err(format!(
            "Projections differ for role {}:\n  DSL:    {:?}\n  Theory: {:?}",
            role_name, dsl_local_r, theory_local
        ))
    }
}

// ============================================================================
// Simple Linear Protocols
// ============================================================================

#[test]
fn test_simple_send() {
    let dsl = r#"
protocol Simple = {
    roles A, B
    A -> B: Msg
}
    "#;

    validate_projection_equivalence(dsl, "A").expect("A projection should match");
    validate_projection_equivalence(dsl, "B").expect("B projection should match");
}

#[test]
fn test_two_message_sequence() {
    let dsl = r#"
protocol TwoMessages = {
    roles A, B
    A -> B: First
    B -> A: Second
}
    "#;

    validate_projection_equivalence(dsl, "A").expect("A projection should match");
    validate_projection_equivalence(dsl, "B").expect("B projection should match");
}

#[test]
fn test_three_message_chain() {
    let dsl = r#"
protocol Chain = {
    roles A, B
    A -> B: One
    B -> A: Two
    A -> B: Three
}
    "#;

    validate_projection_equivalence(dsl, "A").expect("A projection should match");
    validate_projection_equivalence(dsl, "B").expect("B projection should match");
}

// ============================================================================
// Three-Party Protocols
// ============================================================================

#[test]
fn test_three_party_ring() {
    let dsl = r#"
protocol Ring = {
    roles A, B, C
    A -> B: Msg1
    B -> C: Msg2
    C -> A: Msg3
}
    "#;

    validate_projection_equivalence(dsl, "A").expect("A projection should match");
    validate_projection_equivalence(dsl, "B").expect("B projection should match");
    validate_projection_equivalence(dsl, "C").expect("C projection should match");
}

#[test]
fn test_three_party_star() {
    let dsl = r#"
protocol Star = {
    roles Hub, Spoke1, Spoke2
    Spoke1 -> Hub: Request1
    Hub -> Spoke1: Response1
    Spoke2 -> Hub: Request2
    Hub -> Spoke2: Response2
}
    "#;

    validate_projection_equivalence(dsl, "Hub").expect("Hub projection should match");
    validate_projection_equivalence(dsl, "Spoke1").expect("Spoke1 projection should match");
    validate_projection_equivalence(dsl, "Spoke2").expect("Spoke2 projection should match");
}

// ============================================================================
// Choice Protocols
// ============================================================================

#[test]
fn test_binary_choice() {
    let dsl = r#"
protocol BinaryChoice = {
    roles Client, Server
    choice at Client {
        Accept -> {
            Client -> Server: Accept
        }
        Reject -> {
            Client -> Server: Reject
        }
    }
}
    "#;

    validate_projection_equivalence(dsl, "Client").expect("Client projection should match");
    validate_projection_equivalence(dsl, "Server").expect("Server projection should match");
}

#[test]
fn test_choice_with_continuation() {
    let dsl = r#"
protocol ChoiceWithCont = {
    roles Client, Server
    choice at Client {
        Success -> {
            Client -> Server: Success
            Server -> Client: Data
        }
        Failure -> {
            Client -> Server: Failure
            Server -> Client: Error
        }
    }
}
    "#;

    validate_projection_equivalence(dsl, "Client").expect("Client projection should match");
    validate_projection_equivalence(dsl, "Server").expect("Server projection should match");
}

#[test]
fn test_three_way_choice() {
    let dsl = r#"
protocol ThreeWayChoice = {
    roles A, B
    choice at A {
        Option1 -> {
            A -> B: Option1
        }
        Option2 -> {
            A -> B: Option2
        }
        Option3 -> {
            A -> B: Option3
        }
    }
}
    "#;

    validate_projection_equivalence(dsl, "A").expect("A projection should match");
    validate_projection_equivalence(dsl, "B").expect("B projection should match");
}

// ============================================================================
// Recursive Protocols
// ============================================================================

#[test]
fn test_simple_recursion() {
    let dsl = r#"
protocol SimpleRec = {
    roles A, B
    rec Loop {
        A -> B: Ping
        B -> A: Pong
        continue Loop
    }
}
    "#;

    validate_projection_equivalence(dsl, "A").expect("A projection should match");
    validate_projection_equivalence(dsl, "B").expect("B projection should match");
}

#[test]
fn test_recursion_with_choice() {
    let dsl = r#"
protocol RecWithChoice = {
    roles Client, Server
    rec MainLoop {
        choice at Client {
            Continue -> {
                Client -> Server: Continue
                Server -> Client: Data
                continue MainLoop
            }
            Stop -> {
                Client -> Server: Stop
            }
        }
    }
}
    "#;

    validate_projection_equivalence(dsl, "Client").expect("Client projection should match");
    validate_projection_equivalence(dsl, "Server").expect("Server projection should match");
}

// ============================================================================
// Complex Protocols
// ============================================================================

#[test]
fn test_nested_choice() {
    let dsl = r#"
protocol NestedChoice = {
    roles A, B
    choice at A {
        Outer1 -> {
            A -> B: Outer1
            choice at B {
                Inner1 -> {
                    B -> A: Inner1
                }
                Inner2 -> {
                    B -> A: Inner2
                }
            }
        }
        Outer2 -> {
            A -> B: Outer2
        }
    }
}
    "#;

    validate_projection_equivalence(dsl, "A").expect("A projection should match");
    validate_projection_equivalence(dsl, "B").expect("B projection should match");
}

#[test]
fn test_three_party_choice() {
    let dsl = r#"
protocol ThreePartyChoice = {
    roles A, B, C
    choice at A {
        Left -> {
            A -> B: Left
            B -> C: Notify
        }
        Right -> {
            A -> B: Right
            B -> C: Notify
        }
    }
}
    "#;

    validate_projection_equivalence(dsl, "A").expect("A projection should match");
    validate_projection_equivalence(dsl, "B").expect("B projection should match");
    validate_projection_equivalence(dsl, "C").expect("C projection should match");
}

// ============================================================================
// Non-Participant Merge Scenarios
// ============================================================================

#[test]
fn test_non_participant_mergeable() {
    // C is not involved in A->B choice, but sends the same message in both branches
    // This should be mergeable
    let dsl = r#"
protocol Mergeable = {
    roles A, B, C
    choice at A {
        Left -> {
            A -> B: Left
            C -> B: Status
        }
        Right -> {
            A -> B: Right
            C -> B: Status
        }
    }
}
    "#;

    validate_projection_equivalence(dsl, "A").expect("A projection should match");
    validate_projection_equivalence(dsl, "B").expect("B projection should match");
    validate_projection_equivalence(dsl, "C").expect("C projection should match");
}

// ============================================================================
// Edge Cases
// ============================================================================

#[test]
fn test_single_role_in_choice_branch() {
    let dsl = r#"
protocol SingleRoleBranch = {
    roles A, B
    A -> B: Start
    choice at A {
        Done -> {
            A -> B: Done
        }
        More -> {
            A -> B: More
            A -> B: Extra
        }
    }
}
    "#;

    validate_projection_equivalence(dsl, "A").expect("A projection should match");
    validate_projection_equivalence(dsl, "B").expect("B projection should match");
}

#[test]
fn test_deep_nesting() {
    let dsl = r#"
protocol DeepNesting = {
    roles A, B
    A -> B: Level1
    B -> A: Level2
    A -> B: Level3
    B -> A: Level4
    A -> B: Level5
}
    "#;

    validate_projection_equivalence(dsl, "A").expect("A projection should match");
    validate_projection_equivalence(dsl, "B").expect("B projection should match");
}

// ============================================================================
// Validation Helpers
// ============================================================================

/// Run equivalence check for all roles in a choreography
fn validate_all_roles(dsl: &str) -> Vec<(String, Result<(), String>)> {
    let choreography = parse_choreography(dsl);
    choreography
        .roles
        .iter()
        .map(|role| {
            let name = role.name().to_string();
            let result = validate_projection_equivalence(dsl, &name);
            (name, result)
        })
        .collect()
}

#[test]
fn test_comprehensive_validation() {
    let test_cases = [
        // Simple protocols
        r#"protocol T1 = { roles A, B  A -> B: M }"#,
        // Request-response
        r#"protocol T2 = { roles C, S  C -> S: Req  S -> C: Resp }"#,
        // Three-party
        r#"protocol T3 = { roles X, Y, Z  X -> Y: A  Y -> Z: B  Z -> X: C }"#,
    ];

    for (i, dsl) in test_cases.iter().enumerate() {
        let results = validate_all_roles(dsl);
        for (role, result) in results {
            if let Err(e) = result {
                if !e.starts_with("Skipped:") {
                    panic!("Test case {} failed for role {}: {}", i, role, e);
                }
            }
        }
    }
}
