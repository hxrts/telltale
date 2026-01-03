//! Choice Propagation Analysis
//!
//! This module implements compile-time verification that all roles
//! learn which branch was selected in choice blocks.
//!
//! # Choice Knowledge Rules
//!
//! 1. The choosing role automatically knows the branch
//! 2. A role learns the branch when it receives a message from a role that knows
//! 3. Knowledge propagates transitively through message passing
//! 4. If a role participates in a branch but never learns which branch,
//!    that's a compile-time error
//!
//! # Example
//!
//! ```text
//! case choose Seller of
//!     Accept => {
//!         Seller -> Buyer: Accepted;  // Buyer learns: Accept
//!     }
//!     Reject => {
//!         Seller -> Buyer: Rejected;  // Buyer learns: Reject
//!     }
//! }
//! ```
//!
//! Here, both branches start with Seller sending to Buyer, so Buyer learns
//! the outcome. If Observer was involved but never received a message,
//! we'd emit an error.

mod analyzer;
mod types;

pub use analyzer::ChoiceAnalyzer;
pub use types::{ChoiceAnalysisResult, ChoiceId, ChoiceKnowledge, KnowledgeSource};

use crate::ast::{Protocol, Role};
use std::collections::HashSet;

/// Check if message types are distinguishing (unique per branch)
pub fn messages_are_distinguishing(messages_per_branch: &[String]) -> bool {
    let unique: HashSet<&String> = messages_per_branch.iter().collect();
    unique.len() == messages_per_branch.len()
}

/// Analyze choice propagation for a choreography
pub fn analyze_choreography_choices(protocol: &Protocol, roles: &[Role]) -> ChoiceAnalysisResult {
    let mut analyzer = ChoiceAnalyzer::new(roles);
    analyzer.analyze(protocol)
}

/// Calculate Levenshtein edit distance between two strings
#[allow(clippy::needless_range_loop)]
fn levenshtein_distance(a: &str, b: &str) -> usize {
    let a_chars: Vec<char> = a.chars().collect();
    let b_chars: Vec<char> = b.chars().collect();
    let a_len = a_chars.len();
    let b_len = b_chars.len();

    if a_len == 0 {
        return b_len;
    }
    if b_len == 0 {
        return a_len;
    }

    let mut matrix = vec![vec![0usize; b_len + 1]; a_len + 1];

    for i in 0..=a_len {
        matrix[i][0] = i;
    }
    for j in 0..=b_len {
        matrix[0][j] = j;
    }

    for i in 1..=a_len {
        for j in 1..=b_len {
            let cost = if a_chars[i - 1] == b_chars[j - 1] {
                0
            } else {
                1
            };
            matrix[i][j] = std::cmp::min(
                std::cmp::min(matrix[i - 1][j] + 1, matrix[i][j - 1] + 1),
                matrix[i - 1][j - 1] + cost,
            );
        }
    }

    matrix[a_len][b_len]
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{MessageType, NonEmptyVec};
    use proc_macro2::Ident;
    use proc_macro2::Span;

    use crate::ast::Branch;

    // Helper to create NonEmptyVec of branches from first + rest
    fn branches(first: Branch, rest: Vec<Branch>) -> NonEmptyVec<Branch> {
        NonEmptyVec::from_head_tail(first, rest)
    }

    fn make_role(name: &str) -> Role {
        Role::new(Ident::new(name, Span::call_site())).unwrap()
    }

    fn make_message(name: &str) -> MessageType {
        MessageType {
            name: Ident::new(name, Span::call_site()),
            type_annotation: None,
            payload: None,
        }
    }

    #[test]
    fn test_simple_informed_choice() {
        // case choose Seller of
        //     Accept => { Seller -> Buyer: Accepted; }
        //     Reject => { Seller -> Buyer: Rejected; }
        // }
        let seller = make_role("Seller");
        let buyer = make_role("Buyer");

        let protocol = Protocol::Choice {
            role: seller.clone(),
            branches: branches(
                Branch {
                    label: Ident::new("Accept", Span::call_site()),
                    guard: None,
                    protocol: Protocol::Send {
                        from: seller.clone(),
                        to: buyer.clone(),
                        message: make_message("Accepted"),
                        continuation: Box::new(Protocol::End),
                        annotations: Default::default(),
                        from_annotations: Default::default(),
                        to_annotations: Default::default(),
                    },
                },
                vec![Branch {
                    label: Ident::new("Reject", Span::call_site()),
                    guard: None,
                    protocol: Protocol::Send {
                        from: seller.clone(),
                        to: buyer.clone(),
                        message: make_message("Rejected"),
                        continuation: Box::new(Protocol::End),
                        annotations: Default::default(),
                        from_annotations: Default::default(),
                        to_annotations: Default::default(),
                    },
                }],
            ),
            annotations: Default::default(),
        };

        let roles = vec![seller, buyer];
        let result = analyze_choreography_choices(&protocol, &roles);

        assert!(result.passed(), "Should pass: {:?}", result.diagnostics);
        assert_eq!(result.choices.len(), 1);

        let choice = &result.choices[0];
        assert!(choice.informed_roles.contains_key("Seller"));
        assert!(choice.informed_roles.contains_key("Buyer"));
        assert!(choice.uninformed_roles.is_empty());
    }

    #[test]
    fn test_uninformed_observer() {
        // case choose Seller of
        //     Accept => { Seller -> Buyer: Accepted; }
        //     Reject => { Seller -> Buyer: Rejected; }
        // }
        // Observer participates but is not informed
        let seller = make_role("Seller");
        let buyer = make_role("Buyer");
        let observer = make_role("Observer");

        let protocol = Protocol::Choice {
            role: seller.clone(),
            branches: branches(
                Branch {
                    label: Ident::new("Accept", Span::call_site()),
                    guard: None,
                    protocol: Protocol::Send {
                        from: seller.clone(),
                        to: buyer.clone(),
                        message: make_message("Accepted"),
                        continuation: Box::new(Protocol::Send {
                            from: buyer.clone(),
                            to: observer.clone(),
                            message: make_message("Done"),
                            continuation: Box::new(Protocol::End),
                            annotations: Default::default(),
                            from_annotations: Default::default(),
                            to_annotations: Default::default(),
                        }),
                        annotations: Default::default(),
                        from_annotations: Default::default(),
                        to_annotations: Default::default(),
                    },
                },
                vec![Branch {
                    label: Ident::new("Reject", Span::call_site()),
                    guard: None,
                    protocol: Protocol::Send {
                        from: seller.clone(),
                        to: buyer.clone(),
                        message: make_message("Rejected"),
                        continuation: Box::new(Protocol::Send {
                            // Observer only gets message in one branch - still uninformed
                            // because the message type is the same ("Done")
                            from: buyer.clone(),
                            to: observer.clone(),
                            message: make_message("Done"),
                            continuation: Box::new(Protocol::End),
                            annotations: Default::default(),
                            from_annotations: Default::default(),
                            to_annotations: Default::default(),
                        }),
                        annotations: Default::default(),
                        from_annotations: Default::default(),
                        to_annotations: Default::default(),
                    },
                }],
            ),
            annotations: Default::default(),
        };

        let roles = vec![seller, buyer, observer];
        let result = analyze_choreography_choices(&protocol, &roles);

        // Observer IS informed because Buyer (who is informed) sends to Observer
        // This is transitive knowledge propagation
        assert!(result.passed(), "Should pass with transitive knowledge");
        assert_eq!(result.choices.len(), 1);

        let choice = &result.choices[0];
        assert!(choice.informed_roles.contains_key("Observer"));
    }

    #[test]
    fn test_truly_uninformed_observer() {
        // Observer participates in only ONE branch - they're uninformed
        let seller = make_role("Seller");
        let buyer = make_role("Buyer");
        let observer = make_role("Observer");

        let protocol = Protocol::Choice {
            role: seller.clone(),
            branches: branches(
                Branch {
                    label: Ident::new("Accept", Span::call_site()),
                    guard: None,
                    protocol: Protocol::Send {
                        from: seller.clone(),
                        to: buyer.clone(),
                        message: make_message("Accepted"),
                        continuation: Box::new(Protocol::Send {
                            from: buyer.clone(),
                            to: observer.clone(),
                            message: make_message("Notify"),
                            continuation: Box::new(Protocol::End),
                            annotations: Default::default(),
                            from_annotations: Default::default(),
                            to_annotations: Default::default(),
                        }),
                        annotations: Default::default(),
                        from_annotations: Default::default(),
                        to_annotations: Default::default(),
                    },
                },
                vec![Branch {
                    label: Ident::new("Reject", Span::call_site()),
                    guard: None,
                    protocol: Protocol::Send {
                        from: seller.clone(),
                        to: buyer.clone(),
                        message: make_message("Rejected"),
                        continuation: Box::new(Protocol::End), // Observer not involved!
                        annotations: Default::default(),
                        from_annotations: Default::default(),
                        to_annotations: Default::default(),
                    },
                }],
            ),
            annotations: Default::default(),
        };

        let roles = vec![seller, buyer, observer];
        let result = analyze_choreography_choices(&protocol, &roles);

        // Observer only participates in Accept branch - uninformed about choice
        assert!(!result.passed(), "Should fail: Observer uninformed");
        assert_eq!(result.error_count(), 1);

        let choice = &result.choices[0];
        assert!(choice.uninformed_roles.contains("Observer"));
    }

    #[test]
    fn test_transitive_knowledge() {
        // A -> B, B -> C means C knows transitively
        let a = make_role("A");
        let b = make_role("B");
        let c = make_role("C");

        let protocol = Protocol::Choice {
            role: a.clone(),
            branches: branches(
                Branch {
                    label: Ident::new("Left", Span::call_site()),
                    guard: None,
                    protocol: Protocol::Send {
                        from: a.clone(),
                        to: b.clone(),
                        message: make_message("L"),
                        continuation: Box::new(Protocol::Send {
                            from: b.clone(),
                            to: c.clone(),
                            message: make_message("Info"),
                            continuation: Box::new(Protocol::End),
                            annotations: Default::default(),
                            from_annotations: Default::default(),
                            to_annotations: Default::default(),
                        }),
                        annotations: Default::default(),
                        from_annotations: Default::default(),
                        to_annotations: Default::default(),
                    },
                },
                vec![Branch {
                    label: Ident::new("Right", Span::call_site()),
                    guard: None,
                    protocol: Protocol::Send {
                        from: a.clone(),
                        to: b.clone(),
                        message: make_message("R"),
                        continuation: Box::new(Protocol::Send {
                            from: b.clone(),
                            to: c.clone(),
                            message: make_message("Info"),
                            continuation: Box::new(Protocol::End),
                            annotations: Default::default(),
                            from_annotations: Default::default(),
                            to_annotations: Default::default(),
                        }),
                        annotations: Default::default(),
                        from_annotations: Default::default(),
                        to_annotations: Default::default(),
                    },
                }],
            ),
            annotations: Default::default(),
        };

        let roles = vec![a, b, c];
        let result = analyze_choreography_choices(&protocol, &roles);

        assert!(result.passed());

        let choice = &result.choices[0];
        assert!(choice.informed_roles.contains_key("A")); // Chooser
        assert!(choice.informed_roles.contains_key("B")); // Direct message from chooser
        assert!(choice.informed_roles.contains_key("C")); // Informed via B

        // C is informed either via MessageFrom (receives in all branches) or Transitive
        match &choice.informed_roles["C"] {
            KnowledgeSource::MessageFrom { sender, .. } => {
                assert_eq!(sender, "B", "C should learn from B");
            }
            KnowledgeSource::Transitive { via, .. } => {
                assert_eq!(via, "B", "C should learn transitively via B");
            }
            other => panic!("Expected C to learn from B, got {:?}", other),
        }
    }

    #[test]
    fn test_choice_id() {
        let id1 = ChoiceId::new("Seller", 0);
        assert_eq!(id1.display(), "choice Seller #0");

        let id2 = ChoiceId::nested(&id1, "Buyer", 0);
        assert_eq!(id2.display(), "choice Buyer #0 (in Seller:0)");
    }

    #[test]
    fn test_messages_are_distinguishing() {
        assert!(messages_are_distinguishing(&[
            "A".to_string(),
            "B".to_string()
        ]));
        assert!(!messages_are_distinguishing(&[
            "A".to_string(),
            "A".to_string()
        ]));
        assert!(messages_are_distinguishing(&[
            "X".to_string(),
            "Y".to_string(),
            "Z".to_string()
        ]));
    }

    #[test]
    fn test_levenshtein_distance() {
        assert_eq!(levenshtein_distance("", ""), 0);
        assert_eq!(levenshtein_distance("abc", "abc"), 0);
        assert_eq!(levenshtein_distance("abc", "abd"), 1);
        assert_eq!(levenshtein_distance("abc", "abcd"), 1);
        assert_eq!(levenshtein_distance("Buyer", "Buyr"), 1);
        assert_eq!(levenshtein_distance("Seller", "Seler"), 1);
        assert_eq!(levenshtein_distance("Observer", "Observr"), 1);
        assert_eq!(levenshtein_distance("Alice", "Bob"), 5);
    }

    #[test]
    fn test_find_similar_role() {
        let roles = vec![
            make_role("Seller"),
            make_role("Buyer"),
            make_role("Observer"),
        ];
        let analyzer = ChoiceAnalyzer::new(&roles);

        // Typo should suggest similar role
        assert_eq!(
            analyzer.find_similar_role("Seler"),
            Some(&"Seller".to_string())
        );
        assert_eq!(
            analyzer.find_similar_role("Buyr"),
            Some(&"Buyer".to_string())
        );
        assert_eq!(
            analyzer.find_similar_role("Observr"),
            Some(&"Observer".to_string())
        );

        // Completely different name should not suggest
        assert_eq!(analyzer.find_similar_role("XYZ"), None);
        assert_eq!(analyzer.find_similar_role("Coordinator"), None);

        // Exact match should not suggest itself
        assert_eq!(analyzer.find_similar_role("Seller"), None);
    }

    #[test]
    fn test_branch_participation_tracking() {
        // Observer participates in only ONE branch
        let seller = make_role("Seller");
        let buyer = make_role("Buyer");
        let observer = make_role("Observer");

        let protocol = Protocol::Choice {
            role: seller.clone(),
            branches: branches(
                Branch {
                    label: Ident::new("Accept", Span::call_site()),
                    guard: None,
                    protocol: Protocol::Send {
                        from: seller.clone(),
                        to: buyer.clone(),
                        message: make_message("Accepted"),
                        continuation: Box::new(Protocol::Send {
                            from: buyer.clone(),
                            to: observer.clone(),
                            message: make_message("Notify"),
                            continuation: Box::new(Protocol::End),
                            annotations: Default::default(),
                            from_annotations: Default::default(),
                            to_annotations: Default::default(),
                        }),
                        annotations: Default::default(),
                        from_annotations: Default::default(),
                        to_annotations: Default::default(),
                    },
                },
                vec![Branch {
                    label: Ident::new("Reject", Span::call_site()),
                    guard: None,
                    protocol: Protocol::Send {
                        from: seller.clone(),
                        to: buyer.clone(),
                        message: make_message("Rejected"),
                        continuation: Box::new(Protocol::End),
                        annotations: Default::default(),
                        from_annotations: Default::default(),
                        to_annotations: Default::default(),
                    },
                }],
            ),
            annotations: Default::default(),
        };

        let roles = vec![seller, buyer, observer];
        let result = analyze_choreography_choices(&protocol, &roles);

        let choice = &result.choices[0];

        // Check branch participation tracking
        assert!(choice.branch_participation.contains_key("Accept"));
        assert!(choice.branch_participation.contains_key("Reject"));

        // Observer should participate in Accept but not Reject
        let accept_roles = &choice.branch_participation["Accept"];
        let reject_roles = &choice.branch_participation["Reject"];

        assert!(
            accept_roles.contains("Observer"),
            "Observer should be in Accept"
        );
        assert!(
            !reject_roles.contains("Observer"),
            "Observer should NOT be in Reject"
        );

        // Seller and Buyer should be in both branches
        assert!(accept_roles.contains("Seller"));
        assert!(accept_roles.contains("Buyer"));
        assert!(reject_roles.contains("Seller"));
        assert!(reject_roles.contains("Buyer"));
    }

    #[test]
    fn test_declared_roles_methods() {
        let roles = vec![make_role("Alice"), make_role("Bob"), make_role("Carol")];
        let analyzer = ChoiceAnalyzer::new(&roles);

        assert_eq!(analyzer.declared_roles().len(), 3);
        assert!(analyzer.is_role_declared("Alice"));
        assert!(analyzer.is_role_declared("Bob"));
        assert!(analyzer.is_role_declared("Carol"));
        assert!(!analyzer.is_role_declared("Dave"));
    }
}
