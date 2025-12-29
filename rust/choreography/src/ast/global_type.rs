//! Global Types for Multiparty Session Type Protocols
//!
//! This module re-exports the core global types from `rumpsteak-types`.
//! These types describe protocols from a bird's-eye view.
//!
//! Based on: "A Very Gentle Introduction to Multiparty Session Types" (Yoshida & Gheri)
//!
//! # Lean Correspondence
//!
//! These types mirror the definitions in `lean/Rumpsteak/Protocol/GlobalType.lean`.

// Re-export all core types from rumpsteak-types
pub use rumpsteak_types::{GlobalType, Label, PayloadSort};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_protocol() {
        // A -> B: hello. end
        let g = GlobalType::send("A", "B", Label::new("hello"), GlobalType::End);
        assert!(g.well_formed());
        assert_eq!(g.roles().len(), 2);
        assert!(g.mentions_role("A"));
        assert!(g.mentions_role("B"));
    }

    #[test]
    fn test_recursive_protocol() {
        // μt. A -> B: msg. t
        let g = GlobalType::mu(
            "t",
            GlobalType::send("A", "B", Label::new("msg"), GlobalType::var("t")),
        );
        assert!(g.well_formed());
        assert!(g.all_vars_bound());
    }

    #[test]
    fn test_payload_sort() {
        let sort = PayloadSort::prod(PayloadSort::Nat, PayloadSort::Bool);
        assert!(!sort.is_simple());

        let label = Label::with_sort("data", sort);
        assert_eq!(label.name, "data");
    }
}
