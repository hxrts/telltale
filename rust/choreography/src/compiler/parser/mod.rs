//! Parser for choreographic protocol syntax.
//!
//! This module re-exports the shared parser from `telltale-parser` and adds
//! choreography-crate-specific tests.

// Re-export the complete public API from the shared parser crate.
pub use telltale_parser::compiler::parser::*;

#[cfg(test)]
mod tests {
    use super::*;
    use proc_macro2::TokenStream;
    use tempfile::tempdir;

    mod core_syntax_loops {
        include!("../../../tests/unit/compiler/parser/core_syntax_loops.rs");
    }

    mod annotations_and_parallel {
        include!("../../../tests/unit/compiler/parser/annotations_and_parallel.rs");
    }

    mod proof_bundles_predicates {
        include!("../../../tests/unit/compiler/parser/proof_bundles_predicates.rs");
    }

    mod authority_surface {
        include!("../../../tests/unit/compiler/parser/authority_surface.rs");
    }

    #[test]
    fn parse_choreography_file_accepts_tell_extension() {
        let dir = tempdir().expect("tempdir");
        let path = dir.path().join("protocol.tell");
        std::fs::write(&path, "protocol Ping =\n  roles A, B\n  A -> B : Msg\n")
            .expect("write tell fixture");

        let parsed = parse_choreography_file(&path).expect("parse .tell source");
        assert_eq!(parsed.name.to_string(), "Ping");
    }

    #[test]
    fn parse_choreography_file_rejects_choreo_extension() {
        let dir = tempdir().expect("tempdir");
        let path = dir.path().join("protocol.choreo");
        std::fs::write(&path, "protocol Ping =\n  roles A, B\n  A -> B : Msg\n")
            .expect("write choreo fixture");

        let err = parse_choreography_file(&path).expect_err("reject legacy extension");
        let rendered = err.to_string();
        assert!(
            rendered.contains(".tell"),
            "error should point to canonical .tell extension: {rendered}"
        );
    }
}
