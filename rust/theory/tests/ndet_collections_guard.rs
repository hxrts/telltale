//! Guardrail: core theory stepping/projection modules should not depend on
//! hash-randomized collections for runtime semantics.

const FORBIDDEN_PATTERNS: &[&str] = &[
    "HashMap<",
    "HashSet<",
    "collections::HashMap",
    "collections::HashSet",
];

const GUARDED_SOURCES: &[(&str, &str)] = &[
    (
        "src/subtyping/sync.rs",
        include_str!("../src/subtyping/sync.rs"),
    ),
    ("src/semantics.rs", include_str!("../src/semantics.rs")),
    ("src/coherence.rs", include_str!("../src/coherence.rs")),
    ("src/projection.rs", include_str!("../src/projection.rs")),
];

#[test]
fn theory_runtime_collections_are_deterministic() {
    let mut violations = Vec::new();

    for (path, source) in GUARDED_SOURCES {
        for pattern in FORBIDDEN_PATTERNS {
            if source.contains(pattern) {
                violations.push(format!("{path}: found forbidden pattern `{pattern}`"));
            }
        }
    }

    assert!(
        violations.is_empty(),
        "deterministic theory guard failed:\n{}",
        violations.join("\n")
    );
}
