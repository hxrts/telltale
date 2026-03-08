//! Guardrail: core type-level protocol structures should avoid hash-randomized
//! collections in deterministic APIs.

const FORBIDDEN_PATTERNS: &[&str] = &[
    "HashMap<",
    "HashSet<",
    "collections::HashMap",
    "collections::HashSet",
];

const GUARDED_SOURCES: &[(&str, &str)] = &[
    ("src/global.rs", include_str!("../src/global.rs")),
    ("src/local.rs", include_str!("../src/local.rs")),
    ("src/merge.rs", include_str!("../src/merge.rs")),
    ("src/role.rs", include_str!("../src/role.rs")),
];

#[test]
fn type_collections_are_deterministic() {
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
        "deterministic types guard failed:\n{}",
        violations.join("\n")
    );
}
