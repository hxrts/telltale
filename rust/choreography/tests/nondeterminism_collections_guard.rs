//! Guardrail: deterministic runtime-facing choreography modules should avoid
//! hash-randomized collections in their core state.

const FORBIDDEN_PATTERNS: &[&str] = &[
    "HashMap<",
    "HashSet<",
    "collections::HashMap",
    "collections::HashSet",
];

const GUARDED_SOURCES: &[(&str, &str)] = &[
    (
        "src/runtime/adapter.rs",
        include_str!("../src/runtime/adapter.rs"),
    ),
    (
        "src/runtime/test_adapter.rs",
        include_str!("../src/runtime/test_adapter.rs"),
    ),
    (
        "src/effects/handlers/in_memory.rs",
        include_str!("../src/effects/handlers/in_memory.rs"),
    ),
    (
        "src/topology/handler.rs",
        include_str!("../src/topology/handler.rs"),
    ),
    (
        "src/topology/transport.rs",
        include_str!("../src/topology/transport.rs"),
    ),
    (
        "src/topology/resolver.rs",
        include_str!("../src/topology/resolver.rs"),
    ),
    (
        "src/testing/harness.rs",
        include_str!("../src/testing/harness.rs"),
    ),
    (
        "src/extensions/discovery.rs",
        include_str!("../src/extensions/discovery.rs"),
    ),
    (
        "src/testing/transport.rs",
        include_str!("../src/testing/transport.rs"),
    ),
    (
        "src/testing/state_machine.rs",
        include_str!("../src/testing/state_machine.rs"),
    ),
    (
        "src/testing/observer.rs",
        include_str!("../src/testing/observer.rs"),
    ),
];

#[test]
fn runtime_collections_are_deterministic() {
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
        "deterministic choreography runtime guard failed:\n{}",
        violations.join("\n")
    );
}
