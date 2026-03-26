//! Guardrail: host-facing surfaces must keep the owned boundary canonical.

use wasm_bindgen_test::wasm_bindgen_test;

const DRIVER_SOURCES: &[(&str, &str)] = &[
    (
        "src/driver/single_thread.rs",
        include_str!("../src/driver/single_thread.rs"),
    ),
    (
        "src/driver/threaded.rs",
        include_str!("../src/driver/threaded.rs"),
    ),
];

const DOC_SOURCES: &[(&str, &str)] = &[
    (
        "../../../docs/04_code_organization.md",
        include_str!("../../../docs/04_code_organization.md"),
    ),
    (
        "../../../docs/11_effect_session_bridge.md",
        include_str!("../../../docs/11_effect_session_bridge.md"),
    ),
    (
        "../../../docs/14_session_lifecycle.md",
        include_str!("../../../docs/14_session_lifecycle.md"),
    ),
    (
        "../../../docs/30_api_reference.md",
        include_str!("../../../docs/30_api_reference.md"),
    ),
    (
        "../../runtime/src/bin/effect_scaffold.rs",
        include_str!("../../runtime/src/bin/effect_scaffold.rs"),
    ),
];

#[wasm_bindgen_test(unsupported = test)]
fn public_drivers_only_expose_owned_open_paths() {
    let mut violations = Vec::new();
    for (path, src) in DRIVER_SOURCES {
        if src.contains("pub fn load_choreography(") {
            violations.push(format!("{path}: exposes raw `load_choreography(...)`"));
        }
        if !src.contains("pub fn load_choreography_owned(") {
            violations.push(format!("{path}: missing `load_choreography_owned(...)`"));
        }
    }

    assert!(
        violations.is_empty(),
        "host drivers drifted away from owned open path:\n{}",
        violations.join("\n")
    );
}

#[wasm_bindgen_test(unsupported = test)]
fn owned_boundary_docs_do_not_recommend_raw_open_or_backend_abstractions() {
    let forbidden_patterns = [
        "load_choreography(&image)",
        "low-level open",
        "ProtocolMachineBackend",
    ];
    let mut violations = Vec::new();

    for (path, src) in DOC_SOURCES {
        for pattern in forbidden_patterns {
            if src.contains(pattern) {
                violations.push(format!("{path}: found forbidden pattern `{pattern}`"));
            }
        }
    }

    assert!(
        violations.is_empty(),
        "host-facing docs and scaffold sources drifted away from the canonical owned boundary:\n{}",
        violations.join("\n")
    );
}

#[wasm_bindgen_test(unsupported = test)]
fn internal_raw_open_surfaces_are_hidden_from_rustdoc() {
    let lib_src = include_str!("../src/lib.rs");
    let coop_src = include_str!("../src/engine/runtime_exec/core.rs");
    let threaded_src = include_str!("../src/threaded/runtime_and_scheduling.rs");
    let validation_src = include_str!("../src/engine/validation.rs");

    assert!(
        !lib_src.contains("pub use backend::ProtocolMachineBackend;"),
        "crate root must not re-export the removed backend abstraction"
    );
    assert!(
        coop_src.contains("#[doc(hidden)]\n    pub fn load_choreography("),
        "cooperative raw open primitive must stay hidden from rustdoc"
    );
    assert!(
        threaded_src.contains("#[doc(hidden)]\n    pub fn load_choreography("),
        "threaded raw open primitive must stay hidden from rustdoc"
    );
    assert!(
        validation_src.contains("#[doc(hidden)]\n    pub fn sessions_mut("),
        "mutable session-store escape hatch must stay hidden from rustdoc"
    );
}
