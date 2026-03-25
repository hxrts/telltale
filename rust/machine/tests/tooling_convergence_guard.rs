//! Guardrail: examples, benches, and tooling must use the canonical public surfaces.

use wasm_bindgen_test::wasm_bindgen_test;

#[path = "support/tooling_convergence_manifest.rs"]
mod tooling_convergence_manifest;

use tooling_convergence_manifest::{FORBIDDEN_PATTERNS, REQUIRED_PATTERNS};

const TOOLING_SOURCES: &[(&str, &str)] = &[
    ("../../../Justfile", include_str!("../../../Justfile")),
    (
        "../../../docs/02_getting_started.md",
        include_str!("../../../docs/02_getting_started.md"),
    ),
    (
        "../../../docs/03_architecture.md",
        include_str!("../../../docs/03_architecture.md"),
    ),
    (
        "../../../docs/04_code_organization.md",
        include_str!("../../../docs/04_code_organization.md"),
    ),
    (
        "../../../docs/06_choreographic_dsl.md",
        include_str!("../../../docs/06_choreographic_dsl.md"),
    ),
    (
        "../../../docs/08_extensions.md",
        include_str!("../../../docs/08_extensions.md"),
    ),
    (
        "../../../docs/09_effect_handlers.md",
        include_str!("../../../docs/09_effect_handlers.md"),
    ),
    (
        "../../../docs/11_effect_session_bridge.md",
        include_str!("../../../docs/11_effect_session_bridge.md"),
    ),
    (
        "../../../docs/15_protocol_machine_simulation_overview.md",
        include_str!("../../../docs/15_protocol_machine_simulation_overview.md"),
    ),
    (
        "../../../docs/16_protocol_machine_simulation_runner.md",
        include_str!("../../../docs/16_protocol_machine_simulation_runner.md"),
    ),
    (
        "../../../docs/17_protocol_machine_simulation_scenarios.md",
        include_str!("../../../docs/17_protocol_machine_simulation_scenarios.md"),
    ),
    (
        "../../../docs/22_topology.md",
        include_str!("../../../docs/22_topology.md"),
    ),
    (
        "../../../docs/28_examples.md",
        include_str!("../../../docs/28_examples.md"),
    ),
    (
        "../../../docs/29_wasm_guide.md",
        include_str!("../../../docs/29_wasm_guide.md"),
    ),
    (
        "../../choreography/examples/authority_surface.rs",
        include_str!("../../choreography/examples/authority_surface.rs"),
    ),
    (
        "../examples/v2_baseline_capture.rs",
        include_str!("../examples/v2_baseline_capture.rs"),
    ),
    (
        "../benches/protocol_machine_bench_common.rs",
        include_str!("../benches/protocol_machine_bench_common.rs"),
    ),
    (
        "../benches/protocol_machine_bench_runtime.rs",
        include_str!("../benches/protocol_machine_bench_runtime.rs"),
    ),
];

#[wasm_bindgen_test(unsupported = test)]
fn tooling_surfaces_use_generated_effect_and_owned_open_paths() {
    let violations = collect_tooling_convergence_violations();

    assert!(
        violations.is_empty(),
        "tooling/example surfaces drifted away from the canonical protocol-machine + generated-effect model:\n{}",
        violations.join("\n")
    );
}

fn collect_tooling_convergence_violations() -> Vec<String> {
    let mut violations = Vec::new();

    for (path, src) in TOOLING_SOURCES {
        collect_missing_required_patterns(&mut violations, path, src);
        collect_present_forbidden_patterns(&mut violations, path, src);
    }

    violations
}

fn collect_missing_required_patterns(violations: &mut Vec<String>, path: &str, src: &str) {
    for expectation in REQUIRED_PATTERNS {
        if path == expectation.path && !src.contains(expectation.pattern) {
            violations.push(format!(
                "{path}: missing required pattern `{}`",
                expectation.pattern
            ));
        }
    }
}

fn collect_present_forbidden_patterns(violations: &mut Vec<String>, path: &str, src: &str) {
    for expectation in FORBIDDEN_PATTERNS {
        if path == expectation.path && src.contains(expectation.pattern) {
            violations.push(format!(
                "{path}: found forbidden pattern `{}`",
                expectation.pattern
            ));
        }
    }
}
