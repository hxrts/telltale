//! Guardrail: examples, benches, and tooling must use the canonical public surfaces.

use wasm_bindgen_test::wasm_bindgen_test;

const TOOLING_SOURCES: &[(&str, &str)] = &[
    ("../../../Justfile", include_str!("../../../Justfile")),
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
    let required_patterns = [
        (
            "../../../Justfile",
            "cargo run -p effect-scaffold -- --out {{ out }} --dsl {{ dsl }}",
        ),
        (
            "../../../Justfile",
            "./scripts/check/tooling-convergence.sh",
        ),
        (
            "../../../docs/15_protocol_machine_simulation_overview.md",
            "GeneratedEffectScenario::builder()",
        ),
        (
            "../../../docs/16_protocol_machine_simulation_runner.md",
            "ProtocolMachineSemanticObjects",
        ),
        (
            "../../../docs/17_protocol_machine_simulation_scenarios.md",
            "record_stale_late_result",
        ),
        (
            "../../choreography/examples/authority_surface.rs",
            "generated_effect_families()",
        ),
        (
            "../examples/v2_baseline_capture.rs",
            "ThreadedGuestRuntime::with_workers",
        ),
        ("../benches/protocol_machine_bench_common.rs", "load_choreography_owned"),
        (
            "../benches/protocol_machine_bench_common.rs",
            "fn handle_effect(&self, request: EffectRequest) -> EffectOutcome",
        ),
        (
            "../benches/protocol_machine_bench_runtime.rs",
            "protocol_machine_run_yield_small",
        ),
    ];
    let forbidden_patterns = [
        ("../../../Justfile", "effect-scaffold out="),
        ("../../../Justfile", "-- {{ out }} {{ name }}"),
        (
            "../examples/v2_baseline_capture.rs",
            "ThreadedProtocolMachine",
        ),
        ("../benches/protocol_machine_bench_common.rs", "load_choreography("),
        ("../benches/protocol_machine_bench_runtime.rs", "\"vm_run_yield_small\""),
        ("../benches/protocol_machine_bench_runtime.rs", "load_choreography("),
    ];

    let mut violations = Vec::new();

    for (path, src) in TOOLING_SOURCES {
        for (required_path, pattern) in required_patterns {
            if path == &required_path && !src.contains(pattern) {
                violations.push(format!("{path}: missing required pattern `{pattern}`"));
            }
        }
        for (forbidden_path, pattern) in forbidden_patterns {
            if path == &forbidden_path && src.contains(pattern) {
                violations.push(format!("{path}: found forbidden pattern `{pattern}`"));
            }
        }
    }

    assert!(
        violations.is_empty(),
        "tooling/example surfaces drifted away from the canonical protocol-machine + generated-effect model:\n{}",
        violations.join("\n")
    );
}
