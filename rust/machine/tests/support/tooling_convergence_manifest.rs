//! Declarative policy manifest for tooling convergence guardrails.

pub(crate) struct PatternExpectation {
    pub(crate) path: &'static str,
    pub(crate) pattern: &'static str,
}

pub(crate) const REQUIRED_PATTERNS: &[PatternExpectation] = &[
    PatternExpectation {
        path: "../../../Justfile",
        pattern:
            "cargo run -p telltale-choreography --bin effect-scaffold -- --out {{ out }} --dsl {{ dsl }}",
    },
    PatternExpectation {
        path: "../../../Justfile",
        pattern: "./scripts/check/tooling-convergence.sh",
    },
    PatternExpectation {
        path: "../../../docs/02_getting_started.md",
        pattern: "use telltale::tell;",
    },
    PatternExpectation {
        path: "../../../docs/02_getting_started.md",
        pattern: "PingPong::proof_status",
    },
    PatternExpectation {
        path: "../../../docs/03_architecture.md",
        pattern: "protocol-machine and generated effect boundary",
    },
    PatternExpectation {
        path: "../../../docs/04_code_organization.md",
        pattern: "generated surfaces & tooling",
    },
    PatternExpectation {
        path: "../../../docs/06_choreographic_dsl.md",
        pattern: "Protocol::proof_status",
    },
    PatternExpectation {
        path: "../../../docs/08_extensions.md",
        pattern: "not the primary public",
    },
    PatternExpectation {
        path: "../../../docs/09_effect_handlers.md",
        pattern: "Protocol::effects::*",
    },
    PatternExpectation {
        path: "../../../docs/11_effect_session_bridge.md",
        pattern: "interfaces emitted directly by `tell!`",
    },
    PatternExpectation {
        path: "../../../docs/15_protocol_machine_simulation_overview.md",
        pattern: "GeneratedEffectScenario::builder()",
    },
    PatternExpectation {
        path: "../../../docs/16_protocol_machine_simulation_runner.md",
        pattern: "ProtocolMachineSemanticObjects",
    },
    PatternExpectation {
        path: "../../../docs/17_protocol_machine_simulation_scenarios.md",
        pattern: "record_stale_late_result",
    },
    PatternExpectation {
        path: "../../../docs/22_topology.md",
        pattern: "`tell!` emits a topology helper module",
    },
    PatternExpectation {
        path: "../../../docs/28_examples.md",
        pattern: "Protocol::proof_status",
    },
    PatternExpectation {
        path: "../../../docs/29_wasm_guide.md",
        pattern: "Protocol definitions written with `tell!`",
    },
    PatternExpectation {
        path: "../../choreography/examples/authority_surface.rs",
        pattern: "generated_effect_families(&choreography)",
    },
    PatternExpectation {
        path: "../examples/v2_baseline_capture.rs",
        pattern: "ThreadedGuestRuntime::with_workers",
    },
    PatternExpectation {
        path: "../benches/protocol_machine_bench_common.rs",
        pattern: "load_choreography_owned",
    },
    PatternExpectation {
        path: "../benches/protocol_machine_bench_common.rs",
        pattern: "fn handle_effect(&self, request: EffectRequest) -> EffectOutcome",
    },
    PatternExpectation {
        path: "../benches/protocol_machine_bench_runtime.rs",
        pattern: "protocol_machine_run_yield_small",
    },
];

pub(crate) const FORBIDDEN_PATTERNS: &[PatternExpectation] = &[
    PatternExpectation {
        path: "../../../Justfile",
        pattern: "effect-scaffold out=",
    },
    PatternExpectation {
        path: "../../../Justfile",
        pattern: "-- {{ out }} {{ name }}",
    },
    PatternExpectation {
        path: "../examples/v2_baseline_capture.rs",
        pattern: "ThreadedProtocolMachine",
    },
    PatternExpectation {
        path: "../benches/protocol_machine_bench_common.rs",
        pattern: "load_choreography(",
    },
    PatternExpectation {
        path: "../benches/protocol_machine_bench_runtime.rs",
        pattern: "load_choreography(",
    },
    PatternExpectation {
        path: "../../../docs/02_getting_started.md",
        pattern: "Program::new()",
    },
    PatternExpectation {
        path: "../../../docs/03_architecture.md",
        pattern: "Program::new()",
    },
    PatternExpectation {
        path: "../../../docs/08_extensions.md",
        pattern: "Program::new()",
    },
    PatternExpectation {
        path: "../../../docs/09_effect_handlers.md",
        pattern: "Program::new()",
    },
    PatternExpectation {
        path: "../../../docs/28_examples.md",
        pattern: "Program::new()",
    },
    PatternExpectation {
        path: "../../../docs/29_wasm_guide.md",
        pattern: "Program::new()",
    },
    PatternExpectation {
        path: "../../../docs/02_getting_started.md",
        pattern: "choreography!(",
    },
    PatternExpectation {
        path: "../../../docs/06_choreographic_dsl.md",
        pattern: "choreography!(",
    },
    PatternExpectation {
        path: "../../../docs/22_topology.md",
        pattern: "`choreography!`",
    },
    PatternExpectation {
        path: "../../../docs/28_examples.md",
        pattern: "`choreography!`",
    },
    PatternExpectation {
        path: "../../../docs/29_wasm_guide.md",
        pattern: "`choreography!`",
    },
];
