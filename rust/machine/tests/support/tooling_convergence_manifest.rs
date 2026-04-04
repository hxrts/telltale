//! Declarative policy manifest for tooling convergence guardrails.

pub(crate) struct PatternExpectation {
    pub(crate) path: &'static str,
    pub(crate) pattern: &'static str,
}

pub(crate) const REQUIRED_PATTERNS: &[PatternExpectation] = &[
    PatternExpectation {
        path: "../../../justfile",
        pattern:
            "cargo run -p telltale-runtime --bin effect-scaffold -- --out {{ out }} --dsl {{ dsl }}",
    },
    PatternExpectation {
        path: "../../../justfile",
        pattern: "./scripts/check/tooling-convergence.sh",
    },
    PatternExpectation {
        path: "../../../docs/201_getting_started.md",
        pattern: "use telltale::tell;",
    },
    PatternExpectation {
        path: "../../../docs/201_getting_started.md",
        pattern: "PingPong::proof_status",
    },
    PatternExpectation {
        path: "../../../docs/104_architecture.md",
        pattern: "protocol-machine and generated effect boundary",
    },
    PatternExpectation {
        path: "../../../docs/105_code_organization.md",
        pattern: "generated surfaces & tooling",
    },
    PatternExpectation {
        path: "../../../docs/202_choreographic_dsl.md",
        pattern: "Protocol::proof_status",
    },
    PatternExpectation {
        path: "../../../docs/204_extensions.md",
        pattern: "not the primary public",
    },
    PatternExpectation {
        path: "../../../docs/301_effect_handlers.md",
        pattern: "Protocol::effects::*",
    },
    PatternExpectation {
        path: "../../../docs/303_effect_session_bridge.md",
        pattern: "interfaces emitted directly by `tell!`",
    },
    PatternExpectation {
        path: "../../../docs/501_simulation_overview.md",
        pattern: "GeneratedEffectScenario::builder()",
    },
    PatternExpectation {
        path: "../../../docs/502_simulation_runner.md",
        pattern: "ProtocolMachineSemanticObjects",
    },
    PatternExpectation {
        path: "../../../docs/503_simulation_scenarios.md",
        pattern: "record_stale_late_result",
    },
    PatternExpectation {
        path: "../../../docs/603_topology.md",
        pattern: "`tell!` emits a topology helper module",
    },
    PatternExpectation {
        path: "../../../docs/205_examples.md",
        pattern: "Protocol::proof_status",
    },
    PatternExpectation {
        path: "../../../docs/206_wasm_guide.md",
        pattern: "Protocol definitions written with `tell!`",
    },
    PatternExpectation {
        path: "../../runtime/examples/authority_surface.rs",
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
        path: "../../../justfile",
        pattern: "effect-scaffold out=",
    },
    PatternExpectation {
        path: "../../../justfile",
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
        path: "../../../docs/201_getting_started.md",
        pattern: "Program::new()",
    },
    PatternExpectation {
        path: "../../../docs/104_architecture.md",
        pattern: "Program::new()",
    },
    PatternExpectation {
        path: "../../../docs/204_extensions.md",
        pattern: "Program::new()",
    },
    PatternExpectation {
        path: "../../../docs/301_effect_handlers.md",
        pattern: "Program::new()",
    },
    PatternExpectation {
        path: "../../../docs/205_examples.md",
        pattern: "Program::new()",
    },
    PatternExpectation {
        path: "../../../docs/206_wasm_guide.md",
        pattern: "Program::new()",
    },
    PatternExpectation {
        path: "../../../docs/201_getting_started.md",
        pattern: "choreography!(",
    },
    PatternExpectation {
        path: "../../../docs/202_choreographic_dsl.md",
        pattern: "choreography!(",
    },
    PatternExpectation {
        path: "../../../docs/603_topology.md",
        pattern: "`choreography!`",
    },
    PatternExpectation {
        path: "../../../docs/205_examples.md",
        pattern: "`choreography!`",
    },
    PatternExpectation {
        path: "../../../docs/206_wasm_guide.md",
        pattern: "`choreography!`",
    },
];
