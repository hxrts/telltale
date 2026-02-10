//! Guardrail: VM kernel modules must not call host nondeterministic APIs directly.
//!
//! Nondeterminism is required to flow through `EffectHandler` so cross-target
//! replay and determinism-mode checks remain meaningful.

use wasm_bindgen_test::wasm_bindgen_test;

const FORBIDDEN_PATTERNS: &[&str] = &[
    "SystemTime::now(",
    "Instant::now(",
    "UNIX_EPOCH",
    "rand::thread_rng(",
    "thread_rng(",
    "rand::random(",
    "getrandom(",
    "std::fs::",
    "std::net::",
    "std::env::var(",
    "std::process::Command",
];

const KERNEL_SOURCES: &[(&str, &str)] = &[
    ("src/kernel.rs", include_str!("../src/kernel.rs")),
    ("src/vm.rs", include_str!("../src/vm.rs")),
    ("src/threaded.rs", include_str!("../src/threaded.rs")),
    ("src/scheduler.rs", include_str!("../src/scheduler.rs")),
    ("src/session.rs", include_str!("../src/session.rs")),
    ("src/coroutine.rs", include_str!("../src/coroutine.rs")),
    ("src/exec/mod.rs", include_str!("../src/exec/mod.rs")),
    ("src/exec/comm.rs", include_str!("../src/exec/comm.rs")),
    (
        "src/exec/session.rs",
        include_str!("../src/exec/session.rs"),
    ),
    (
        "src/exec/guard_effect.rs",
        include_str!("../src/exec/guard_effect.rs"),
    ),
    (
        "src/exec/speculation.rs",
        include_str!("../src/exec/speculation.rs"),
    ),
    (
        "src/exec/ownership.rs",
        include_str!("../src/exec/ownership.rs"),
    ),
    (
        "src/exec/control.rs",
        include_str!("../src/exec/control.rs"),
    ),
    (
        "src/exec/helpers.rs",
        include_str!("../src/exec/helpers.rs"),
    ),
];

const FORBIDDEN_TOPOLOGY_MUTATORS: &[&str] = &[
    "fn crash(",
    "fn partition(",
    "fn heal(",
    "TopologyPerturbation::Crash",
    "TopologyPerturbation::Partition",
    "TopologyPerturbation::Heal",
];

// vm.rs is excluded from topology mutation check because it contains
// apply_topology_event which legitimately processes events received from
// the effect handler via ingest_topology_events. This is the correct
// ingress point for topology effects flowing through the handler.
const TOPOLOGY_CHECK_EXCLUDES: &[&str] = &["src/vm.rs"];

#[wasm_bindgen_test(unsupported = test)]
fn vm_kernel_has_no_direct_nondeterministic_calls() {
    let mut violations = Vec::new();
    for (path, src) in KERNEL_SOURCES {
        for pattern in FORBIDDEN_PATTERNS {
            if src.contains(pattern) {
                violations.push(format!("{path}: found forbidden pattern `{pattern}`"));
            }
        }
    }

    assert!(
        violations.is_empty(),
        "direct host nondeterminism detected in VM kernel:\n{}",
        violations.join("\n")
    );
}

#[wasm_bindgen_test(unsupported = test)]
fn vm_kernel_has_no_direct_topology_mutation_paths() {
    let mut violations = Vec::new();
    for (path, src) in KERNEL_SOURCES {
        // Skip files that are legitimate ingress points for topology events
        if TOPOLOGY_CHECK_EXCLUDES.contains(path) {
            continue;
        }
        for pattern in FORBIDDEN_TOPOLOGY_MUTATORS {
            if src.contains(pattern) {
                violations.push(format!(
                    "{path}: found forbidden topology mutation pattern `{pattern}`"
                ));
            }
        }
    }

    assert!(
        violations.is_empty(),
        "topology effects must ingress through effect event stream only:\n{}",
        violations.join("\n")
    );
}
