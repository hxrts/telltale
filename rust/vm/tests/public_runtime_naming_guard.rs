//! Guardrail: public-facing runtime docs should teach protocol-machine terms.

use wasm_bindgen_test::wasm_bindgen_test;

const PUBLIC_RUNTIME_SOURCES: &[(&str, &str)] = &[
    ("../src/lib.rs", include_str!("../src/lib.rs")),
    (
        "../../../docs/03_architecture.md",
        include_str!("../../../docs/03_architecture.md"),
    ),
    (
        "../../../docs/04_code_organization.md",
        include_str!("../../../docs/04_code_organization.md"),
    ),
    (
        "../../../docs/12_vm_architecture.md",
        include_str!("../../../docs/12_vm_architecture.md"),
    ),
    (
        "../../../docs/14_session_lifecycle.md",
        include_str!("../../../docs/14_session_lifecycle.md"),
    ),
    (
        "../../../docs/19_rust_lean_parity.md",
        include_str!("../../../docs/19_rust_lean_parity.md"),
    ),
    (
        "../../../docs/24_lean_rust_bridge.md",
        include_str!("../../../docs/24_lean_rust_bridge.md"),
    ),
    (
        "../../../docs/30_api_reference.md",
        include_str!("../../../docs/30_api_reference.md"),
    ),
    (
        "../../effect-scaffold/templates/effect_handler_test.rs.tmpl",
        include_str!("../../effect-scaffold/templates/effect_handler_test.rs.tmpl"),
    ),
    (
        "../../lean-bridge/src/lib.rs",
        include_str!("../../lean-bridge/src/lib.rs"),
    ),
];

#[wasm_bindgen_test(unsupported = test)]
fn crate_root_exports_protocol_machine_runtime_terms() {
    let lib_src = include_str!("../src/lib.rs");

    let required_patterns = [
        "VM as ProtocolMachine",
        "VMConfig as ProtocolMachineConfig",
        "NativeSingleThreadDriver as GuestRuntime",
        "EffectHandler as ExternalHandler",
        "pub mod protocol_machine {",
        "pub mod guest_runtime {",
        "pub mod host_runtime {",
    ];
    let forbidden_patterns = [
        "VmRetainedBytes, VM, VMConfig, VMState",
        "LaneSelection, ThreadedVM,",
        "pub use driver::NativeSingleThreadDriver;",
        "pub use driver::NativeThreadedDriver;",
    ];

    let mut missing = Vec::new();
    for pattern in required_patterns {
        if !lib_src.contains(pattern) {
            missing.push(pattern);
        }
    }
    for pattern in forbidden_patterns {
        if lib_src.contains(pattern) {
            missing.push(pattern);
        }
    }

    assert!(
        missing.is_empty(),
        "crate root is missing canonical runtime aliases or still exposes legacy root naming:\n{}",
        missing.join("\n")
    );
}

#[wasm_bindgen_test(unsupported = test)]
fn canonical_public_examples_use_protocol_machine_terms() {
    let required_patterns = [
        ("../../../docs/04_code_organization.md", "ProtocolMachine"),
        ("../../../docs/04_code_organization.md", "GuestRuntime"),
        ("../../../docs/30_api_reference.md", "ProtocolMachine"),
        ("../../../docs/30_api_reference.md", "GuestRuntime"),
        ("../../../docs/14_session_lifecycle.md", "ProtocolMachineConfig"),
        ("../../../docs/19_rust_lean_parity.md", "ProtocolMachine"),
        (
            "../../effect-scaffold/templates/effect_handler_test.rs.tmpl",
            "ProtocolMachine::new",
        ),
        ("../../../docs/24_lean_rust_bridge.md", "ProtocolMachineRunner"),
        ("../../../docs/24_lean_rust_bridge.md", "ProtocolMachineSemanticObjects"),
        ("../../lean-bridge/src/lib.rs", "ProtocolMachineRunner"),
        ("../../lean-bridge/src/lib.rs", "ProtocolMachineSemanticObjects"),
    ];
    let forbidden_patterns = [
        ("../../../docs/04_code_organization.md", "use telltale_vm::{OwnedSession, VM, VMConfig};"),
        ("../../../docs/04_code_organization.md", "let mut vm = VM::new"),
        ("../../../docs/24_lean_rust_bridge.md", "The bridge does not define VM semantics."),
        ("../../../docs/24_lean_rust_bridge.md", "## Lean VM Runner Wrapper"),
        (
            "../../effect-scaffold/templates/effect_handler_test.rs.tmpl",
            "use telltale_vm::vm::{EffectTraceCaptureMode, VMConfig, VM};",
        ),
        (
            "../../effect-scaffold/templates/effect_handler_test.rs.tmpl",
            "let mut vm = VM::new",
        ),
    ];

    let mut violations = Vec::new();

    for (path, src) in PUBLIC_RUNTIME_SOURCES {
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
        "canonical public runtime sources drifted away from protocol-machine terms:\n{}",
        violations.join("\n")
    );
}
