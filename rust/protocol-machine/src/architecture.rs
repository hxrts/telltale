//! Runtime architecture contract.
//!
//! This module defines the canonical semantic engine and the role of each
//! runtime surface.

/// Runtime engine role classification during migration.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EngineRole {
    /// Canonical semantic owner.
    Canonical,
    /// Adapter/runtime surface that must not redefine semantics.
    AdapterOnly,
}

/// Semantic ownership contract for runtime execution surfaces.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EngineOwnership {
    /// Runtime surface name.
    pub engine: &'static str,
    /// Canonical/adaptor role.
    pub role: EngineRole,
    /// Who owns instruction semantics.
    pub instruction_semantics_owner: &'static str,
    /// Who owns scheduler policy interpretation.
    pub scheduler_policy_owner: &'static str,
    /// Who owns observable trace emission semantics.
    pub trace_semantics_owner: &'static str,
}

/// Canonical semantic owner for ProtocolMachine execution.
pub const CANONICAL_ENGINE: &str = "ProtocolMachineKernel";

/// Cross-target semantic contract.
///
/// Native single-threaded, native threaded, and wasm cooperative runtimes
/// must agree on canonical ProtocolMachine observables, modulo effect-policy differences.
pub const CROSS_TARGET_CONTRACT: &str =
    "NativeThreaded ~= NativeSingleThreaded ~= WasmCooperative (modulo effects)";

/// Equivalence surfaces checked by cross-target validation.
pub const EQUIVALENCE_SURFACES: &[&str] = &[
    "normalized_vm_observable_trace",
    "normalized_scheduler_step_trace",
    "effect_trace",
];

/// Declared runtime ownership for all ProtocolMachine execution surfaces.
pub const ENGINE_OWNERSHIP: &[EngineOwnership] = &[
    EngineOwnership {
        engine: "ProtocolMachineKernel",
        role: EngineRole::Canonical,
        instruction_semantics_owner: "ProtocolMachineKernel + exec::*",
        scheduler_policy_owner: "ProtocolMachineKernel + scheduler::Scheduler",
        trace_semantics_owner: "ProtocolMachineKernel commit path",
    },
    EngineOwnership {
        engine: "ProtocolMachine",
        role: EngineRole::AdapterOnly,
        instruction_semantics_owner: "ProtocolMachineKernel + exec::*",
        scheduler_policy_owner: "ProtocolMachineKernel + scheduler::Scheduler",
        trace_semantics_owner: "ProtocolMachineKernel commit path",
    },
    EngineOwnership {
        engine: "ThreadedProtocolMachine",
        role: EngineRole::AdapterOnly,
        instruction_semantics_owner: "ProtocolMachineKernel + exec::*",
        scheduler_policy_owner: "ProtocolMachineKernel + scheduler::Scheduler",
        trace_semantics_owner: "ProtocolMachineKernel commit path",
    },
    EngineOwnership {
        engine: "WasmCooperativeDriver",
        role: EngineRole::AdapterOnly,
        instruction_semantics_owner: "ProtocolMachineKernel + exec::*",
        scheduler_policy_owner: "ProtocolMachineKernel + scheduler::Scheduler",
        trace_semantics_owner: "ProtocolMachineKernel commit path",
    },
];

#[cfg(test)]
mod tests {
    use super::{
        EngineRole, CANONICAL_ENGINE, CROSS_TARGET_CONTRACT, ENGINE_OWNERSHIP, EQUIVALENCE_SURFACES,
    };

    #[test]
    fn canonical_engine_is_declared_once() {
        let canon = ENGINE_OWNERSHIP
            .iter()
            .filter(|o| o.role == EngineRole::Canonical)
            .collect::<Vec<_>>();
        assert_eq!(canon.len(), 1);
        assert_eq!(canon[0].engine, CANONICAL_ENGINE);
    }

    #[test]
    fn cross_target_contract_declares_required_surfaces() {
        assert!(CROSS_TARGET_CONTRACT.contains("modulo effects"));
        assert_eq!(EQUIVALENCE_SURFACES.len(), 3);
        assert!(EQUIVALENCE_SURFACES.contains(&"normalized_vm_observable_trace"));
        assert!(EQUIVALENCE_SURFACES.contains(&"normalized_scheduler_step_trace"));
        assert!(EQUIVALENCE_SURFACES.contains(&"effect_trace"));
    }
}
