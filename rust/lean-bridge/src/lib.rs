//! Lean verification bridge for Telltale protocol-machine artifacts.
//!
//! This crate provides bidirectional conversion between Rust protocol/session
//! artifacts and Lean-compatible JSON format, enabling formal verification of
//! protocol-machine properties in Lean.
//!
//! # Features
//!
//! - `runner` (default) - Enable LeanRunner for invoking the Lean binary
//! - `cli` - Enable command-line interface binary
//!
//! # Overview
//!
//! The bridge supports:
//!
//! - **Export**: Convert Rust types to Lean-compatible JSON
//! - **Import**: Parse Lean JSON output into Rust types
//! - **Validation**: Cross-validate Rust implementations against Lean proofs (requires `runner` feature)
//!
//! # JSON Format
//!
//! The JSON format matches the Lean type definitions:
//!
//! ```json
//! {
//!   "kind": "comm",
//!   "sender": "Client",
//!   "receiver": "Server",
//!   "branches": [
//!     {
//!       "label": { "name": "request", "sort": "unit" },
//!       "continuation": { "kind": "end" }
//!     }
//!   ]
//! }
//! ```
//!
//! # Example
//!
//! ```
//! use telltale_types::{GlobalType, Label};
//! use telltale_lean_bridge::export::global_to_json;
//!
//! let g = GlobalType::comm(
//!     "Client",
//!     "Server",
//!     vec![(Label::new("hello"), GlobalType::End)],
//! );
//!
//! let json = global_to_json(&g);
//! assert_eq!(json["kind"], "comm");
//! ```

#![allow(
    clippy::missing_errors_doc,
    clippy::missing_panics_doc,
    clippy::must_use_candidate
)]

use cfg_if::cfg_if;

pub mod export;
pub mod import;
pub mod invariants;
pub mod schema;
pub mod semantic_objects;
pub mod vm_trace;

cfg_if! {
    if #[cfg(feature = "runner")] {
        pub(crate) mod projection_payload;
        pub mod equivalence;
        pub mod runner;
        pub mod sim_reference;
        pub mod validate;
        pub mod vm_runner;
    }
}

#[cfg(test)]
pub mod test_utils;

pub use export::{global_to_json, local_to_json};
pub use import::{json_to_global, json_to_local, ImportError};
pub use invariants::{
    export_protocol_bundle, AccountableSafetyConfig, AvailabilityLevel, ByzantineSafetyConfig,
    CAPConfig, CRDTConfig, ClassicalClaims, ConcentrationConfig, ConsensusEnvelopeConfig,
    ConsistencyLevel, CoordinationConfig, DataAvailabilityConfig, DistributedClaims, FLPConfig,
    FailureDetectorsConfig, FailureEnvelopeConfig, FaultModel, FluidConfig, FosterConfig,
    FunctionalCLTConfig, HeavyTrafficConfig, InvariantClaims, LDPConfig, LittlesLawConfig,
    LivenessConfig, MaxWeightConfig, MeanFieldConfig, MixingConfig, NakamotoConfig,
    PartialSynchronyConfig, PartitionModel, ProtocolBundle, ProtocolEnvelopeBridgeConfig,
    QuorumGeometryConfig, QuorumSystemKind, ReconfigurationConfig, ResponsivenessConfig,
    SchedulerKind, TimingModel, VMEnvelopeAdherenceConfig, VMEnvelopeAdmissionConfig,
    PROTOCOL_BUNDLE_SCHEMA_VERSION,
};
pub use schema::{
    default_schema_version, ensure_supported_schema_version, is_supported_schema_version,
    LEAN_BRIDGE_SCHEMA_VERSION,
};
pub use semantic_objects::{
    default_semantic_objects_schema_version, semantic_objects_from_json, semantic_objects_to_json,
    AuthoritativeRead, AuthoritativeReadKind, AuthoritativeReadLifecycle, CanonicalHandle,
    CanonicalHandleKind, DelegationStatus, MaterializationProof, ObservedRead, OperationInstance,
    OperationPhase, OutstandingEffect, OutstandingEffectStatus, OwnershipScope, ProgressContract,
    ProgressState, ProtocolMachineSemanticObjects, SemanticHandoff, TickedObsEvent,
    SEMANTIC_OBJECTS_SCHEMA_VERSION,
};
pub use vm_trace::{
    event_session, normalize_vm_trace, observationally_equivalent, partition_by_session,
    traces_equivalent, EffectTraceEvent, NormalizedEvent, OutputConditionTraceEvent,
    ReplayTraceBundle, SessionTrace, TopologyPerturbationEvent, TopologyPerturbationKind,
};

cfg_if! {
    if #[cfg(feature = "runner")] {
        pub use equivalence::{
            CoherenceBundle, EquivalenceChecker, EquivalenceConfig, EquivalenceError,
            EquivalenceResult, GoldenBundle,
        };
        pub use runner::{ChoreographyJson, LeanRunner, LeanRunnerError, LeanValidationResult};
        pub use sim_reference::{
            SimRunInput, SimRunOutput, SimTraceValidation, SimulationStructuredError,
        };
        pub use vm_runner::{
            compute_trace_diff, ComparisonResult, InvariantVerificationResult, LeanStructuredError,
            ProtocolMachineRunInput, ProtocolMachineRunOutput, ProtocolMachineRunner,
            ProtocolMachineRunnerError, ProtocolMachineSessionStatus,
            ProtocolMachineStepState, ProtocolMachineTraceEvent, TraceValidation,
        };
        pub use validate::{ValidationResult, Validator};
    }
}
