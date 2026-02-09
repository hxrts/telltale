//! Lean Verification Bridge for Telltale Session Types
//!
//! This crate provides bidirectional conversion between Rust session types
//! and Lean-compatible JSON format, enabling formal verification of
//! protocol properties in Lean.
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

pub mod export;
pub mod import;
pub mod invariants;
pub mod schema;
pub mod vm_export;
pub mod vm_trace;

#[cfg(feature = "runner")]
pub mod equivalence;

#[cfg(feature = "runner")]
pub mod runner;

#[cfg(feature = "runner")]
pub mod validate;

#[cfg(feature = "runner")]
pub mod vm_runner;

#[cfg(test)]
pub mod test_utils;

pub use export::{global_to_json, local_to_json};
pub use import::{json_to_global, json_to_local, ImportError};
pub use invariants::{
    export_protocol_bundle, AvailabilityLevel, CAPConfig, ClassicalClaims, ConcentrationConfig,
    ConsistencyLevel, DistributedClaims, FLPConfig, FaultModel, FluidConfig, FosterConfig,
    FunctionalCLTConfig, HeavyTrafficConfig, InvariantClaims, LDPConfig, LittlesLawConfig,
    LivenessConfig, MaxWeightConfig, MeanFieldConfig, MixingConfig, NakamotoConfig,
    PartialSynchronyConfig, PartitionModel, ProtocolBundle, QuorumGeometryConfig, QuorumSystemKind,
    ReconfigurationConfig, ResponsivenessConfig, SchedulerKind, TimingModel,
    PROTOCOL_BUNDLE_SCHEMA_VERSION,
};
pub use schema::{
    default_schema_version, ensure_supported_schema_version, is_supported_schema_version,
    LEAN_BRIDGE_SCHEMA_VERSION,
};
pub use vm_export::{
    coroutine_to_json, endpoint_to_json, event_to_json, obs_event_to_json, sessions_to_json,
    status_to_json, vm_state_from_json, vm_state_to_json, CompatibilityMeta, CoroutineState,
    EndpointRef, SessionView, TickedObsEvent, VMState, VM_STATE_SCHEMA_VERSION,
};
pub use vm_trace::{
    event_session, normalize_vm_trace, partition_by_session, traces_equivalent, EffectTraceEvent,
    NormalizedEvent, OutputConditionTraceEvent, ReplayTraceBundle, SessionTrace,
    TopologyPerturbationEvent, TopologyPerturbationKind,
};

#[cfg(feature = "runner")]
pub use equivalence::{
    CoherenceBundle, EquivalenceChecker, EquivalenceConfig, EquivalenceError, EquivalenceResult,
    GoldenBundle,
};

#[cfg(feature = "runner")]
pub use runner::{ChoreographyJson, LeanRunner, LeanRunnerError, LeanValidationResult};

#[cfg(feature = "runner")]
pub use vm_runner::{
    compute_trace_diff, ComparisonResult, InvariantVerificationResult, LeanStructuredError,
    TraceValidation, VmRunInput, VmRunOutput, VmRunner, VmRunnerError, VmSessionStatus,
    VmStepState, VmTraceEvent,
};

#[cfg(feature = "runner")]
pub use validate::{ValidationResult, Validator};
