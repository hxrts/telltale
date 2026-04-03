//! Protocol-machine-backed simulation engine for Telltale choreographic protocols.
//!
//! Executes projected local types through the protocol machine with pluggable
//! effect handlers.

// Simulator uses explicit Result-based error propagation in runtime paths.
#![allow(clippy::missing_panics_doc)]
// Simulator uses u64/usize conversions for tick/index interop with the protocol machine.
#![allow(
    clippy::as_conversions,
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss
)]
// Property monitor has complex evaluation logic by design.
#![allow(clippy::cognitive_complexity, clippy::too_many_lines)]
// Internal simulator errors are self-documenting via Result types.
#![allow(clippy::missing_errors_doc)]

pub mod analysis;
#[doc(hidden)]
pub mod backend;
pub mod checkpoint;
pub mod contracts;
pub mod decision;
pub mod distributed;
#[doc(hidden)]
pub mod execution;
pub mod fault;
/// Generated effect-family simulator helpers and scenario surfaces.
pub mod generated;
pub mod harness;
pub mod material;
pub mod material_handlers;
pub mod network;
pub mod presets;
pub mod property;
pub mod reconfiguration;
pub mod rng;
pub mod runner;
pub mod scenario;
pub mod trace;
mod value_conv;

pub use analysis::{
    compare_observability, normalized_observability, NormalizedObservability,
    ObservabilityComparison, ObservabilityRelation,
};
pub use contracts::{
    assert_contracts, evaluate_contracts, ContractCheckConfig, ContractCheckReport,
};
pub use decision::{
    decide_async_subtyping, decide_capacity_predicate, decide_global_coherence,
    decide_global_well_formedness, decide_sync_subtyping, decide_theorem_eligibility,
    theorem_eligibility_from_result, AsyncSubtypeWitness, CapacityCounterexample, CoherenceFailure,
    DecisionCertificate, DecisionCounterexample, DecisionKind, DecisionOutcome, DecisionReport,
    SyncSubtypeWitness, TheoremEligibilityCounterexample, WellFormednessViolation,
};
pub use distributed::{DistributedSimBuilder, DistributedSimulation, NestedExecutionContract};
pub use fault::{
    AdversaryAction, AdversaryBudget, AdversaryBudgetMode, AdversaryBudgetRecord,
    AdversaryBudgetRecordKind, AdversaryInjector, AdversaryProgram, AdversarySummary,
    AssumptionDiagnostic, AssumptionFailureClass, ScheduledAdversary, Trigger,
};
pub use harness::{
    derive_initial_states, derive_initial_states_for_model, BatchConfig, BatchRunManifest,
    BatchRunManifestEntry, BatchRunResult, DirectAdapter, HarnessConfig, HarnessSpec, HostAdapter,
    MaterialAdapter, SimulationHarness,
};
pub use material::{MaterialModel, MaterialParams};
pub use material_handlers::{
    handler_from_material, handler_from_model, ContinuumFieldHandler, HamiltonianHandler,
    IsingHandler,
};
pub use network::{NetworkConfig, NetworkModel};
pub use property::{Property, PropertyMonitor};
pub use reconfiguration::{
    ReconfigurationAction, ReconfigurationController, ReconfigurationEffect,
    ReconfigurationEffectKind, ReconfigurationFootprint, ReconfigurationLink,
    ReconfigurationRecord, ReconfigurationSummary, ScheduledReconfiguration,
};
pub use rng::SimRng;
pub use runner::{
    compare_scheduler_runs, CriticalCapacityPhase, CriticalCapacitySummary,
    ScenarioAnalysisArtifact, SchedulerBoundMode, SchedulerComparison, SchedulerEnvelopeStatus,
    SchedulerFairnessRequirement, SchedulerProfileSummary, TheoremProgressSummary,
};
pub use telltale_machine::model::effects::EffectHandler;
