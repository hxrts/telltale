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
pub mod approximation;
#[doc(hidden)]
pub mod backend;
pub mod checkpoint;
pub mod contracts;
pub mod decision;
pub mod distributed;
pub mod durability;
pub mod environment;
#[doc(hidden)]
pub mod execution;
pub mod fault;
pub mod field;
pub mod field_handlers;
/// Generated effect-family simulator helpers and scenario surfaces.
pub mod generated;
pub mod harness;
pub mod network;
pub mod persistence;
pub mod presets;
pub mod property;
pub mod reconfiguration;
pub mod rng;
pub mod runner;
pub mod scenario;
pub mod search;
pub mod sweep;
pub mod trace;
mod value_conv;

pub use analysis::{
    compare_observability, normalized_observability, NormalizedObservability,
    ObservabilityComparison, ObservabilityRelation,
};
pub use approximation::{
    compare_exact_and_approximate, run_approximation, ApproximationAdmissibility,
    ApproximationArtifact, ApproximationComparison, ApproximationFamily, ApproximationManifest,
    ApproximationObservables, ApproximationScope, ApproximationSpec,
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
pub use distributed::{
    DistributedExecutionRegime, DistributedRunManifest, DistributedRunResult,
    DistributedSimBuilder, DistributedSimulation, DistributedSiteResult, NestedExecutionContract,
};
pub use durability::{
    durable_property_report, inspect_durable_artifacts, monitor_evidence_consistency,
    monitor_monotonic_wal_levels, monitor_recovery_equivalence, monitor_write_ahead,
    run_durable_recovery_case, DurableFaultKind, DurableFaultOutcome, DurableFaultProgram,
    DurableFaultRecord, DurableInspectionReport, DurablePropertyReport, DurableRecoveryRun,
    DurableWalEntryKind, DurableWalEntryProjection, EvidenceCacheEntryProjection,
    FaultInjectingAgreementWal, ScheduledDurableFault,
};
pub use environment::{
    EnvironmentArtifact, EnvironmentController, EnvironmentModels, EnvironmentSnapshot,
    EnvironmentTrace, LinkAdmissionDecision, LinkAdmissionModel, MediumModel, MediumOutcomeKind,
    MediumResolution, MobilityModel, NodeCapabilityModel, NodeCapabilityState, NodePose,
    PotentialLink, TopologyModel, TransmissionIntent,
};
pub use fault::{
    AdversaryAction, AdversaryBudget, AdversaryBudgetMode, AdversaryBudgetRecord,
    AdversaryBudgetRecordKind, AdversaryInjector, AdversaryProgram, AdversarySummary,
    AssumptionDiagnostic, AssumptionFailureClass, ScheduledAdversary, Trigger,
};
pub use field::{ContinuumFieldSpec, FieldModel, FieldSpec, HamiltonianFieldSpec, MeanFieldSpec};
pub use field_handlers::{
    handler_from_field, handler_from_field_model, ContinuumFieldHandler, HamiltonianHandler,
    IsingHandler,
};
pub use harness::{
    derive_initial_states, derive_initial_states_for_field_model, BatchConfig, BatchRunManifest,
    BatchRunManifestEntry, BatchRunResult, DirectAdapter, FieldAdapter, HarnessConfig, HarnessSpec,
    HostAdapter, SimulationHarness,
};
pub use network::{NetworkConfig, NetworkModel};
pub use persistence::{CheckpointArtifact, PersistedReplayArtifact, PersistedReplayPayload};
pub use property::{Property, PropertyMonitor};
pub use reconfiguration::{
    ReconfigurationAction, ReconfigurationController, ReconfigurationEffect,
    ReconfigurationEffectKind, ReconfigurationFootprint, ReconfigurationLink,
    ReconfigurationRecord, ReconfigurationSummary, ScheduledReconfiguration,
};
pub use rng::SimRng;
pub use runner::{
    canonical_replay_scenario, compare_scheduler_runs, remaining_rounds_from_checkpoint,
    resume_with_checkpoint_artifact, resume_with_durable_checkpoint_artifact,
    resume_with_scenario_from_checkpoint, run_canonical_replay, CriticalCapacityPhase,
    CriticalCapacitySummary, DurableResumeArtifacts, DurableResumeSummary,
    ScenarioAnalysisArtifact, SchedulerBoundMode, SchedulerComparison, SchedulerEnvelopeStatus,
    SchedulerFairnessRequirement, SchedulerProfileSummary, TheoremProgressSummary,
};
pub use search::{project_search_run, SearchSimulationArtifact};
pub use sweep::{
    compare_sweep_results, run_sweep, SweepAxis, SweepBinding, SweepConfig, SweepDiffReport,
    SweepManifest, SweepManifestEntry, SweepRunDiff, SweepRunResult,
};
pub use telltale_machine::model::effects::EffectHandler;
