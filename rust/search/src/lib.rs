//! Generic deterministic weighted-graph search substrate for Telltale.
//!
//! `telltale-search` holds reusable search-machine semantics, replay-ready
//! artifacts, and runtime/admission vocabulary for weighted graph search over
//! explicit graph epochs.
//!
//! The crate is intentionally generic:
//!
//! - it does not define application-specific transport or routing concepts,
//! - it does not depend on simulator, viewer, or web crates,
//! - it is meant to be extended by downstream domain implementations via typed
//!   search traits and adapters.

pub mod admission;
pub mod cost;
pub mod domain;
pub mod machine;
pub mod observe;
pub mod runtime;

pub use admission::{
    check_capability_containment, AdmissionRejectionReason, CommutativityRegionClass,
    SearchCertifiedCapability, SearchDUser, SearchDeterminismMode, SearchFairnessAssumption,
    SearchObservableClass, SearchSchedulerProfile,
};
pub use cost::{EpsilonMilli, SearchCost};
pub use domain::SearchDomain;
pub use machine::{
    CanonicalBatch, Incumbent, Proposal, ProposalKind, SearchBudgetState, SearchError,
    SearchInvariantViolation, SearchMachine, SearchTraceState,
};
pub use observe::{
    compare_observations, IncumbentPublicationRecord, NormalizedCommitRecord,
    ObservationComparison, ObservationRelation, SearchObservationArtifact,
};
pub use runtime::{
    classify_fairness_claim, classify_scheduler_artifact, commit_epoch_reconfiguration,
    fairness_artifact_for_profile, proposals_independent, replay_observation, run_with_executor,
    search_theorem_pack_artifact, theorem_backed_observables, validate_fairness_certificate_trace,
    validate_run_config, AuthorityReadSet, AuthoritySurface, AuthorityWriteSet,
    EpochReconfigurationRequest, NativeParallelExecutor, NativeParallelExecutorError,
    ProgressSummary, ProposalExecutor, ProposalExecutorKind, ReplayError, ReplayExpectation,
    ReplayRoundRecord, SchedulerArtifact, SchedulerArtifactClass, SearchExecutionReport,
    SearchFairnessArtifact, SearchFairnessCertificate, SearchFairnessCertificateClass,
    SearchFairnessClaimClass, SearchFairnessTraceValidationError, SearchReplayArtifact,
    SearchRouteBoundArtifact, SearchRouteDiscoveryBoundClass, SearchRouteDiscoveryCertificate,
    SearchRouteDiscoveryCertificateClass, SearchRouteMetric, SearchRouteMetricName,
    SearchRouteQualityClass, SearchRouteSummary, SearchRunConfig, SearchRunConfigError,
    SearchRunError, SearchRuntimeMarker, SearchStateArtifact, SearchTheoremInventoryEntry,
    SearchTheoremInventorySupportClassEntry, SearchTheoremPackArtifact, SearchTheoremSupportClass,
    SerialProposalExecutor, TotalStepMode,
};

/// Current crate scope statement used by smoke tests and boundary checks.
pub const CRATE_SCOPE: &str = "generic weighted-graph-plus-epoch search";
