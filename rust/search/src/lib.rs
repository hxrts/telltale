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
//!
//! Runtime execution policy is explicit and separate from downstream search
//! problem semantics. Downstream domains define node/edge meaning, heuristic
//! policy, and objective semantics; runtime policy chooses scheduler profile,
//! batch width, caching mode, and effort regime without changing that
//! objective meaning.
//!
//! `SearchQuery` provides the built-in generic problem adapters:
//!
//! - `SingleGoal` for classic one-goal path search
//! - `MultiGoal` for any-of-N terminal search
//! - `CandidateSet` for selector-style best-candidate search
//!
//! The historical incumbent/route vocabulary remains available for
//! compatibility, but the crate now also exports selected-solution aliases so
//! downstream code can migrate toward generic result terminology.

pub mod admission;
pub mod cost;
pub mod domain;
pub mod machine;
pub mod observe;
pub mod runtime;

pub use admission::{
    check_capability_containment, AdmissionRejectionReason, CommutativityRegionClass,
    SearchCertifiedCapability, SearchClaimClass, SearchDUser, SearchDeterminismMode,
    SearchFairnessAssumption, SearchObservableClass, SearchSchedulerProfile,
    SELECTED_RESULT_COST_OBSERVABLE, SELECTED_RESULT_PUBLICATION_TRACE_OBSERVABLE,
    SELECTED_RESULT_WITNESS_OBSERVABLE,
};
pub use cost::{EpsilonMilli, SearchCost};
pub use domain::{
    SearchDomain, SearchQuery, SearchQueryError, SearchReseedingPolicy,
    SearchSelectedResultSemanticsClass,
};
pub use machine::{
    CanonicalBatch, Proposal, ProposalKind, SearchBudgetState, SearchError,
    SearchInvariantViolation, SearchMachine, SearchTraceState, SelectedSolution,
};
pub use observe::{
    compare_observations, NormalizedCommitRecord, ObservationComparison, ObservationRelation,
    SearchObservationArtifact, SearchSelectedResultArtifact, SelectedSolutionPublicationRecord,
};
pub use runtime::{
    classify_approximation_contract, classify_fairness_claim, classify_scheduler_artifact,
    classify_theorem_problem_class, commit_epoch_reconfiguration, default_proposal_read_set,
    default_proposal_write_set, fairness_artifact_for_profile, full_state_artifact_for_machine,
    proposals_independent, replay_observation, run_with_executor, run_with_executor_report_only,
    search_theorem_pack_artifact, theorem_backed_observables, theorem_inventory_problem_classes,
    validate_fairness_certificate_trace, validate_run_config, AuthorityReadSet, AuthoritySurface,
    AuthorityWriteSet, EpochReconfigurationRequest, NativeParallelExecutor,
    NativeParallelExecutorError, ProgressSummary, ProposalExecutor, ProposalExecutorKind,
    ReplayError, ReplayExpectation, ReplayRoundRecord, SchedulerArtifact, SchedulerArtifactClass,
    SearchApproximationArtifact, SearchApproximationContractClass, SearchAuthorityPolicy,
    SearchCachingProfile, SearchEffortProfile, SearchExecutionPolicy, SearchExecutionReport,
    SearchFairnessArtifact, SearchFairnessCertificate, SearchFairnessCertificateClass,
    SearchFairnessClaimClass, SearchFairnessTraceValidationError, SearchFullStateArtifact,
    SearchPathProblemDiscoveryArtifact, SearchPathProblemReplayArtifact, SearchPathResultSummary,
    SearchReplayArtifact, SearchResultBoundArtifact, SearchResultDiscoveryBoundClass,
    SearchResultDiscoveryCertificate, SearchResultDiscoveryCertificateClass, SearchResultMetric,
    SearchResultMetricName, SearchResultQualityClass, SearchResultSummary, SearchRunConfig,
    SearchRunConfigError, SearchRunError, SearchRunTermination, SearchRuntimeMarker,
    SearchSelectedResultBoundArtifact, SearchSelectedResultMetric, SearchSelectedResultMetricName,
    SearchSelectedResultSummary, SearchStateArtifact, SearchTheoremInventoryEntry,
    SearchTheoremInventoryProblemClassEntry, SearchTheoremInventorySupportClassEntry,
    SearchTheoremPackArtifact, SearchTheoremProblemClass, SearchTheoremSupportClass,
    SerialProposalExecutor, TotalStepMode,
};

/// Narrow compatibility surface retained for downstream migration from the
/// historical route/incumbent vocabulary.
pub mod compat {
    pub use crate::machine::Incumbent;
    pub use crate::observe::IncumbentPublicationRecord;
    pub use crate::runtime::compat::{
        SearchRouteBoundArtifact, SearchRouteDiscoveryBoundClass, SearchRouteDiscoveryCertificate,
        SearchRouteDiscoveryCertificateClass, SearchRouteMetric, SearchRouteMetricName,
        SearchRouteProblemDiscoveryArtifact, SearchRouteQualityClass, SearchRouteSummary,
    };
}

/// Current crate scope statement used by smoke tests and boundary checks.
pub const CRATE_SCOPE: &str = "generic weighted-graph-plus-epoch search";
