//! Runtime, scheduler, replay, and reconfiguration boundary for
//! `telltale-search`.

mod authority;
mod executor;
mod lifecycle;

pub use authority::{
    default_proposal_read_set, default_proposal_write_set, proposals_independent, AuthorityReadSet,
    AuthoritySurface, AuthorityWriteSet, SearchAuthorityPolicy,
};
pub use executor::{
    NativeParallelExecutor, NativeParallelExecutorError, ProposalExecutor, ProposalExecutorKind,
    SerialProposalExecutor,
};
pub use lifecycle::{
    classify_approximation_contract, classify_fairness_claim, classify_scheduler_artifact,
    classify_theorem_problem_class, commit_epoch_reconfiguration, fairness_artifact_for_profile,
    full_state_artifact_for_machine, replay_observation, run_with_executor,
    run_with_executor_report_only, search_theorem_pack_artifact, theorem_backed_observables,
    theorem_inventory_problem_classes, validate_fairness_certificate_trace, validate_run_config,
    EpochReconfigurationRequest, ProgressSummary, ReplayError, ReplayExpectation,
    ReplayRoundRecord, SchedulerArtifact, SchedulerArtifactClass, SearchApproximationArtifact,
    SearchApproximationContractClass, SearchCachingProfile, SearchEffortProfile,
    SearchExecutionPolicy, SearchExecutionReport, SearchFairnessArtifact,
    SearchFairnessCertificate, SearchFairnessCertificateClass, SearchFairnessClaimClass,
    SearchFairnessTraceValidationError, SearchFullStateArtifact,
    SearchPathProblemDiscoveryArtifact, SearchPathProblemReplayArtifact, SearchPathResultSummary,
    SearchReplayArtifact, SearchResultBoundArtifact, SearchResultDiscoveryBoundClass,
    SearchResultDiscoveryCertificate, SearchResultDiscoveryCertificateClass, SearchResultMetric,
    SearchResultMetricName, SearchResultQualityClass, SearchResultSummary, SearchRunConfig,
    SearchRunConfigError, SearchRunError, SearchRunTermination, SearchRuntimeMarker,
    SearchSelectedResultBoundArtifact, SearchSelectedResultMetric, SearchSelectedResultMetricName,
    SearchSelectedResultSummary, SearchStateArtifact, SearchTheoremInventoryEntry,
    SearchTheoremInventoryProblemClassEntry, SearchTheoremInventorySupportClassEntry,
    SearchTheoremPackArtifact, SearchTheoremProblemClass, SearchTheoremSupportClass, TotalStepMode,
};

/// Narrow compatibility surface retained for downstream migration from the
/// historical route-oriented runtime vocabulary.
pub mod compat {
    pub use super::lifecycle::{
        SearchRouteBoundArtifact, SearchRouteDiscoveryBoundClass, SearchRouteDiscoveryCertificate,
        SearchRouteDiscoveryCertificateClass, SearchRouteMetric, SearchRouteMetricName,
        SearchRouteProblemDiscoveryArtifact, SearchRouteQualityClass, SearchRouteSummary,
    };
}
