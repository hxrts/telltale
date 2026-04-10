//! Runtime, scheduler, replay, and reconfiguration boundary for
//! `telltale-search`.

mod authority;
mod executor;
mod lifecycle;

pub use authority::{proposals_independent, AuthorityReadSet, AuthoritySurface, AuthorityWriteSet};
pub use executor::{
    NativeParallelExecutor, NativeParallelExecutorError, ProposalExecutor, ProposalExecutorKind,
    SerialProposalExecutor,
};
pub use lifecycle::{
    classify_fairness_claim, classify_scheduler_artifact, commit_epoch_reconfiguration,
    fairness_artifact_for_profile, full_state_artifact_for_machine, replay_observation,
    run_with_executor, search_theorem_pack_artifact, theorem_backed_observables,
    validate_fairness_certificate_trace, validate_run_config, EpochReconfigurationRequest,
    ProgressSummary, ReplayError, ReplayExpectation, ReplayRoundRecord, SchedulerArtifact,
    SchedulerArtifactClass, SearchExecutionReport, SearchFairnessArtifact,
    SearchFairnessCertificate, SearchFairnessCertificateClass, SearchFairnessClaimClass,
    SearchFairnessTraceValidationError, SearchFullStateArtifact, SearchReplayArtifact,
    SearchRouteBoundArtifact, SearchRouteDiscoveryBoundClass, SearchRouteDiscoveryCertificate,
    SearchRouteDiscoveryCertificateClass, SearchRouteMetric, SearchRouteMetricName,
    SearchRouteQualityClass, SearchRouteSummary, SearchRunConfig, SearchRunConfigError,
    SearchRunError, SearchRuntimeMarker, SearchStateArtifact, SearchTheoremInventoryEntry,
    SearchTheoremInventorySupportClassEntry, SearchTheoremPackArtifact, SearchTheoremSupportClass,
    TotalStepMode,
};
