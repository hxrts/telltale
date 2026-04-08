//! Runtime, scheduler, replay, and reconfiguration boundary for
//! `telltale-search`.

mod authority;
mod executor;
mod lifecycle;

pub use authority::{proposals_independent, AuthorityReadSet, AuthoritySurface, AuthorityWriteSet};
pub use executor::{
    NativeParallelExecutor, NativeParallelExecutorError, ProposalExecutor, SerialProposalExecutor,
};
pub use lifecycle::{
    classify_scheduler_artifact, commit_epoch_reconfiguration, replay_observation,
    run_with_executor, EpochReconfigurationRequest, ProgressSummary, ReplayError,
    ReplayExpectation, ReplayRoundRecord, SchedulerArtifact, SchedulerArtifactClass,
    SearchExecutionReport, SearchReplayArtifact, SearchRunConfig, SearchRuntimeMarker,
    TotalStepMode,
};
