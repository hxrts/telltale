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
    CanonicalBatch, FrontierEntry, FrontierScore, Incumbent, ParentRecord, Proposal, ProposalKind,
    SearchBudgetState, SearchError, SearchInvariantViolation, SearchMachine, SearchState,
    SearchTraceState,
};
pub use observe::{
    compare_observations, NormalizedCommitRecord, ObservationComparison, ObservationRelation,
    SearchObservationArtifact,
};

/// Current crate scope statement used by smoke tests and boundary checks.
pub const CRATE_SCOPE: &str = "generic weighted-graph-plus-epoch search";
