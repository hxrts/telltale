//! Pure artifact, query, command, and application-service models for the
//! Telltale simulator webapp.
//!
//! This crate deliberately keeps browser APIs and renderer concerns out of the
//! artifact boundary so `telltale-ui` and `telltale-web` can remain thin
//! consumers of the same deterministic model surface.

#![allow(missing_docs)]

pub mod error;
pub mod service;
pub mod types;

#[cfg(test)]
mod tests;

pub use error::ViewerModelError;
pub use service::{InMemoryViewerService, ViewerApplicationService};
pub use types::*;

pub use telltale_simulator::analysis::{
    compare_observability, NormalizedObservability, ObservabilityComparison, ObservabilityRelation,
};
pub use telltale_simulator::approximation::ApproximationManifest;
pub use telltale_simulator::contracts::ContractCheckReport;
pub use telltale_simulator::decision::{
    decide_theorem_eligibility, DecisionCounterexample, DecisionKind, DecisionOutcome,
    DecisionReport,
};
pub use telltale_simulator::durability::DurableInspectionReport;
pub use telltale_simulator::environment::{EnvironmentTrace, TransmissionIntent};
pub use telltale_simulator::reconfiguration::ReconfigurationRecord;
pub use telltale_simulator::runner::{
    ScenarioAnalysisArtifact, ScenarioReplayArtifact, ScenarioResult, ScenarioStats,
    SchedulerComparison,
};
pub use telltale_simulator::scenario::{
    ExecutionBackend, ReconfigurationSpec, ResolvedExecutionBackend, ResolvedTheoremProfile,
    Scenario, SchedulerPolicySpec, TheoremProfileSpec,
};
pub use telltale_simulator::sweep::{SweepDiffReport, SweepManifest};
pub use telltale_simulator::trace::Trace;
