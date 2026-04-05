//! Pure artifact, query, command, and application-service models for the
//! Telltale simulator webapp.
//!
//! This crate deliberately keeps browser APIs and renderer concerns out of the
//! artifact boundary so `telltale-ui` and `telltale-web` can remain thin
//! consumers of the same deterministic model surface.

#![allow(missing_docs)]

use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::fmt;
use std::fs;
use std::path::Path;
use telltale_macros::authoritative_source;

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

/// Stable top-level file format marker for viewer artifacts.
pub const VIEWER_ARTIFACT_FORMAT: &str = "telltale.viewer.artifact";
/// Initial schema version for viewer artifacts.
pub const VIEWER_ARTIFACT_SCHEMA_V1: u32 = 1;

/// Stable identifier for one artifact in the viewer service.
pub type ArtifactId = String;
/// Stable identifier for one logical run/workspace.
pub type RunId = String;
/// Stable identifier for one derived branch.
pub type BranchId = String;

/// Versioned viewer artifact file stored on disk.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ViewerArtifactFile {
    /// Stable format marker for loader dispatch.
    pub format: String,
    /// Versioned schema number for the payload below.
    pub schema_version: u32,
    /// Typed artifact payload.
    pub artifact: ViewerArtifact,
}

impl ViewerArtifactFile {
    /// Wrap one viewer artifact in the current schema envelope.
    #[must_use]
    pub fn new(artifact: ViewerArtifact) -> Self {
        Self {
            format: VIEWER_ARTIFACT_FORMAT.to_string(),
            schema_version: VIEWER_ARTIFACT_SCHEMA_V1,
            artifact,
        }
    }

    /// Load a viewer artifact file from JSON on disk.
    ///
    /// # Errors
    ///
    /// Returns a descriptive error when the file is unreadable, malformed, or
    /// uses an unsupported schema version.
    pub fn load_json(path: impl AsRef<Path>) -> Result<Self, ViewerModelError> {
        let path = path.as_ref();
        let source = fs::read_to_string(path).map_err(|error| ViewerModelError::Io {
            path: path.display().to_string(),
            message: error.to_string(),
        })?;
        let parsed = serde_json::from_str::<Self>(&source).map_err(|error| {
            ViewerModelError::InvalidArtifactFile {
                message: format!("{}: {error}", path.display()),
            }
        })?;
        parsed.validate()?;
        Ok(parsed)
    }

    /// Write one viewer artifact file as pretty JSON.
    ///
    /// # Errors
    ///
    /// Returns a descriptive error when serialization or writing fails.
    pub fn write_json(&self, path: impl AsRef<Path>) -> Result<(), ViewerModelError> {
        self.validate()?;
        let path = path.as_ref();
        let json = serde_json::to_string_pretty(self).map_err(|error| {
            ViewerModelError::Serialization {
                message: error.to_string(),
            }
        })?;
        fs::write(path, format!("{json}\n")).map_err(|error| ViewerModelError::Io {
            path: path.display().to_string(),
            message: error.to_string(),
        })
    }

    /// Validate envelope metadata.
    ///
    /// # Errors
    ///
    /// Returns a descriptive error when the format marker or schema version is unsupported.
    pub fn validate(&self) -> Result<(), ViewerModelError> {
        if self.format != VIEWER_ARTIFACT_FORMAT {
            return Err(ViewerModelError::InvalidArtifactFile {
                message: format!(
                    "unsupported artifact format `{}`; expected `{VIEWER_ARTIFACT_FORMAT}`",
                    self.format
                ),
            });
        }
        if self.schema_version != VIEWER_ARTIFACT_SCHEMA_V1 {
            return Err(ViewerModelError::UnsupportedSchemaVersion {
                supported: VIEWER_ARTIFACT_SCHEMA_V1,
                found: self.schema_version,
            });
        }
        Ok(())
    }

    /// Return the typed artifact kind.
    #[must_use]
    pub fn kind(&self) -> ViewerArtifactKind {
        self.artifact.kind()
    }
}

/// One typed artifact payload consumed by the viewer stack.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "kind", content = "payload", rename_all = "snake_case")]
pub enum ViewerArtifact {
    /// Full scenario-plus-result bundle.
    ScenarioBundle(Box<ScenarioBundleArtifact>),
    /// Standalone theorem/decision report.
    DecisionReport(DecisionReport),
    /// Standalone environment trace.
    EnvironmentTrace(EnvironmentTrace),
    /// Standalone reconfiguration trace.
    ReconfigurationTrace(Vec<ReconfigurationRecord>),
    /// Standalone sweep manifest.
    SweepManifest(SweepManifest),
    /// Standalone sweep diff report.
    SweepDiffReport(SweepDiffReport),
    /// Standalone scheduler comparison report.
    SchedulerComparison(SchedulerComparison),
    /// Standalone normalized observability comparison report.
    ObservabilityComparison(ObservabilityComparison),
    /// Standalone approximation manifest.
    ApproximationManifest(ApproximationManifest),
    /// Standalone contract-check report.
    ContractCheckReport(ContractCheckReport),
    /// Higher-level semantic comparison result.
    SemanticComparison(Box<SemanticComparisonResult>),
    /// Reusable theorem-aware counterexample.
    Counterexample(Box<TheoremAwareCounterexample>),
    /// Deterministic sweep report over archived run artifacts.
    SweepReport(Box<DeterministicSweepReport>),
    /// Experiment-suite baseline/candidate report.
    ExperimentSuite(Box<ExperimentSuiteReport>),
    /// Typed effect-trace artifact for one run or branch.
    EffectTrace(Box<EffectTraceArtifact>),
    /// Observed-only durable inspection report.
    DurableInspection(Box<DurableInspectionReport>),
    /// Deterministic minimization result.
    Minimization(Box<MinimizationResult>),
}

impl ViewerArtifact {
    /// Return the stable payload kind.
    #[must_use]
    pub const fn kind(&self) -> ViewerArtifactKind {
        match self {
            Self::ScenarioBundle(_) => ViewerArtifactKind::ScenarioBundle,
            Self::DecisionReport(_) => ViewerArtifactKind::DecisionReport,
            Self::EnvironmentTrace(_) => ViewerArtifactKind::EnvironmentTrace,
            Self::ReconfigurationTrace(_) => ViewerArtifactKind::ReconfigurationTrace,
            Self::SweepManifest(_) => ViewerArtifactKind::SweepManifest,
            Self::SweepDiffReport(_) => ViewerArtifactKind::SweepDiffReport,
            Self::SchedulerComparison(_) => ViewerArtifactKind::SchedulerComparison,
            Self::ObservabilityComparison(_) => ViewerArtifactKind::ObservabilityComparison,
            Self::ApproximationManifest(_) => ViewerArtifactKind::ApproximationManifest,
            Self::ContractCheckReport(_) => ViewerArtifactKind::ContractCheckReport,
            Self::SemanticComparison(_) => ViewerArtifactKind::SemanticComparison,
            Self::Counterexample(_) => ViewerArtifactKind::Counterexample,
            Self::SweepReport(_) => ViewerArtifactKind::SweepReport,
            Self::ExperimentSuite(_) => ViewerArtifactKind::ExperimentSuite,
            Self::EffectTrace(_) => ViewerArtifactKind::EffectTrace,
            Self::DurableInspection(_) => ViewerArtifactKind::DurableInspection,
            Self::Minimization(_) => ViewerArtifactKind::Minimization,
        }
    }
}

/// Stable artifact payload kind.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq, PartialOrd, Ord)]
#[serde(rename_all = "snake_case")]
pub enum ViewerArtifactKind {
    ScenarioBundle,
    DecisionReport,
    EnvironmentTrace,
    ReconfigurationTrace,
    SweepManifest,
    SweepDiffReport,
    SchedulerComparison,
    ObservabilityComparison,
    ApproximationManifest,
    ContractCheckReport,
    SemanticComparison,
    Counterexample,
    SweepReport,
    ExperimentSuite,
    EffectTrace,
    DurableInspection,
    Minimization,
}

/// Scenario-plus-result bundle used by the viewer stack.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ScenarioBundleArtifact {
    /// Optional originating scenario config when available.
    pub scenario: Option<Scenario>,
    /// Canonical simulator run result.
    pub result: ScenarioResult,
    /// Optional contract-check output captured beside the run.
    pub contracts: Option<ContractCheckReport>,
}

impl ScenarioBundleArtifact {
    /// Build one scenario bundle from a canonical simulator result.
    #[must_use]
    pub fn new(
        scenario: Option<Scenario>,
        result: ScenarioResult,
        contracts: Option<ContractCheckReport>,
    ) -> Self {
        Self {
            scenario,
            result,
            contracts,
        }
    }

    /// Stable summary for inventory UIs and query results.
    #[must_use]
    pub fn summary(&self) -> ScenarioBundleSummary {
        let scenario_name = self
            .scenario
            .as_ref()
            .map(|scenario| scenario.name.clone())
            .unwrap_or_else(|| "unnamed_scenario".to_string());
        let branch_id = "root".to_string();
        ScenarioBundleSummary {
            scenario_name,
            execution_backend: self.result.stats.backend,
            theorem_profile: self.result.stats.theorem_profile.clone(),
            total_steps_sampled: u64::try_from(self.result.trace.records.len()).unwrap_or(u64::MAX),
            total_obs_events: u64::try_from(self.result.replay.obs_trace.len()).unwrap_or(u64::MAX),
            total_effect_events: u64::try_from(self.result.replay.effect_trace.len())
                .unwrap_or(u64::MAX),
            root_branch_id: branch_id,
        }
    }
}

/// Stable scenario-bundle summary surfaced by queries and inventories.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct ScenarioBundleSummary {
    pub scenario_name: String,
    pub execution_backend: ResolvedExecutionBackend,
    pub theorem_profile: ResolvedTheoremProfile,
    pub total_steps_sampled: u64,
    pub total_obs_events: u64,
    pub total_effect_events: u64,
    pub root_branch_id: BranchId,
}

/// Canonical generic report model rendered by the first shared viewer shell.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct ViewerReport {
    pub artifacts: Vec<ArtifactInventoryEntry>,
    pub scenario_summaries: Vec<ViewerScenarioReport>,
    pub artifact_family_counts: BTreeMap<ViewerArtifactKind, u64>,
}

/// Stable scenario card content derived from one scenario bundle artifact.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct ViewerScenarioReport {
    pub artifact_id: ArtifactId,
    pub summary: ScenarioBundleSummary,
}

impl ViewerReport {
    /// Load the canonical generic viewer report through the typed query surface.
    ///
    /// # Errors
    ///
    /// Returns any query or decoding errors from the backing application service.
    pub fn load(service: &impl ViewerApplicationService) -> Result<Self, ViewerModelError> {
        let ViewerQueryResult::ArtifactInventory { artifacts } =
            service.query(ViewerQuery::ListArtifacts)?
        else {
            return Err(ViewerModelError::UnexpectedQueryShape {
                expected: "artifact_inventory".to_string(),
            });
        };
        let mut artifact_family_counts: BTreeMap<ViewerArtifactKind, u64> = BTreeMap::new();
        let mut scenario_summaries = Vec::new();
        for artifact in &artifacts {
            *artifact_family_counts.entry(artifact.kind).or_insert(0) = artifact_family_counts
                .get(&artifact.kind)
                .copied()
                .unwrap_or(0)
                .saturating_add(1);
            if artifact.kind == ViewerArtifactKind::ScenarioBundle {
                let ViewerQueryResult::ScenarioSummary { summary } =
                    service.query(ViewerQuery::ScenarioSummary {
                        artifact_id: artifact.artifact_id.clone(),
                    })?
                else {
                    return Err(ViewerModelError::UnexpectedQueryShape {
                        expected: "scenario_summary".to_string(),
                    });
                };
                scenario_summaries.push(ViewerScenarioReport {
                    artifact_id: artifact.artifact_id.clone(),
                    summary,
                });
            }
        }
        Ok(Self {
            artifacts,
            scenario_summaries,
            artifact_family_counts,
        })
    }
}

/// Stable graph projection family requested by the UI layer.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum GraphProjectionKind {
    ChoreographyStructure,
    InstantiatedProtocol,
    ExecutionTimeline,
    BranchLineage,
}

/// Stable query model owned by the application service boundary.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum ViewerQuery {
    ListArtifacts,
    LoadArtifact {
        artifact_id: ArtifactId,
    },
    ScenarioSummary {
        artifact_id: ArtifactId,
    },
    BranchLineage {
        run_id: RunId,
    },
    GraphProjection(GraphProjectionRequest),
    Search(SearchQuery),
    HistoricalInspection(HistoricalInspectionState),
    SemanticComparison(SemanticComparisonRequest),
    FirstDivergence(SemanticComparisonRequest),
    ComparisonCounterexample(SemanticComparisonRequest),
    ArtifactCounterexample {
        artifact_id: ArtifactId,
    },
    SweepExplorer(SweepExplorerRequest),
    ExperimentSuite {
        suite_id: String,
    },
    EffectTrace {
        artifact_id: ArtifactId,
        branch_id: BranchId,
    },
    Minimization {
        request_id: String,
    },
    ExtensionManifest,
}

/// Stable query result surface returned by the application service.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum ViewerQueryResult {
    ArtifactInventory {
        artifacts: Vec<ArtifactInventoryEntry>,
    },
    ArtifactFile {
        artifact: Box<ViewerArtifactFile>,
    },
    ScenarioSummary {
        summary: ScenarioBundleSummary,
    },
    BranchLineage {
        lineage: BranchLineageProjection,
    },
    GraphProjection {
        projection: GraphProjection,
    },
    SearchResults {
        matches: Vec<SearchResult>,
    },
    HistoricalInspection {
        state: HistoricalInspectionState,
    },
    SemanticComparison {
        comparison: Box<SemanticComparisonResult>,
    },
    FirstDivergence {
        divergence: Option<SemanticDivergencePoint>,
    },
    Counterexample {
        counterexample: Box<TheoremAwareCounterexample>,
    },
    SweepExplorer {
        explorer: Box<SweepExplorerView>,
    },
    ExperimentSuite {
        suite: Box<ExperimentSuiteReport>,
    },
    EffectTrace {
        effect_trace: Box<EffectTraceArtifact>,
    },
    Minimization {
        result: Box<MinimizationResult>,
    },
    ExtensionManifest {
        manifest: Box<ViewerExtensionManifest>,
    },
}

/// One registered artifact surfaced in inventory queries.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct ArtifactInventoryEntry {
    pub artifact_id: ArtifactId,
    pub kind: ViewerArtifactKind,
    pub label: String,
}

/// Stable graph projection request owned by the model/service layer.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct GraphProjectionRequest {
    pub run_id: RunId,
    pub branch_id: BranchId,
    pub step: Option<u64>,
    pub kind: GraphProjectionKind,
}

/// Stable graph projection returned by the application-service boundary.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct GraphProjection {
    pub run_id: RunId,
    pub branch_id: BranchId,
    pub step: Option<u64>,
    pub kind: GraphProjectionKind,
    pub nodes: Vec<GraphNode>,
    pub edges: Vec<GraphEdge>,
}

/// One stable graph node.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct GraphNode {
    pub id: String,
    pub label: String,
    pub category: String,
    pub step: Option<u64>,
}

/// One stable graph edge.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct GraphEdge {
    pub from: String,
    pub to: String,
    pub label: String,
    pub step: Option<u64>,
}

/// Stable search domains indexed by the pure model layer.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum SearchDomain {
    Role,
    Step,
    Branch,
    EventLabel,
    Artifact,
    Divergence,
    Sweep,
    Effect,
}

/// Search request over loaded viewer artifacts.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct SearchQuery {
    pub text: String,
    pub domain: Option<SearchDomain>,
}

/// One stable search match surfaced to the UI layer.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct SearchResult {
    pub artifact_id: ArtifactId,
    pub domain: SearchDomain,
    pub label: String,
    pub detail: String,
    pub branch_id: Option<BranchId>,
    pub step: Option<u64>,
}

/// Historical inspection position chosen by the user.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct HistoricalInspectionState {
    pub run_id: RunId,
    pub branch_id: BranchId,
    pub step: u64,
}

/// Stable command surface owned by the application service boundary.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum ViewerCommand {
    ImportArtifact {
        artifact_id: ArtifactId,
        artifact: Box<ViewerArtifactFile>,
    },
    CreateBranch {
        run_id: RunId,
        branch_id: BranchId,
        parent_branch_id: BranchId,
        from_step: u64,
        patch: ScenarioBranchPatch,
    },
    UpdateBranch {
        run_id: RunId,
        branch_id: BranchId,
        patch: ScenarioBranchPatch,
    },
    DeleteBranch {
        run_id: RunId,
        branch_id: BranchId,
    },
    RequestRerun {
        run_id: RunId,
        branch_id: BranchId,
    },
    ExecuteSweep {
        sweep_id: String,
        baseline_artifact_id: Option<ArtifactId>,
        cases: Vec<SweepCaseSpec>,
    },
    ExecuteExperimentSuite {
        definition: ExperimentSuiteDefinition,
    },
    RequestMockedRerun {
        run_id: RunId,
        branch_id: BranchId,
        overrides: Vec<EffectOverrideSpec>,
    },
    RequestMinimization {
        request: MinimizationRequest,
    },
    RegisterExtensions {
        manifest: ViewerExtensionManifest,
    },
}

/// Build a typed branch-creation command for one deterministic fork point.
#[must_use]
pub fn create_branch_command(
    run_id: RunId,
    branch_id: BranchId,
    parent_branch_id: BranchId,
    from_step: u64,
) -> ViewerCommand {
    ViewerCommand::CreateBranch {
        run_id,
        branch_id,
        parent_branch_id,
        from_step,
        patch: ScenarioBranchPatch {
            operations: vec![ScenarioPatchOperation::SetSteps {
                steps: from_step.saturating_add(1),
            }],
        },
    }
}

/// Build a typed branch-update command for one deterministic edit.
#[must_use]
pub fn update_branch_command(
    run_id: RunId,
    branch_id: BranchId,
    active_step: u64,
) -> ViewerCommand {
    ViewerCommand::UpdateBranch {
        run_id,
        branch_id,
        patch: ScenarioBranchPatch {
            operations: vec![ScenarioPatchOperation::SetSeed {
                seed: active_step.saturating_add(100),
            }],
        },
    }
}

/// Build a typed branch-deletion command.
#[must_use]
pub fn delete_branch_command(run_id: RunId, branch_id: BranchId) -> ViewerCommand {
    ViewerCommand::DeleteBranch { run_id, branch_id }
}

/// Build a typed mocked-rerun command for one effect operation.
#[must_use]
pub fn mocked_rerun_command(
    run_id: RunId,
    branch_id: BranchId,
    operation: impl Into<String>,
) -> ViewerCommand {
    ViewerCommand::RequestMockedRerun {
        run_id,
        branch_id,
        overrides: vec![EffectOverrideSpec {
            operation: operation.into(),
            mode: EffectOverrideMode::ForceSuccess,
            payload: None,
        }],
    }
}

/// Build a typed minimization request command for one branch.
#[must_use]
pub fn minimize_branch_command(
    request_id: impl Into<String>,
    artifact_id: ArtifactId,
    branch_id: BranchId,
) -> ViewerCommand {
    ViewerCommand::RequestMinimization {
        request: MinimizationRequest {
            request_id: request_id.into(),
            artifact_id,
            branch_id,
            strategy: MinimizationStrategy::FirstDivergencePrefix,
        },
    }
}

/// Stable command result surface returned by the application service boundary.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum ViewerCommandResult {
    ArtifactImported { artifact_id: ArtifactId },
    BranchCreated { run_id: RunId, branch_id: BranchId },
    BranchUpdated { run_id: RunId, branch_id: BranchId },
    BranchDeleted { run_id: RunId, branch_id: BranchId },
    RerunRequested { run_id: RunId, branch_id: BranchId },
    SweepExecuted { sweep_id: String },
    ExperimentSuiteExecuted { suite_id: String },
    MockedRerunRequested { run_id: RunId, branch_id: BranchId },
    MinimizationRequested { request_id: String },
    ExtensionsRegistered { count: usize },
}

/// Typed branch/scenario patch emitted by the UI layer.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct ScenarioBranchPatch {
    pub operations: Vec<ScenarioPatchOperation>,
}

/// Typed scenario delta applied by the application service.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum ScenarioPatchOperation {
    SetName {
        name: String,
    },
    SetSeed {
        seed: u64,
    },
    SetSteps {
        steps: u64,
    },
    SetExecutionBackend {
        backend: ExecutionBackend,
    },
    SetSchedulerPolicy {
        policy: SchedulerPolicySpec,
    },
    SetSchedulerConcurrency {
        lanes: u64,
    },
    SetWorkerThreads {
        worker_threads: u64,
    },
    ReplaceTheoremProfile {
        theorem: TheoremProfileSpec,
    },
    ReplaceScenario {
        scenario: Box<Scenario>,
    },
    UpsertExtension {
        namespace: String,
        value: toml::Value,
    },
    RemoveExtension {
        namespace: String,
    },
    ReplaceReconfigurations {
        items: Vec<ReconfigurationSpec>,
    },
}

/// Stable branch lineage projection returned by the application service.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct BranchLineageProjection {
    pub run_id: RunId,
    pub branches: Vec<BranchLineageNode>,
}

/// One branch in the lineage projection.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct BranchLineageNode {
    pub branch_id: BranchId,
    pub parent_branch_id: Option<BranchId>,
    pub from_step: u64,
    pub deleted: bool,
    pub rerun_requested: bool,
    pub patch_count: u64,
}

/// Stable comparison relation over generic simulator artifacts.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum SemanticComparisonClass {
    ExactMatch,
    EquivalentUnderNormalization,
    SafetyVisibleDivergence,
}

/// First semantically meaningful divergence family.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum SemanticDivergenceKind {
    TraceRecord,
    Observability,
    Reconfiguration,
    TheoremProfile,
    ExecutionRegime,
    EffectTrace,
    StepCount,
}

/// Stable divergence point for comparison and counterexample workflows.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct SemanticDivergencePoint {
    pub kind: SemanticDivergenceKind,
    pub step: Option<u64>,
    pub label: String,
    pub baseline_detail: String,
    pub candidate_detail: String,
}

/// Generic semantic comparison result consumed by the webapp and downstreams.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct SemanticComparisonResult {
    pub baseline_artifact_id: ArtifactId,
    pub candidate_artifact_id: ArtifactId,
    pub relation: SemanticComparisonClass,
    pub normalized_observability: ObservabilityComparison,
    pub classification_changed_only: bool,
    pub first_divergence: Option<SemanticDivergencePoint>,
    pub summary: String,
}

/// Comparison request between two viewer artifacts.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct SemanticComparisonRequest {
    pub baseline_artifact_id: ArtifactId,
    pub candidate_artifact_id: ArtifactId,
}

/// Reusable theorem-aware counterexample surface.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct TheoremAwareCounterexample {
    pub summary: String,
    pub theorem_profile: Option<ResolvedTheoremProfile>,
    pub execution_regime: Option<telltale_simulator::scenario::ExecutionRegime>,
    pub first_failed_assumption: Option<String>,
    pub divergence: Option<SemanticDivergencePoint>,
    pub decision_report: Option<DecisionReport>,
}

/// Deterministic sweep case specification over archived artifacts.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct SweepCaseSpec {
    pub case_id: String,
    pub artifact_id: ArtifactId,
    pub parameters: BTreeMap<String, String>,
}

/// One deterministic sweep case outcome.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct SweepCaseResult {
    pub case_id: String,
    pub artifact_id: ArtifactId,
    pub parameters: BTreeMap<String, String>,
    pub theorem_profile: Option<ResolvedTheoremProfile>,
    pub execution_regime: Option<telltale_simulator::scenario::ExecutionRegime>,
    pub comparison_to_baseline: Option<SemanticComparisonResult>,
}

/// Canonical deterministic sweep report over archived artifacts.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct DeterministicSweepReport {
    pub sweep_id: String,
    pub baseline_artifact_id: Option<ArtifactId>,
    pub cases: Vec<SweepCaseResult>,
}

/// Query model for one sweep explorer view.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct SweepExplorerRequest {
    pub sweep_id: String,
    pub filter_text: Option<String>,
    pub group_by: Option<String>,
    pub max_results: Option<usize>,
}

/// Explorer view returned for one deterministic sweep report.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct SweepExplorerView {
    pub sweep_id: String,
    pub total_cases: usize,
    pub visible_cases: Vec<SweepCaseResult>,
    pub outlier_case_ids: Vec<String>,
}

/// One baseline-vs-candidate experiment-suite case.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct ExperimentSuiteCase {
    pub case_id: String,
    pub baseline_artifact_id: ArtifactId,
    pub candidate_artifact_id: ArtifactId,
}

/// Regression-threshold policy for one suite.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct RegressionThreshold {
    pub max_changed_steps: u64,
    pub allow_normalization_only: bool,
}

/// Canonical experiment-suite definition built on comparison/sweep layers.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct ExperimentSuiteDefinition {
    pub suite_id: String,
    pub threshold: RegressionThreshold,
    pub cases: Vec<ExperimentSuiteCase>,
}

/// One case outcome within an experiment-suite report.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct ExperimentSuiteCaseResult {
    pub case_id: String,
    pub comparison: SemanticComparisonResult,
    pub threshold_passed: bool,
    pub counterexample: Option<TheoremAwareCounterexample>,
}

/// Reusable experiment-suite report with baseline/candidate regression output.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct ExperimentSuiteReport {
    pub definition: ExperimentSuiteDefinition,
    pub cases: Vec<ExperimentSuiteCaseResult>,
}

/// Stable effect-trace entry for viewer inspection.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct EffectTraceEntry {
    pub step: u64,
    pub kind: String,
    pub detail: String,
}

/// Typed effect-trace artifact used by the effect workspace.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct EffectTraceArtifact {
    pub artifact_id: ArtifactId,
    pub branch_id: BranchId,
    pub entries: Vec<EffectTraceEntry>,
    pub overrides: Vec<EffectOverrideSpec>,
}

/// Effect override mode for mocked reruns.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum EffectOverrideMode {
    ForceSuccess,
    ForceFailure,
    ReplacePayload,
}

/// Typed effect override attached to a rerun request.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct EffectOverrideSpec {
    pub operation: String,
    pub mode: EffectOverrideMode,
    pub payload: Option<serde_json::Value>,
}

/// Deterministic minimization strategy.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum MinimizationStrategy {
    FirstDivergencePrefix,
    FirstViolationPrefix,
}

/// Request to minimize one artifact or branch.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct MinimizationRequest {
    pub request_id: String,
    pub artifact_id: ArtifactId,
    pub branch_id: BranchId,
    pub strategy: MinimizationStrategy,
}

/// Stable minimization result for a failing run or branch.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MinimizationResult {
    pub request: MinimizationRequest,
    pub minimized_steps: u64,
    pub patch: ScenarioBranchPatch,
    pub retained_counterexample: Option<TheoremAwareCounterexample>,
    pub summary: String,
}

impl PartialEq for MinimizationResult {
    fn eq(&self, other: &Self) -> bool {
        self.request == other.request
            && self.minimized_steps == other.minimized_steps
            && self.retained_counterexample == other.retained_counterexample
            && self.summary == other.summary
    }
}

/// Extension slot for downstream overlays and panels.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum ViewerExtensionSlot {
    OverviewPanel,
    GraphAnnotation,
    TimeTravelPanel,
    InsightPanel,
}

/// Stable downstream overlay descriptor.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct ViewerExtensionDescriptor {
    pub id: String,
    pub title: String,
    pub slot: ViewerExtensionSlot,
    pub summary: String,
}

/// Stable downstream integration manifest for viewer extensions.
#[derive(Debug, Clone, Default, Serialize, Deserialize, PartialEq, Eq)]
pub struct ViewerExtensionManifest {
    pub descriptors: Vec<ViewerExtensionDescriptor>,
}

/// Stable application-service trait shared by UI and shell layers.
pub trait ViewerApplicationService {
    /// Execute one typed query.
    ///
    /// # Errors
    ///
    /// Returns `ViewerModelError` when the requested artifact, run, or branch does not
    /// exist, or when the query cannot be satisfied by the backing service.
    fn query(&self, query: ViewerQuery) -> Result<ViewerQueryResult, ViewerModelError>;

    /// Execute one typed command.
    ///
    /// # Errors
    ///
    /// Returns `ViewerModelError` when the target artifact, run, or branch does not
    /// exist, when imported artifacts fail validation, or when the command cannot be
    /// applied by the backing service.
    fn command(&mut self, command: ViewerCommand) -> Result<ViewerCommandResult, ViewerModelError>;
}

/// In-process application-service implementation used by tests and the first web shell.
#[derive(Default)]
pub struct InMemoryViewerService {
    artifacts: BTreeMap<ArtifactId, ViewerArtifactFile>,
    runs: BTreeMap<RunId, RunWorkspace>,
    sweeps: BTreeMap<String, DeterministicSweepReport>,
    suites: BTreeMap<String, ExperimentSuiteReport>,
    mocked_reruns: BTreeMap<(RunId, BranchId), Vec<EffectOverrideSpec>>,
    minimizations: BTreeMap<String, MinimizationResult>,
    extensions: ViewerExtensionManifest,
}

#[derive(Default)]
struct RunWorkspace {
    root_artifact_id: Option<ArtifactId>,
    branches: BTreeMap<BranchId, BranchWorkspace>,
}

struct BranchWorkspace {
    parent_branch_id: Option<BranchId>,
    from_step: u64,
    patches: Vec<ScenarioBranchPatch>,
    deleted: bool,
    rerun_requested: bool,
}

impl InMemoryViewerService {
    /// Build one empty in-process service.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    fn ensure_run_workspace(&mut self, run_id: &str) -> &mut RunWorkspace {
        self.runs.entry(run_id.to_string()).or_insert_with(|| {
            let mut workspace = RunWorkspace::default();
            workspace.branches.insert(
                "root".to_string(),
                BranchWorkspace {
                    parent_branch_id: None,
                    from_step: 0,
                    patches: Vec::new(),
                    deleted: false,
                    rerun_requested: false,
                },
            );
            workspace
        })
    }

    fn scenario_bundle_for_run(&self, run: &RunWorkspace) -> Option<&ScenarioBundleArtifact> {
        let artifact_id = run.root_artifact_id.as_ref()?;
        let artifact = self.artifacts.get(artifact_id)?;
        match &artifact.artifact {
            ViewerArtifact::ScenarioBundle(bundle) => Some(bundle.as_ref()),
            _ => None,
        }
    }

    fn scenario_bundle_for_artifact(
        &self,
        artifact_id: &str,
    ) -> Result<&ScenarioBundleArtifact, ViewerModelError> {
        let artifact =
            self.artifacts
                .get(artifact_id)
                .ok_or_else(|| ViewerModelError::NotFound {
                    kind: "artifact".to_string(),
                    id: artifact_id.to_string(),
                })?;
        match &artifact.artifact {
            ViewerArtifact::ScenarioBundle(bundle) => Ok(bundle.as_ref()),
            _ => Err(ViewerModelError::UnexpectedQueryShape {
                expected: "scenario_bundle".to_string(),
            }),
        }
    }

    fn semantic_comparison(
        &self,
        request: &SemanticComparisonRequest,
    ) -> Result<SemanticComparisonResult, ViewerModelError> {
        let baseline = self.scenario_bundle_for_artifact(&request.baseline_artifact_id)?;
        let candidate = self.scenario_bundle_for_artifact(&request.candidate_artifact_id)?;
        Ok(build_semantic_comparison_result(
            &request.baseline_artifact_id,
            &request.candidate_artifact_id,
            baseline,
            candidate,
        ))
    }

    fn comparison_counterexample(
        &self,
        request: &SemanticComparisonRequest,
    ) -> Result<TheoremAwareCounterexample, ViewerModelError> {
        let baseline = self.scenario_bundle_for_artifact(&request.baseline_artifact_id)?;
        let candidate = self.scenario_bundle_for_artifact(&request.candidate_artifact_id)?;
        Ok(build_comparison_counterexample(
            &request.baseline_artifact_id,
            &request.candidate_artifact_id,
            baseline,
            candidate,
        ))
    }

    fn artifact_counterexample(
        &self,
        artifact_id: &str,
    ) -> Result<TheoremAwareCounterexample, ViewerModelError> {
        let bundle = self.scenario_bundle_for_artifact(artifact_id)?;
        Ok(build_artifact_counterexample(bundle))
    }

    fn effect_trace_for_branch(
        &self,
        artifact_id: &str,
        branch_id: &str,
    ) -> Result<EffectTraceArtifact, ViewerModelError> {
        let bundle = self.scenario_bundle_for_artifact(artifact_id)?;
        Ok(EffectTraceArtifact {
            artifact_id: artifact_id.to_string(),
            branch_id: branch_id.to_string(),
            entries: build_effect_trace_entries(bundle),
            overrides: self
                .mocked_reruns
                .get(&(artifact_id.to_string(), branch_id.to_string()))
                .cloned()
                .unwrap_or_default(),
        })
    }

    fn sweep_explorer(
        &self,
        request: &SweepExplorerRequest,
    ) -> Result<SweepExplorerView, ViewerModelError> {
        let report =
            self.sweeps
                .get(&request.sweep_id)
                .ok_or_else(|| ViewerModelError::NotFound {
                    kind: "sweep".to_string(),
                    id: request.sweep_id.clone(),
                })?;
        let mut visible = report.cases.clone();
        if let Some(filter) = request.filter_text.as_ref() {
            let needle = filter.to_lowercase();
            visible.retain(|case| {
                case.case_id.to_lowercase().contains(&needle)
                    || case.artifact_id.to_lowercase().contains(&needle)
                    || case.parameters.iter().any(|(key, value)| {
                        key.to_lowercase().contains(&needle)
                            || value.to_lowercase().contains(&needle)
                    })
            });
        }
        if let Some(max_results) = request.max_results {
            visible.truncate(max_results);
        }
        let outlier_case_ids = report
            .cases
            .iter()
            .filter_map(|case| {
                case.comparison_to_baseline.as_ref().and_then(|comparison| {
                    (comparison.relation == SemanticComparisonClass::SafetyVisibleDivergence)
                        .then(|| case.case_id.clone())
                })
            })
            .collect();
        Ok(SweepExplorerView {
            sweep_id: request.sweep_id.clone(),
            total_cases: report.cases.len(),
            visible_cases: visible,
            outlier_case_ids,
        })
    }

    fn build_sweep_report(
        &self,
        sweep_id: String,
        baseline_artifact_id: Option<ArtifactId>,
        cases: Vec<SweepCaseSpec>,
    ) -> Result<DeterministicSweepReport, ViewerModelError> {
        let mut results = Vec::new();
        for case in cases {
            let bundle = self.scenario_bundle_for_artifact(&case.artifact_id)?;
            let comparison_to_baseline = if let Some(baseline_id) = baseline_artifact_id.as_ref() {
                Some(self.semantic_comparison(&SemanticComparisonRequest {
                    baseline_artifact_id: baseline_id.clone(),
                    candidate_artifact_id: case.artifact_id.clone(),
                })?)
            } else {
                None
            };
            results.push(SweepCaseResult {
                case_id: case.case_id,
                artifact_id: case.artifact_id,
                parameters: case.parameters,
                theorem_profile: Some(bundle.result.stats.theorem_profile.clone()),
                execution_regime: Some(bundle.result.stats.execution_regime),
                comparison_to_baseline,
            });
        }
        Ok(DeterministicSweepReport {
            sweep_id,
            baseline_artifact_id,
            cases: results,
        })
    }

    fn build_suite_report(
        &self,
        definition: ExperimentSuiteDefinition,
    ) -> Result<ExperimentSuiteReport, ViewerModelError> {
        let mut cases = Vec::new();
        for case in &definition.cases {
            let comparison = self.semantic_comparison(&SemanticComparisonRequest {
                baseline_artifact_id: case.baseline_artifact_id.clone(),
                candidate_artifact_id: case.candidate_artifact_id.clone(),
            })?;
            let changed_steps = comparison
                .first_divergence
                .as_ref()
                .and_then(|point| point.step);
            let threshold_passed = if comparison.relation
                == SemanticComparisonClass::EquivalentUnderNormalization
                && definition.threshold.allow_normalization_only
            {
                true
            } else {
                changed_steps.unwrap_or(0) <= definition.threshold.max_changed_steps
                    && comparison.relation != SemanticComparisonClass::SafetyVisibleDivergence
            };
            let counterexample = (!threshold_passed)
                .then(|| {
                    self.comparison_counterexample(&SemanticComparisonRequest {
                        baseline_artifact_id: case.baseline_artifact_id.clone(),
                        candidate_artifact_id: case.candidate_artifact_id.clone(),
                    })
                })
                .transpose()?;
            cases.push(ExperimentSuiteCaseResult {
                case_id: case.case_id.clone(),
                comparison,
                threshold_passed,
                counterexample,
            });
        }
        Ok(ExperimentSuiteReport { definition, cases })
    }

    fn build_minimization_result(
        &self,
        request: &MinimizationRequest,
    ) -> Result<MinimizationResult, ViewerModelError> {
        let bundle = self.scenario_bundle_for_artifact(&request.artifact_id)?;
        let retained_counterexample = self.artifact_counterexample(&request.artifact_id).ok();
        let minimized_steps = match request.strategy {
            MinimizationStrategy::FirstDivergencePrefix => retained_counterexample
                .as_ref()
                .and_then(|counterexample| counterexample.divergence.as_ref())
                .and_then(|point| point.step)
                .or_else(|| bundle.result.violations.first().map(|_| 1))
                .unwrap_or_else(|| bundle.result.stats.rounds_executed.max(1)),
            MinimizationStrategy::FirstViolationPrefix => 1,
        };
        let minimized_steps = minimized_steps.max(1);
        Ok(MinimizationResult {
            request: request.clone(),
            minimized_steps,
            patch: ScenarioBranchPatch {
                operations: vec![ScenarioPatchOperation::SetSteps {
                    steps: minimized_steps,
                }],
            },
            retained_counterexample,
            summary: format!(
                "minimized `{}` on branch `{}` to {} step(s)",
                request.artifact_id, request.branch_id, minimized_steps
            ),
        })
    }

    fn search_branch_matches(&self, matches: &mut Vec<SearchResult>, needle: &str) {
        for (run_id, run) in &self.runs {
            for (branch_id, branch) in &run.branches {
                if branch_id.to_lowercase().contains(needle) {
                    matches.push(SearchResult {
                        artifact_id: run
                            .root_artifact_id
                            .clone()
                            .unwrap_or_else(|| run_id.clone()),
                        domain: SearchDomain::Branch,
                        label: branch_id.clone(),
                        detail: format!("from step {}", branch.from_step),
                        branch_id: Some(branch_id.clone()),
                        step: Some(branch.from_step),
                    });
                }
            }
        }
    }

    fn scenario_bundle_artifact_ids(&self) -> Vec<ArtifactId> {
        self.artifacts
            .iter()
            .filter(|(_, artifact)| matches!(artifact.artifact, ViewerArtifact::ScenarioBundle(_)))
            .map(|(artifact_id, _)| artifact_id.clone())
            .collect()
    }

    fn search_divergence_matches(&self, matches: &mut Vec<SearchResult>, needle: &str) {
        let scenario_ids = self.scenario_bundle_artifact_ids();
        for pair in scenario_ids.windows(2) {
            if let [baseline_artifact_id, candidate_artifact_id] = pair {
                let request = SemanticComparisonRequest {
                    baseline_artifact_id: baseline_artifact_id.clone(),
                    candidate_artifact_id: candidate_artifact_id.clone(),
                };
                if let Ok(comparison) = self.semantic_comparison(&request) {
                    if let Some(point) = comparison.first_divergence {
                        let haystack = format!(
                            "{} {} {}",
                            comparison.summary, point.label, point.baseline_detail
                        )
                        .to_lowercase();
                        if haystack.contains(needle) {
                            matches.push(SearchResult {
                                artifact_id: candidate_artifact_id.clone(),
                                domain: SearchDomain::Divergence,
                                label: point.label,
                                detail: comparison.summary,
                                branch_id: Some("root".to_string()),
                                step: point.step,
                            });
                        }
                    }
                }
            }
        }
    }

    fn graph_projection_for_request(
        &self,
        run_id: &str,
        request: &GraphProjectionRequest,
        run: &RunWorkspace,
    ) -> GraphProjection {
        let step_limit = request.step;
        let bundle = self.scenario_bundle_for_run(run);
        let (nodes, edges) = match request.kind {
            GraphProjectionKind::BranchLineage => self.branch_lineage_projection(run),
            GraphProjectionKind::ChoreographyStructure => {
                self.choreography_projection(bundle, step_limit)
            }
            GraphProjectionKind::InstantiatedProtocol => {
                self.instantiated_protocol_projection(bundle, step_limit)
            }
            GraphProjectionKind::ExecutionTimeline => {
                self.execution_timeline_projection(bundle, step_limit)
            }
        };
        GraphProjection {
            run_id: run_id.to_string(),
            branch_id: request.branch_id.clone(),
            step: request.step,
            kind: request.kind,
            nodes,
            edges,
        }
    }

    fn branch_lineage_projection(&self, run: &RunWorkspace) -> (Vec<GraphNode>, Vec<GraphEdge>) {
        let nodes = run
            .branches
            .iter()
            .map(|(branch_id, branch)| GraphNode {
                id: branch_id.clone(),
                label: branch_id.clone(),
                category: if branch.deleted {
                    "branch_deleted".to_string()
                } else {
                    "branch".to_string()
                },
                step: Some(branch.from_step),
            })
            .collect::<Vec<_>>();
        let edges = run
            .branches
            .iter()
            .filter_map(|(branch_id, branch)| {
                branch.parent_branch_id.as_ref().map(|parent| GraphEdge {
                    from: parent.clone(),
                    to: branch_id.clone(),
                    label: "fork".to_string(),
                    step: Some(branch.from_step),
                })
            })
            .collect::<Vec<_>>();
        (nodes, edges)
    }

    fn choreography_projection(
        &self,
        bundle: Option<&ScenarioBundleArtifact>,
        step_limit: Option<u64>,
    ) -> (Vec<GraphNode>, Vec<GraphEdge>) {
        let Some(bundle) = bundle else {
            return (Vec::new(), Vec::new());
        };
        let roles = bundle
            .scenario
            .as_ref()
            .map(|scenario| scenario.roles.clone())
            .unwrap_or_else(|| bundle.trace_roles());
        let nodes = roles
            .iter()
            .map(|role| GraphNode {
                id: role.clone(),
                label: role.clone(),
                category: "role".to_string(),
                step: step_limit,
            })
            .collect::<Vec<_>>();
        let mut edges = Vec::new();
        for pair in roles.windows(2) {
            if let [from, to] = pair {
                edges.push(GraphEdge {
                    from: from.clone(),
                    to: to.clone(),
                    label: "flow".to_string(),
                    step: step_limit,
                });
            }
        }
        (nodes, edges)
    }

    fn instantiated_protocol_projection(
        &self,
        bundle: Option<&ScenarioBundleArtifact>,
        step_limit: Option<u64>,
    ) -> (Vec<GraphNode>, Vec<GraphEdge>) {
        let Some(bundle) = bundle else {
            return (Vec::new(), Vec::new());
        };
        let records = bundle
            .result
            .trace
            .records
            .iter()
            .filter(|record| step_limit.map_or(true, |limit| record.step <= limit))
            .collect::<Vec<_>>();
        let nodes = records
            .iter()
            .map(|record| GraphNode {
                id: format!("{}@{}", record.role, record.step),
                label: format!("{} @ {}", record.role, record.step),
                category: "session_step".to_string(),
                step: Some(record.step),
            })
            .collect::<Vec<_>>();
        let edges = records
            .windows(2)
            .map(|window| GraphEdge {
                from: format!("{}@{}", window[0].role, window[0].step),
                to: format!("{}@{}", window[1].role, window[1].step),
                label: "continuation".to_string(),
                step: Some(window[1].step),
            })
            .collect::<Vec<_>>();
        (nodes, edges)
    }

    fn execution_timeline_projection(
        &self,
        bundle: Option<&ScenarioBundleArtifact>,
        step_limit: Option<u64>,
    ) -> (Vec<GraphNode>, Vec<GraphEdge>) {
        let Some(bundle) = bundle else {
            return (Vec::new(), Vec::new());
        };
        let records = bundle
            .result
            .trace
            .records
            .iter()
            .filter(|record| step_limit.map_or(true, |limit| record.step <= limit))
            .collect::<Vec<_>>();
        let nodes = records
            .iter()
            .map(|record| GraphNode {
                id: format!("step-{}", record.step),
                label: format!("step {} ({})", record.step, record.role),
                category: "timeline_step".to_string(),
                step: Some(record.step),
            })
            .collect::<Vec<_>>();
        let edges = records
            .windows(2)
            .map(|window| GraphEdge {
                from: format!("step-{}", window[0].step),
                to: format!("step-{}", window[1].step),
                label: window[1].role.clone(),
                step: Some(window[1].step),
            })
            .collect::<Vec<_>>();
        (nodes, edges)
    }

    fn artifact_inventory(&self) -> Vec<ArtifactInventoryEntry> {
        self.artifacts
            .iter()
            .map(|(artifact_id, artifact)| ArtifactInventoryEntry {
                artifact_id: artifact_id.clone(),
                kind: artifact.kind(),
                label: format!("{artifact_id}: {:?}", artifact.kind()),
            })
            .collect()
    }

    fn load_artifact(&self, artifact_id: &str) -> Result<ViewerQueryResult, ViewerModelError> {
        let artifact =
            self.artifacts
                .get(artifact_id)
                .cloned()
                .ok_or_else(|| ViewerModelError::NotFound {
                    kind: "artifact".to_string(),
                    id: artifact_id.to_string(),
                })?;
        Ok(ViewerQueryResult::ArtifactFile {
            artifact: Box::new(artifact),
        })
    }

    fn scenario_summary(
        &self,
        artifact_id: ArtifactId,
    ) -> Result<ViewerQueryResult, ViewerModelError> {
        let Some(ViewerArtifact::ScenarioBundle(bundle)) =
            self.artifacts.get(&artifact_id).map(|file| &file.artifact)
        else {
            return Err(ViewerModelError::NotFound {
                kind: "scenario_bundle".to_string(),
                id: artifact_id,
            });
        };
        Ok(ViewerQueryResult::ScenarioSummary {
            summary: bundle.summary(),
        })
    }

    fn branch_lineage(&self, run_id: RunId) -> Result<ViewerQueryResult, ViewerModelError> {
        let run = self
            .runs
            .get(&run_id)
            .ok_or_else(|| ViewerModelError::NotFound {
                kind: "run".to_string(),
                id: run_id.clone(),
            })?;
        Ok(ViewerQueryResult::BranchLineage {
            lineage: BranchLineageProjection {
                run_id,
                branches: run
                    .branches
                    .iter()
                    .map(|(branch_id, branch)| BranchLineageNode {
                        branch_id: branch_id.clone(),
                        parent_branch_id: branch.parent_branch_id.clone(),
                        from_step: branch.from_step,
                        deleted: branch.deleted,
                        rerun_requested: branch.rerun_requested,
                        patch_count: u64::try_from(branch.patches.len()).unwrap_or(u64::MAX),
                    })
                    .collect(),
            },
        })
    }

    fn graph_projection(
        &self,
        request: GraphProjectionRequest,
    ) -> Result<ViewerQueryResult, ViewerModelError> {
        let run = self
            .runs
            .get(&request.run_id)
            .ok_or_else(|| ViewerModelError::NotFound {
                kind: "run".to_string(),
                id: request.run_id.clone(),
            })?;
        if !run.branches.contains_key(&request.branch_id) {
            return Err(ViewerModelError::NotFound {
                kind: "branch".to_string(),
                id: request.branch_id,
            });
        }
        Ok(ViewerQueryResult::GraphProjection {
            projection: self.graph_projection_for_request(&request.run_id, &request, run),
        })
    }

    fn import_artifact_command(
        &mut self,
        artifact_id: ArtifactId,
        artifact: &ViewerArtifactFile,
    ) -> Result<ViewerCommandResult, ViewerModelError> {
        artifact.validate()?;
        self.artifacts.insert(artifact_id.clone(), artifact.clone());
        if matches!(artifact.artifact, ViewerArtifact::ScenarioBundle(_)) {
            let workspace = self.ensure_run_workspace(&artifact_id);
            workspace.root_artifact_id = Some(artifact_id.clone());
        }
        Ok(ViewerCommandResult::ArtifactImported { artifact_id })
    }

    fn create_branch_command(
        &mut self,
        run_id: RunId,
        branch_id: BranchId,
        parent_branch_id: BranchId,
        from_step: u64,
        patch: ScenarioBranchPatch,
    ) -> Result<ViewerCommandResult, ViewerModelError> {
        let run = self.ensure_run_workspace(&run_id);
        if !run.branches.contains_key(&parent_branch_id) {
            return Err(ViewerModelError::NotFound {
                kind: "parent_branch".to_string(),
                id: parent_branch_id,
            });
        }
        run.branches.insert(
            branch_id.clone(),
            BranchWorkspace {
                parent_branch_id: Some(parent_branch_id),
                from_step,
                patches: vec![patch],
                deleted: false,
                rerun_requested: false,
            },
        );
        Ok(ViewerCommandResult::BranchCreated { run_id, branch_id })
    }

    fn update_branch_command(
        &mut self,
        run_id: RunId,
        branch_id: BranchId,
        patch: ScenarioBranchPatch,
    ) -> Result<ViewerCommandResult, ViewerModelError> {
        let run = self
            .runs
            .get_mut(&run_id)
            .ok_or_else(|| ViewerModelError::NotFound {
                kind: "run".to_string(),
                id: run_id.clone(),
            })?;
        let branch =
            run.branches
                .get_mut(&branch_id)
                .ok_or_else(|| ViewerModelError::NotFound {
                    kind: "branch".to_string(),
                    id: branch_id.clone(),
                })?;
        branch.patches.push(patch);
        Ok(ViewerCommandResult::BranchUpdated { run_id, branch_id })
    }

    fn mark_branch_deleted(
        &mut self,
        run_id: RunId,
        branch_id: BranchId,
    ) -> Result<ViewerCommandResult, ViewerModelError> {
        let run = self
            .runs
            .get_mut(&run_id)
            .ok_or_else(|| ViewerModelError::NotFound {
                kind: "run".to_string(),
                id: run_id.clone(),
            })?;
        let branch =
            run.branches
                .get_mut(&branch_id)
                .ok_or_else(|| ViewerModelError::NotFound {
                    kind: "branch".to_string(),
                    id: branch_id.clone(),
                })?;
        branch.deleted = true;
        Ok(ViewerCommandResult::BranchDeleted { run_id, branch_id })
    }

    fn mark_rerun_requested(
        &mut self,
        run_id: RunId,
        branch_id: BranchId,
    ) -> Result<ViewerCommandResult, ViewerModelError> {
        let run = self
            .runs
            .get_mut(&run_id)
            .ok_or_else(|| ViewerModelError::NotFound {
                kind: "run".to_string(),
                id: run_id.clone(),
            })?;
        let branch =
            run.branches
                .get_mut(&branch_id)
                .ok_or_else(|| ViewerModelError::NotFound {
                    kind: "branch".to_string(),
                    id: branch_id.clone(),
                })?;
        branch.rerun_requested = true;
        Ok(ViewerCommandResult::RerunRequested { run_id, branch_id })
    }

    fn search(&self, query: &SearchQuery) -> Result<ViewerQueryResult, ViewerModelError> {
        let needle = query.text.to_lowercase();
        let mut matches = Vec::new();
        for (artifact_id, artifact) in &self.artifacts {
            self.search_artifact_inventory_matches(
                &mut matches,
                artifact_id,
                artifact,
                &needle,
                query.domain,
            );
            if let ViewerArtifact::ScenarioBundle(bundle) = &artifact.artifact {
                self.search_bundle_matches(
                    &mut matches,
                    artifact_id,
                    bundle,
                    &needle,
                    query.domain,
                );
            }
        }
        if query.domain.is_none() || query.domain == Some(SearchDomain::Branch) {
            self.search_branch_matches(&mut matches, &needle);
        }
        if query.domain.is_none() || query.domain == Some(SearchDomain::Divergence) {
            self.search_divergence_matches(&mut matches, &needle);
        }
        if query.domain.is_none() || query.domain == Some(SearchDomain::Sweep) {
            for report in self.sweeps.values() {
                for case in &report.cases {
                    if case.case_id.to_lowercase().contains(&needle) {
                        matches.push(SearchResult {
                            artifact_id: case.artifact_id.clone(),
                            domain: SearchDomain::Sweep,
                            label: case.case_id.clone(),
                            detail: report.sweep_id.clone(),
                            branch_id: Some("root".to_string()),
                            step: None,
                        });
                    }
                }
            }
        }
        if query.domain.is_none() || query.domain == Some(SearchDomain::Effect) {
            for artifact_id in self.artifacts.keys() {
                if let Ok(effect_trace) = self.effect_trace_for_branch(artifact_id, "root") {
                    for entry in effect_trace.entries {
                        let haystack = format!("{} {}", entry.kind, entry.detail).to_lowercase();
                        if haystack.contains(&needle) {
                            matches.push(SearchResult {
                                artifact_id: artifact_id.clone(),
                                domain: SearchDomain::Effect,
                                label: entry.kind,
                                detail: entry.detail,
                                branch_id: Some("root".to_string()),
                                step: Some(entry.step),
                            });
                        }
                    }
                }
            }
        }
        Ok(ViewerQueryResult::SearchResults { matches })
    }

    fn search_artifact_inventory_matches(
        &self,
        matches: &mut Vec<SearchResult>,
        artifact_id: &str,
        artifact: &ViewerArtifactFile,
        needle: &str,
        domain: Option<SearchDomain>,
    ) {
        let kind_match = format!("{:?}", artifact.kind()).to_lowercase();
        if (domain.is_none() || domain == Some(SearchDomain::Artifact))
            && (artifact_id.to_lowercase().contains(needle) || kind_match.contains(needle))
        {
            matches.push(SearchResult {
                artifact_id: artifact_id.to_string(),
                domain: SearchDomain::Artifact,
                label: artifact_id.to_string(),
                detail: format!("{:?}", artifact.kind()),
                branch_id: None,
                step: None,
            });
        }
    }

    fn search_bundle_matches(
        &self,
        matches: &mut Vec<SearchResult>,
        artifact_id: &str,
        bundle: &ScenarioBundleArtifact,
        needle: &str,
        domain: Option<SearchDomain>,
    ) {
        if domain.is_none() || domain == Some(SearchDomain::Role) {
            for role in bundle
                .trace_roles()
                .into_iter()
                .filter(|role| role.to_lowercase().contains(needle))
            {
                matches.push(SearchResult {
                    artifact_id: artifact_id.to_string(),
                    domain: SearchDomain::Role,
                    label: role.clone(),
                    detail: "trace role".to_string(),
                    branch_id: Some("root".to_string()),
                    step: None,
                });
            }
        }
        if domain.is_none() || domain == Some(SearchDomain::Step) {
            for record in &bundle.result.trace.records {
                if record.role.to_lowercase().contains(needle) {
                    matches.push(SearchResult {
                        artifact_id: artifact_id.to_string(),
                        domain: SearchDomain::Step,
                        label: format!("step {}", record.step),
                        detail: record.role.clone(),
                        branch_id: Some("root".to_string()),
                        step: Some(record.step),
                    });
                }
            }
        }
    }
}

impl ViewerApplicationService for InMemoryViewerService {
    fn query(&self, query: ViewerQuery) -> Result<ViewerQueryResult, ViewerModelError> {
        match query {
            ViewerQuery::ListArtifacts => Ok(ViewerQueryResult::ArtifactInventory {
                artifacts: self.artifact_inventory(),
            }),
            ViewerQuery::LoadArtifact { artifact_id } => self.load_artifact(&artifact_id),
            ViewerQuery::ScenarioSummary { artifact_id } => self.scenario_summary(artifact_id),
            ViewerQuery::BranchLineage { run_id } => self.branch_lineage(run_id),
            ViewerQuery::GraphProjection(request) => self.graph_projection(request),
            ViewerQuery::Search(query) => self.search(&query),
            ViewerQuery::HistoricalInspection(state) => {
                Ok(ViewerQueryResult::HistoricalInspection { state })
            }
            ViewerQuery::SemanticComparison(request) => {
                let comparison = self.semantic_comparison(&request)?;
                Ok(ViewerQueryResult::SemanticComparison {
                    comparison: Box::new(comparison),
                })
            }
            ViewerQuery::FirstDivergence(request) => {
                let divergence = self.semantic_comparison(&request)?.first_divergence;
                Ok(ViewerQueryResult::FirstDivergence { divergence })
            }
            ViewerQuery::ComparisonCounterexample(request) => {
                let counterexample = self.comparison_counterexample(&request)?;
                Ok(ViewerQueryResult::Counterexample {
                    counterexample: Box::new(counterexample),
                })
            }
            ViewerQuery::ArtifactCounterexample { artifact_id } => {
                let counterexample = self.artifact_counterexample(&artifact_id)?;
                Ok(ViewerQueryResult::Counterexample {
                    counterexample: Box::new(counterexample),
                })
            }
            ViewerQuery::SweepExplorer(request) => {
                let explorer = self.sweep_explorer(&request)?;
                Ok(ViewerQueryResult::SweepExplorer {
                    explorer: Box::new(explorer),
                })
            }
            ViewerQuery::ExperimentSuite { suite_id } => {
                let suite = self.suites.get(&suite_id).cloned().ok_or_else(|| {
                    ViewerModelError::NotFound {
                        kind: "suite".to_string(),
                        id: suite_id.clone(),
                    }
                })?;
                Ok(ViewerQueryResult::ExperimentSuite {
                    suite: Box::new(suite),
                })
            }
            ViewerQuery::EffectTrace {
                artifact_id,
                branch_id,
            } => {
                let effect_trace = self.effect_trace_for_branch(&artifact_id, &branch_id)?;
                Ok(ViewerQueryResult::EffectTrace {
                    effect_trace: Box::new(effect_trace),
                })
            }
            ViewerQuery::Minimization { request_id } => {
                let result = self
                    .minimizations
                    .get(&request_id)
                    .cloned()
                    .ok_or_else(|| ViewerModelError::NotFound {
                        kind: "minimization".to_string(),
                        id: request_id.clone(),
                    })?;
                Ok(ViewerQueryResult::Minimization {
                    result: Box::new(result),
                })
            }
            ViewerQuery::ExtensionManifest => Ok(ViewerQueryResult::ExtensionManifest {
                manifest: Box::new(self.extensions.clone()),
            }),
        }
    }

    fn command(&mut self, command: ViewerCommand) -> Result<ViewerCommandResult, ViewerModelError> {
        match command {
            ViewerCommand::ImportArtifact {
                artifact_id,
                artifact,
            } => self.import_artifact_command(artifact_id, &artifact),
            ViewerCommand::CreateBranch {
                run_id,
                branch_id,
                parent_branch_id,
                from_step,
                patch,
            } => self.create_branch_command(run_id, branch_id, parent_branch_id, from_step, patch),
            ViewerCommand::UpdateBranch {
                run_id,
                branch_id,
                patch,
            } => self.update_branch_command(run_id, branch_id, patch),
            ViewerCommand::DeleteBranch { run_id, branch_id } => {
                self.mark_branch_deleted(run_id, branch_id)
            }
            ViewerCommand::RequestRerun { run_id, branch_id } => {
                self.mark_rerun_requested(run_id, branch_id)
            }
            ViewerCommand::ExecuteSweep {
                sweep_id,
                baseline_artifact_id,
                cases,
            } => {
                let report =
                    self.build_sweep_report(sweep_id.clone(), baseline_artifact_id.clone(), cases)?;
                self.sweeps.insert(sweep_id.clone(), report);
                Ok(ViewerCommandResult::SweepExecuted { sweep_id })
            }
            ViewerCommand::ExecuteExperimentSuite { definition } => {
                let suite_id = definition.suite_id.clone();
                let report = self.build_suite_report(definition)?;
                self.suites.insert(suite_id.clone(), report);
                Ok(ViewerCommandResult::ExperimentSuiteExecuted { suite_id })
            }
            ViewerCommand::RequestMockedRerun {
                run_id,
                branch_id,
                overrides,
            } => {
                self.mocked_reruns
                    .insert((run_id.clone(), branch_id.clone()), overrides);
                Ok(ViewerCommandResult::MockedRerunRequested { run_id, branch_id })
            }
            ViewerCommand::RequestMinimization { request } => {
                let request_id = request.request_id.clone();
                let result = self.build_minimization_result(&request)?;
                self.minimizations.insert(request_id.clone(), result);
                Ok(ViewerCommandResult::MinimizationRequested { request_id })
            }
            ViewerCommand::RegisterExtensions { manifest } => {
                let count = manifest.descriptors.len();
                self.extensions = manifest;
                Ok(ViewerCommandResult::ExtensionsRegistered { count })
            }
        }
    }
}

fn effect_trace_entry_detail(value: &impl Serialize) -> String {
    serde_json::to_string(value).unwrap_or_else(|_| "\"unserializable\"".to_string())
}

fn build_effect_trace_entries(bundle: &ScenarioBundleArtifact) -> Vec<EffectTraceEntry> {
    let mut entries = Vec::new();
    for (index, exchange) in bundle.result.replay.effect_exchanges.iter().enumerate() {
        entries.push(EffectTraceEntry {
            step: u64::try_from(index).unwrap_or(u64::MAX),
            kind: "effect_exchange".to_string(),
            detail: effect_trace_entry_detail(exchange),
        });
    }
    for (index, trace) in bundle.result.replay.effect_trace.iter().enumerate() {
        entries.push(EffectTraceEntry {
            step: u64::try_from(index).unwrap_or(u64::MAX),
            kind: "effect_trace".to_string(),
            detail: effect_trace_entry_detail(trace),
        });
    }
    if entries.is_empty() {
        entries.push(EffectTraceEntry {
            step: 0,
            kind: "no_effects_recorded".to_string(),
            detail: "run emitted no effect traffic".to_string(),
        });
    }
    entries
}

fn first_trace_divergence(
    baseline: &ScenarioBundleArtifact,
    candidate: &ScenarioBundleArtifact,
) -> Option<SemanticDivergencePoint> {
    let left = &baseline.result.trace.records;
    let right = &candidate.result.trace.records;
    let common_len = left.len().min(right.len());
    for index in 0..common_len {
        if left[index] != right[index] {
            return Some(SemanticDivergencePoint {
                kind: SemanticDivergenceKind::TraceRecord,
                step: Some(left[index].step.min(right[index].step)),
                label: "trace record mismatch".to_string(),
                baseline_detail: format!("{:?}", left[index]),
                candidate_detail: format!("{:?}", right[index]),
            });
        }
    }
    if left.len() != right.len() {
        return Some(SemanticDivergencePoint {
            kind: SemanticDivergenceKind::StepCount,
            step: Some(u64::try_from(common_len).unwrap_or(u64::MAX)),
            label: "trace length mismatch".to_string(),
            baseline_detail: left.len().to_string(),
            candidate_detail: right.len().to_string(),
        });
    }
    if baseline.result.replay.reconfiguration_trace != candidate.result.replay.reconfiguration_trace
    {
        return Some(SemanticDivergencePoint {
            kind: SemanticDivergenceKind::Reconfiguration,
            step: baseline
                .result
                .replay
                .reconfiguration_trace
                .first()
                .map(|record| record.logical_step)
                .or_else(|| {
                    candidate
                        .result
                        .replay
                        .reconfiguration_trace
                        .first()
                        .map(|record| record.logical_step)
                }),
            label: "reconfiguration mismatch".to_string(),
            baseline_detail: format!("{:?}", baseline.result.replay.reconfiguration_trace),
            candidate_detail: format!("{:?}", candidate.result.replay.reconfiguration_trace),
        });
    }
    if baseline.result.replay.effect_trace != candidate.result.replay.effect_trace {
        return Some(SemanticDivergencePoint {
            kind: SemanticDivergenceKind::EffectTrace,
            step: Some(0),
            label: "effect trace mismatch".to_string(),
            baseline_detail: effect_trace_entry_detail(&baseline.result.replay.effect_trace),
            candidate_detail: effect_trace_entry_detail(&candidate.result.replay.effect_trace),
        });
    }
    if baseline.result.stats.execution_regime != candidate.result.stats.execution_regime {
        return Some(SemanticDivergencePoint {
            kind: SemanticDivergenceKind::ExecutionRegime,
            step: None,
            label: "execution regime mismatch".to_string(),
            baseline_detail: format!("{:?}", baseline.result.stats.execution_regime),
            candidate_detail: format!("{:?}", candidate.result.stats.execution_regime),
        });
    }
    if baseline.result.stats.theorem_profile != candidate.result.stats.theorem_profile {
        return Some(SemanticDivergencePoint {
            kind: SemanticDivergenceKind::TheoremProfile,
            step: None,
            label: "theorem profile mismatch".to_string(),
            baseline_detail: format!("{:?}", baseline.result.stats.theorem_profile),
            candidate_detail: format!("{:?}", candidate.result.stats.theorem_profile),
        });
    }
    None
}

#[authoritative_source("viewer_semantic_comparison")]
fn build_semantic_comparison_result(
    baseline_artifact_id: &str,
    candidate_artifact_id: &str,
    baseline: &ScenarioBundleArtifact,
    candidate: &ScenarioBundleArtifact,
) -> SemanticComparisonResult {
    let normalized_observability = compare_observability(
        &baseline.result.replay.obs_trace,
        &baseline.result.replay.reconfiguration_trace,
        &baseline.result.analysis.normalized_observability,
        &candidate.result.replay.obs_trace,
        &candidate.result.replay.reconfiguration_trace,
        &candidate.result.analysis.normalized_observability,
    );
    let first_divergence = first_trace_divergence(baseline, candidate);
    let classification_changed_only = matches!(
        first_divergence.as_ref().map(|point| point.kind),
        Some(SemanticDivergenceKind::TheoremProfile | SemanticDivergenceKind::ExecutionRegime)
    ) && normalized_observability.relation
        == ObservabilityRelation::ExactRawMatch;
    let mut relation = match normalized_observability.relation {
        ObservabilityRelation::ExactRawMatch => SemanticComparisonClass::ExactMatch,
        ObservabilityRelation::EquivalentUnderNormalization => {
            SemanticComparisonClass::EquivalentUnderNormalization
        }
        ObservabilityRelation::SafetyVisibleDivergence => {
            SemanticComparisonClass::SafetyVisibleDivergence
        }
    };
    if first_divergence.is_some() && !classification_changed_only {
        relation = SemanticComparisonClass::SafetyVisibleDivergence;
    }
    let summary = if classification_changed_only {
        "runtime artifacts match exactly but theorem/regime classification changed".to_string()
    } else {
        match relation {
            SemanticComparisonClass::ExactMatch => "artifacts match exactly".to_string(),
            SemanticComparisonClass::EquivalentUnderNormalization => {
                "raw traces differ but normalized observability matches".to_string()
            }
            SemanticComparisonClass::SafetyVisibleDivergence => {
                "safety-visible divergence detected".to_string()
            }
        }
    };
    SemanticComparisonResult {
        baseline_artifact_id: baseline_artifact_id.to_string(),
        candidate_artifact_id: candidate_artifact_id.to_string(),
        relation,
        normalized_observability,
        classification_changed_only,
        first_divergence,
        summary,
    }
}

#[authoritative_source("viewer_comparison_counterexample")]
fn build_comparison_counterexample(
    baseline_artifact_id: &str,
    candidate_artifact_id: &str,
    baseline: &ScenarioBundleArtifact,
    candidate: &ScenarioBundleArtifact,
) -> TheoremAwareCounterexample {
    let comparison = build_semantic_comparison_result(
        baseline_artifact_id,
        candidate_artifact_id,
        baseline,
        candidate,
    );
    let first_failed_assumption = if comparison.classification_changed_only {
        Some("theorem_profile_or_execution_regime_changed".to_string())
    } else if comparison.relation == SemanticComparisonClass::EquivalentUnderNormalization {
        Some("raw_trace_exactness_not_preserved".to_string())
    } else if comparison.relation == SemanticComparisonClass::SafetyVisibleDivergence {
        Some("normalized_equivalence_failed".to_string())
    } else {
        None
    };
    TheoremAwareCounterexample {
        summary: format!(
            "comparison between `{baseline_artifact_id}` and `{candidate_artifact_id}` failed semantic equivalence expectations"
        ),
        theorem_profile: Some(candidate.result.stats.theorem_profile.clone()),
        execution_regime: Some(candidate.result.stats.execution_regime),
        first_failed_assumption,
        divergence: comparison.first_divergence,
        decision_report: None,
    }
}

#[authoritative_source("viewer_artifact_counterexample")]
fn build_artifact_counterexample(bundle: &ScenarioBundleArtifact) -> TheoremAwareCounterexample {
    let decision_report = bundle
        .scenario
        .as_ref()
        .map(decide_theorem_eligibility)
        .or({
            Some(DecisionReport {
                kind: DecisionKind::TheoremEligibility,
                outcome: DecisionOutcome::Certified(
                    telltale_simulator::decision::DecisionCertificate::TheoremEligibility {
                        eligibility: bundle.result.stats.theorem_profile.eligibility,
                    },
                ),
            })
        });
    let first_failed_assumption =
        decision_report
            .as_ref()
            .and_then(|report| match &report.outcome {
                DecisionOutcome::Counterexample(DecisionCounterexample::TheoremEligibility {
                    cause,
                }) => Some(format!("{cause:?}")),
                _ => None,
            });
    TheoremAwareCounterexample {
        summary: if let Some(reason) = bundle
            .result
            .stats
            .theorem_profile
            .eligibility_reason
            .clone()
        {
            reason
        } else {
            "artifact has no failing theorem-side decision".to_string()
        },
        theorem_profile: Some(bundle.result.stats.theorem_profile.clone()),
        execution_regime: Some(bundle.result.stats.execution_regime),
        first_failed_assumption,
        divergence: None,
        decision_report,
    }
}

impl ScenarioBundleArtifact {
    fn trace_roles(&self) -> Vec<String> {
        let mut roles = self
            .result
            .trace
            .records
            .iter()
            .map(|record| record.role.clone())
            .collect::<Vec<_>>();
        roles.sort();
        roles.dedup();
        roles
    }
}

/// Errors surfaced by the pure model/service layer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ViewerModelError {
    Io { path: String, message: String },
    InvalidArtifactFile { message: String },
    UnsupportedSchemaVersion { supported: u32, found: u32 },
    NotFound { kind: String, id: String },
    Serialization { message: String },
    UnexpectedQueryShape { expected: String },
}

impl fmt::Display for ViewerModelError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io { path, message } => write!(f, "io error for {path}: {message}"),
            Self::InvalidArtifactFile { message } => write!(f, "{message}"),
            Self::UnsupportedSchemaVersion { supported, found } => write!(
                f,
                "unsupported artifact schema version {found}; expected {supported}"
            ),
            Self::NotFound { kind, id } => write!(f, "missing {kind} `{id}`"),
            Self::Serialization { message } => write!(f, "serialization error: {message}"),
            Self::UnexpectedQueryShape { expected } => {
                write!(
                    f,
                    "application service returned an unexpected query result; expected {expected}"
                )
            }
        }
    }
}

impl std::error::Error for ViewerModelError {}

#[cfg(test)]
mod tests {
    use super::*;
    use telltale_simulator::analysis::NormalizedObservability;
    use telltale_simulator::runner::{
        CriticalCapacityPhase, CriticalCapacitySummary, SchedulerBoundMode,
        SchedulerEnvelopeStatus, SchedulerFairnessRequirement, SchedulerProfileSummary,
        TheoremProgressSummary,
    };
    use telltale_simulator::scenario::{
        ExecutionRegime, ResolvedExecutionBackend, ResolvedSchedulerPolicy,
        TheoremAssumptionBundle, TheoremEligibility, TheoremEnvelopeProfile,
        TheoremSchedulerProfile,
    };
    use tempfile::NamedTempFile;

    fn sample_result() -> ScenarioResult {
        ScenarioResult {
            trace: Trace::default(),
            violations: Vec::new(),
            replay: ScenarioReplayArtifact {
                theorem_profile: ResolvedTheoremProfile {
                    scheduler_profile: TheoremSchedulerProfile::CanonicalExact,
                    envelope_profile: TheoremEnvelopeProfile::Exact,
                    assumption_bundle: TheoremAssumptionBundle::FaultFreeTransport,
                    eligibility: TheoremEligibility::Exact,
                    eligibility_reason: None,
                },
                adversary_schedule: Vec::new(),
                adversary_budget_history: Vec::new(),
                assumption_diagnostics: Vec::new(),
                obs_trace: Vec::new(),
                effect_trace: Vec::new(),
                effect_exchanges: Vec::new(),
                output_condition_trace: Vec::new(),
                semantic_audit_log: Vec::new(),
                semantic_objects: telltale_machine::ProtocolMachineSemanticObjects::default(),
                reconfiguration_trace: Vec::new(),
                environment_trace: EnvironmentTrace::default(),
                checkpoints: Vec::new(),
            },
            analysis: ScenarioAnalysisArtifact {
                normalized_observability: NormalizedObservability {
                    schema_version:
                        telltale_simulator::analysis::NORMALIZED_OBSERVABILITY_SCHEMA_VERSION,
                    raw_observable_event_count: 0,
                    raw_reconfiguration_count: 0,
                    normalized_event_class: Vec::new(),
                    normalized_reconfiguration_class: Vec::new(),
                },
            },
            stats: ScenarioStats {
                seed: 7,
                execution_regime: ExecutionRegime::CanonicalExact,
                theorem_profile: ResolvedTheoremProfile {
                    scheduler_profile: TheoremSchedulerProfile::CanonicalExact,
                    envelope_profile: TheoremEnvelopeProfile::Exact,
                    assumption_bundle: TheoremAssumptionBundle::FaultFreeTransport,
                    eligibility: TheoremEligibility::Exact,
                    eligibility_reason: None,
                },
                theorem_progress: TheoremProgressSummary {
                    initial_weighted_measure: 0,
                    initial_depth_budget: 0,
                    productive_step_count: 0,
                    remaining_weighted_measure: 0,
                    weighted_measure_consumed: 0,
                    critical_capacity: CriticalCapacitySummary {
                        threshold: None,
                        phase: CriticalCapacityPhase::Unsupported,
                    },
                },
                scheduler_profile: SchedulerProfileSummary {
                    implementation_policy: ResolvedSchedulerPolicy::Cooperative,
                    theorem_profile: TheoremSchedulerProfile::CanonicalExact,
                    productive_exactness: true,
                    total_step_mode: SchedulerBoundMode::ProductiveExactOnly,
                    total_step_upper_bound: None,
                    fairness_requirement: SchedulerFairnessRequirement::ExplicitYieldFairness,
                    envelope_status: SchedulerEnvelopeStatus::Exact,
                },
                reconfiguration_summary:
                    telltale_simulator::reconfiguration::ReconfigurationSummary::default(),
                environment_trace: EnvironmentTrace::default(),
                adversary_summary: telltale_simulator::fault::AdversarySummary::default(),
                assumption_diagnostics: Vec::new(),
                backend: ResolvedExecutionBackend::Canonical,
                scheduler_concurrency: 1,
                worker_threads: 1,
                rounds_executed: 0,
                final_tick: 0,
                total_obs_events: 0,
                total_invoked_events: 0,
                checkpoint_writes: 0,
                checkpoint_error: None,
                durable_recovery: None,
            },
        }
    }

    #[test]
    fn viewer_artifact_file_round_trips_and_validates_version() {
        let artifact = ViewerArtifactFile::new(ViewerArtifact::ScenarioBundle(Box::new(
            ScenarioBundleArtifact::new(None, sample_result(), None),
        )));
        let file = NamedTempFile::new().expect("temp file");
        artifact.write_json(file.path()).expect("write artifact");
        let loaded = ViewerArtifactFile::load_json(file.path()).expect("load artifact");
        assert_eq!(loaded.kind(), ViewerArtifactKind::ScenarioBundle);
        assert_eq!(loaded.schema_version, artifact.schema_version);
        assert_eq!(loaded.format, artifact.format);
    }

    #[test]
    fn durable_inspection_artifact_round_trips_through_viewer_surface() {
        let artifact = ViewerArtifactFile::new(ViewerArtifact::DurableInspection(Box::new(
            DurableInspectionReport {
                wal_entries: vec![telltale_simulator::durability::DurableWalEntryProjection {
                    tick: 4,
                    operation_id: "op#durable".to_string(),
                    kind: telltale_simulator::durability::DurableWalEntryKind::Escalation,
                    detail: "provisional -> soft_safe evidence=e#1".to_string(),
                }],
                evidence_cache_entries: vec![
                    telltale_simulator::durability::EvidenceCacheEntryProjection {
                        evidence_id: "e#1".to_string(),
                        interface_name: "Storage".to_string(),
                        operation_name: "commit".to_string(),
                        outcome_status: "success".to_string(),
                    },
                ],
                recovery: None,
            },
        )));
        let file = NamedTempFile::new().expect("temp file");
        artifact.write_json(file.path()).expect("write artifact");
        let loaded = ViewerArtifactFile::load_json(file.path()).expect("load artifact");
        assert_eq!(loaded.kind(), ViewerArtifactKind::DurableInspection);
        match loaded.artifact {
            ViewerArtifact::DurableInspection(report) => {
                assert_eq!(report.wal_entries.len(), 1);
                assert_eq!(report.evidence_cache_entries.len(), 1);
                assert_eq!(report.wal_entries[0].operation_id, "op#durable");
            }
            other => panic!("unexpected artifact kind: {other:?}"),
        }
    }

    #[test]
    fn durable_inspection_artifact_supports_non_empty_recovery_summaries() {
        let recovery: telltale_simulator::runner::DurableResumeSummary =
            serde_json::from_value(serde_json::json!({
                "execution_regime": "canonical_exact",
                "theorem_profile": {
                    "scheduler_profile": "canonical_exact",
                    "envelope_profile": "exact",
                    "assumption_bundle": "fault_free_transport",
                    "eligibility": "exact",
                    "eligibility_reason": null
                },
                "metadata": {
                    "checkpoint_tick": 4,
                    "wal_tail_start_tick": 5,
                    "highest_recovered_tick": 6,
                    "resumed_operation_ids": ["op#durable"],
                    "terminal_operation_ids": [],
                    "cached_evidence_ids": ["proof#1"]
                },
                "decisions": [{
                    "operation_id": "op#durable",
                    "level": "finalized",
                    "finalization": "finalized",
                    "action": "reuse_finalized",
                    "cached_evidence_ids": ["proof#1"],
                    "gate_crossed": true
                }]
            }))
            .expect("decode durable resume summary");
        let artifact = ViewerArtifactFile::new(ViewerArtifact::DurableInspection(Box::new(
            DurableInspectionReport {
                wal_entries: vec![telltale_simulator::durability::DurableWalEntryProjection {
                    tick: 4,
                    operation_id: "op#durable".to_string(),
                    kind: telltale_simulator::durability::DurableWalEntryKind::Finalization,
                    detail: "Finalized proof=proof#1 handle=handle#1".to_string(),
                }],
                evidence_cache_entries: Vec::new(),
                recovery: Some(recovery),
            },
        )));
        let file = NamedTempFile::new().expect("temp file");
        artifact.write_json(file.path()).expect("write artifact");
        let loaded = ViewerArtifactFile::load_json(file.path()).expect("load artifact");
        match loaded.artifact {
            ViewerArtifact::DurableInspection(report) => {
                let recovery = report.recovery.expect("recovery summary");
                assert_eq!(recovery.metadata.checkpoint_tick, 4);
                assert_eq!(recovery.decisions.len(), 1);
                assert_eq!(recovery.decisions[0].operation_id, "op#durable");
                assert!(recovery.decisions[0].gate_crossed);
            }
            other => panic!("unexpected artifact kind: {other:?}"),
        }
    }

    #[test]
    fn viewer_artifact_file_rejects_unknown_schema_version() {
        let mut artifact = ViewerArtifactFile::new(ViewerArtifact::DecisionReport(
            telltale_simulator::decision::decide_theorem_eligibility(&Scenario {
                name: "x".to_string(),
                roles: vec!["A".to_string()],
                steps: 1,
                execution: Default::default(),
                seed: 0,
                network: None,
                field: None,
                reconfigurations: Vec::new(),
                adversaries: Vec::new(),
                properties: None,
                checkpoint_interval: None,
                durability: Default::default(),
                theorem: Default::default(),
                extensions: BTreeMap::new(),
            }),
        ));
        artifact.schema_version = 99;
        let error = artifact.validate().expect_err("unsupported version");
        assert!(matches!(
            error,
            ViewerModelError::UnsupportedSchemaVersion {
                supported: 1,
                found: 99
            }
        ));
    }

    #[test]
    fn branch_patch_serializes_stably() {
        let patch = ScenarioBranchPatch {
            operations: vec![
                ScenarioPatchOperation::SetSeed { seed: 42 },
                ScenarioPatchOperation::SetExecutionBackend {
                    backend: ExecutionBackend::Canonical,
                },
                ScenarioPatchOperation::UpsertExtension {
                    namespace: "demo".to_string(),
                    value: toml::Value::String("enabled".to_string()),
                },
            ],
        };
        let json = serde_json::to_string(&patch).expect("serialize patch");
        let decoded =
            serde_json::from_str::<ScenarioBranchPatch>(&json).expect("deserialize patch");
        let reencoded = serde_json::to_string(&decoded).expect("reencode patch");
        assert_eq!(reencoded, json);
    }

    #[test]
    fn in_memory_service_supports_artifact_inventory_and_branch_commands() {
        let artifact = ViewerArtifactFile::new(ViewerArtifact::ScenarioBundle(Box::new(
            ScenarioBundleArtifact::new(None, sample_result(), None),
        )));
        let mut service = InMemoryViewerService::new();
        service
            .command(ViewerCommand::ImportArtifact {
                artifact_id: "run/demo".to_string(),
                artifact: Box::new(artifact),
            })
            .expect("import artifact");

        let inventory = service
            .query(ViewerQuery::ListArtifacts)
            .expect("query inventory");
        match inventory {
            ViewerQueryResult::ArtifactInventory { artifacts } => {
                assert_eq!(artifacts.len(), 1);
                assert_eq!(artifacts[0].artifact_id, "run/demo");
            }
            other => panic!("unexpected inventory result: {other:?}"),
        }

        service
            .command(create_branch_command(
                "run/demo".to_string(),
                "branch/alt".to_string(),
                "root".to_string(),
                3,
            ))
            .expect("create branch");
        service
            .command(update_branch_command(
                "run/demo".to_string(),
                "branch/alt".to_string(),
                3,
            ))
            .expect("update branch");
        service
            .command(ViewerCommand::RequestRerun {
                run_id: "run/demo".to_string(),
                branch_id: "branch/alt".to_string(),
            })
            .expect("request rerun");

        let lineage = service
            .query(ViewerQuery::BranchLineage {
                run_id: "run/demo".to_string(),
            })
            .expect("lineage");
        match lineage {
            ViewerQueryResult::BranchLineage { lineage } => {
                assert_eq!(lineage.branches.len(), 2);
                assert!(lineage
                    .branches
                    .iter()
                    .any(|branch| branch.branch_id == "branch/alt" && branch.rerun_requested));
            }
            other => panic!("unexpected lineage result: {other:?}"),
        }
    }

    #[test]
    fn branch_lineage_graph_projection_is_deterministic() {
        let artifact = ViewerArtifactFile::new(ViewerArtifact::ScenarioBundle(Box::new(
            ScenarioBundleArtifact::new(None, sample_result(), None),
        )));
        let mut service = InMemoryViewerService::new();
        service
            .command(ViewerCommand::ImportArtifact {
                artifact_id: "run/demo".to_string(),
                artifact: Box::new(artifact),
            })
            .expect("import artifact");
        service
            .command(create_branch_command(
                "run/demo".to_string(),
                "branch/alt".to_string(),
                "root".to_string(),
                3,
            ))
            .expect("create branch");

        let projection = service
            .query(ViewerQuery::GraphProjection(GraphProjectionRequest {
                run_id: "run/demo".to_string(),
                branch_id: "root".to_string(),
                step: None,
                kind: GraphProjectionKind::BranchLineage,
            }))
            .expect("branch lineage graph");
        match projection {
            ViewerQueryResult::GraphProjection { projection } => {
                assert_eq!(projection.nodes.len(), 2);
                assert_eq!(projection.edges.len(), 1);
                assert_eq!(projection.edges[0].from, "root");
                assert_eq!(projection.edges[0].to, "branch/alt");
            }
            other => panic!("unexpected graph projection result: {other:?}"),
        }
    }

    #[test]
    fn branch_command_builders_emit_typed_patch_commands() {
        let create = create_branch_command(
            "run/demo".to_string(),
            "branch/next".to_string(),
            "root".to_string(),
            4,
        );
        let update = update_branch_command("run/demo".to_string(), "branch/next".to_string(), 9);
        let delete = delete_branch_command("run/demo".to_string(), "branch/next".to_string());

        assert!(matches!(
            create,
            ViewerCommand::CreateBranch {
                from_step: 4,
                patch: ScenarioBranchPatch { .. },
                ..
            }
        ));
        assert!(matches!(
            update,
            ViewerCommand::UpdateBranch {
                patch: ScenarioBranchPatch { .. },
                ..
            }
        ));
        assert!(matches!(delete, ViewerCommand::DeleteBranch { .. }));
    }

    #[test]
    fn semantic_comparison_and_divergence_queries_are_stable() {
        let mut baseline = sample_result();
        baseline
            .trace
            .records
            .push(telltale_simulator::trace::StepRecord {
                step: 1,
                role: "alpha".to_string(),
                state: Vec::new(),
            });
        let mut candidate = baseline.clone();
        candidate
            .trace
            .records
            .push(telltale_simulator::trace::StepRecord {
                step: 2,
                role: "beta".to_string(),
                state: Vec::new(),
            });

        let mut service = InMemoryViewerService::new();
        for (artifact_id, result) in [("run/base", baseline), ("run/candidate", candidate)] {
            service
                .command(ViewerCommand::ImportArtifact {
                    artifact_id: artifact_id.to_string(),
                    artifact: Box::new(ViewerArtifactFile::new(ViewerArtifact::ScenarioBundle(
                        Box::new(ScenarioBundleArtifact::new(None, result, None)),
                    ))),
                })
                .expect("import scenario bundle");
        }

        let request = SemanticComparisonRequest {
            baseline_artifact_id: "run/base".to_string(),
            candidate_artifact_id: "run/candidate".to_string(),
        };
        let comparison = service
            .query(ViewerQuery::SemanticComparison(request.clone()))
            .expect("comparison query");
        match comparison {
            ViewerQueryResult::SemanticComparison { comparison } => {
                assert_eq!(
                    comparison.relation,
                    SemanticComparisonClass::SafetyVisibleDivergence
                );
                assert!(comparison.first_divergence.is_some());
            }
            other => panic!("unexpected comparison result: {other:?}"),
        }

        let divergence = service
            .query(ViewerQuery::FirstDivergence(request))
            .expect("first divergence query");
        match divergence {
            ViewerQueryResult::FirstDivergence { divergence } => {
                assert_eq!(
                    divergence.expect("divergence point").kind,
                    SemanticDivergenceKind::StepCount
                );
            }
            other => panic!("unexpected divergence result: {other:?}"),
        }
    }

    #[test]
    fn counterexample_sweep_effect_and_minimization_queries_round_trip() {
        let mut service = InMemoryViewerService::new();
        import_counterexample_fixture(&mut service);
        assert_counterexample_query(&service);
        assert_sweep_query(&mut service);
        assert_suite_query(&mut service);
        assert_effect_trace_query(&mut service);
        assert_minimization_query(&mut service);
    }

    fn import_counterexample_fixture(service: &mut InMemoryViewerService) {
        let mut ineligible_result = sample_result();
        ineligible_result.stats.theorem_profile.assumption_bundle =
            TheoremAssumptionBundle::ObservedTransport;
        ineligible_result.stats.theorem_profile.eligibility = TheoremEligibility::Ineligible;
        ineligible_result.stats.theorem_profile.eligibility_reason =
            Some("observed transport is not exact".to_string());

        for (artifact_id, result) in [
            ("run/base", sample_result()),
            ("run/ineligible", ineligible_result),
        ] {
            service
                .command(ViewerCommand::ImportArtifact {
                    artifact_id: artifact_id.to_string(),
                    artifact: Box::new(ViewerArtifactFile::new(ViewerArtifact::ScenarioBundle(
                        Box::new(ScenarioBundleArtifact::new(None, result, None)),
                    ))),
                })
                .expect("import scenario bundle");
        }
    }

    fn assert_counterexample_query(service: &InMemoryViewerService) {
        let counterexample = service
            .query(ViewerQuery::ArtifactCounterexample {
                artifact_id: "run/ineligible".to_string(),
            })
            .expect("artifact counterexample");
        match counterexample {
            ViewerQueryResult::Counterexample { counterexample } => {
                assert!(
                    counterexample.summary.contains("exact")
                        || counterexample.decision_report.is_some()
                );
            }
            other => panic!("unexpected counterexample result: {other:?}"),
        }
    }

    fn assert_sweep_query(service: &mut InMemoryViewerService) {
        service
            .command(ViewerCommand::ExecuteSweep {
                sweep_id: "sweep/demo".to_string(),
                baseline_artifact_id: Some("run/base".to_string()),
                cases: vec![
                    SweepCaseSpec {
                        case_id: "base".to_string(),
                        artifact_id: "run/base".to_string(),
                        parameters: BTreeMap::from([("seed".to_string(), "7".to_string())]),
                    },
                    SweepCaseSpec {
                        case_id: "ineligible".to_string(),
                        artifact_id: "run/ineligible".to_string(),
                        parameters: BTreeMap::from([(
                            "assumption_bundle".to_string(),
                            "observed_transport".to_string(),
                        )]),
                    },
                ],
            })
            .expect("execute sweep");
        let sweep = service
            .query(ViewerQuery::SweepExplorer(SweepExplorerRequest {
                sweep_id: "sweep/demo".to_string(),
                filter_text: Some("ineligible".to_string()),
                group_by: Some("assumption_bundle".to_string()),
                max_results: Some(4),
            }))
            .expect("load sweep explorer");
        match sweep {
            ViewerQueryResult::SweepExplorer { explorer } => {
                assert_eq!(explorer.total_cases, 2);
                assert_eq!(explorer.visible_cases.len(), 1);
            }
            other => panic!("unexpected sweep explorer result: {other:?}"),
        }
    }

    fn assert_suite_query(service: &mut InMemoryViewerService) {
        service
            .command(ViewerCommand::ExecuteExperimentSuite {
                definition: ExperimentSuiteDefinition {
                    suite_id: "suite/demo".to_string(),
                    threshold: RegressionThreshold {
                        max_changed_steps: 0,
                        allow_normalization_only: true,
                    },
                    cases: vec![ExperimentSuiteCase {
                        case_id: "base-vs-ineligible".to_string(),
                        baseline_artifact_id: "run/base".to_string(),
                        candidate_artifact_id: "run/ineligible".to_string(),
                    }],
                },
            })
            .expect("execute suite");
        let suite = service
            .query(ViewerQuery::ExperimentSuite {
                suite_id: "suite/demo".to_string(),
            })
            .expect("load suite");
        match suite {
            ViewerQueryResult::ExperimentSuite { suite } => {
                assert_eq!(suite.cases.len(), 1);
            }
            other => panic!("unexpected suite result: {other:?}"),
        }
    }

    fn assert_effect_trace_query(service: &mut InMemoryViewerService) {
        service
            .command(mocked_rerun_command(
                "run/base".to_string(),
                "root".to_string(),
                "ready",
            ))
            .expect("queue mocked rerun");
        let effect_trace = service
            .query(ViewerQuery::EffectTrace {
                artifact_id: "run/base".to_string(),
                branch_id: "root".to_string(),
            })
            .expect("load effect trace");
        match effect_trace {
            ViewerQueryResult::EffectTrace { effect_trace } => {
                assert_eq!(effect_trace.overrides.len(), 1);
                assert!(!effect_trace.entries.is_empty());
            }
            other => panic!("unexpected effect trace result: {other:?}"),
        }
    }

    fn assert_minimization_query(service: &mut InMemoryViewerService) {
        service
            .command(minimize_branch_command(
                "minimize:run/base:root",
                "run/base".to_string(),
                "root".to_string(),
            ))
            .expect("request minimization");
        let minimization = service
            .query(ViewerQuery::Minimization {
                request_id: "minimize:run/base:root".to_string(),
            })
            .expect("load minimization");
        match minimization {
            ViewerQueryResult::Minimization { result } => {
                assert!(result.minimized_steps >= 1);
            }
            other => panic!("unexpected minimization result: {other:?}"),
        }
    }

    #[test]
    fn downstream_extension_manifest_round_trips_without_internal_assumptions() {
        let mut service = InMemoryViewerService::new();
        service
            .command(ViewerCommand::RegisterExtensions {
                manifest: ViewerExtensionManifest {
                    descriptors: vec![
                        ViewerExtensionDescriptor {
                            id: "downstream.overview".to_string(),
                            title: "Overview Overlay".to_string(),
                            slot: ViewerExtensionSlot::OverviewPanel,
                            summary: "External summary panel".to_string(),
                        },
                        ViewerExtensionDescriptor {
                            id: "downstream.graph".to_string(),
                            title: "Graph Overlay".to_string(),
                            slot: ViewerExtensionSlot::GraphAnnotation,
                            summary: "External graph annotations".to_string(),
                        },
                    ],
                },
            })
            .expect("register extensions");
        let manifest = service
            .query(ViewerQuery::ExtensionManifest)
            .expect("load extension manifest");
        match manifest {
            ViewerQueryResult::ExtensionManifest { manifest } => {
                assert_eq!(manifest.descriptors.len(), 2);
                assert_eq!(manifest.descriptors[0].id, "downstream.overview");
            }
            other => panic!("unexpected extension manifest: {other:?}"),
        }
    }
}
