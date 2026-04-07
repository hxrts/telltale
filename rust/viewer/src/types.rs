//! Data types for the viewer artifact, query, command, and comparison surfaces.

use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::fs;
use std::path::Path;
use telltale_simulator::analysis::ObservabilityComparison;
use telltale_simulator::approximation::ApproximationManifest;
use telltale_simulator::contracts::ContractCheckReport;
use telltale_simulator::decision::DecisionReport;
use telltale_simulator::durability::DurableInspectionReport;
use telltale_simulator::environment::EnvironmentTrace;
use telltale_simulator::reconfiguration::ReconfigurationRecord;
use telltale_simulator::runner::{ScenarioResult, SchedulerComparison};
use telltale_simulator::scenario::{
    ExecutionBackend, ReconfigurationSpec, ResolvedExecutionBackend, ResolvedTheoremProfile,
    Scenario, SchedulerPolicySpec, TheoremProfileSpec,
};
use telltale_simulator::sweep::{SweepDiffReport, SweepManifest};

use crate::error::ViewerModelError;
use crate::service::ViewerApplicationService;

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
