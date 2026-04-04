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

pub use telltale_simulator::analysis::{NormalizedObservability, ObservabilityComparison};
pub use telltale_simulator::approximation::ApproximationManifest;
pub use telltale_simulator::contracts::ContractCheckReport;
pub use telltale_simulator::decision::DecisionReport;
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
    ScenarioBundle(ScenarioBundleArtifact),
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
    LoadArtifact { artifact_id: ArtifactId },
    ScenarioSummary { artifact_id: ArtifactId },
    BranchLineage { run_id: RunId },
    GraphProjection(GraphProjectionRequest),
    Search(SearchQuery),
    HistoricalInspection(HistoricalInspectionState),
}

/// Stable query result surface returned by the application service.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum ViewerQueryResult {
    ArtifactInventory {
        artifacts: Vec<ArtifactInventoryEntry>,
    },
    ArtifactFile {
        artifact: ViewerArtifactFile,
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
        artifact: ViewerArtifactFile,
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

/// Stable command result surface returned by the application service boundary.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum ViewerCommandResult {
    ArtifactImported { artifact_id: ArtifactId },
    BranchCreated { run_id: RunId, branch_id: BranchId },
    BranchUpdated { run_id: RunId, branch_id: BranchId },
    BranchDeleted { run_id: RunId, branch_id: BranchId },
    RerunRequested { run_id: RunId, branch_id: BranchId },
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
        scenario: Scenario,
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

/// Stable application-service trait shared by UI and shell layers.
pub trait ViewerApplicationService {
    /// Execute one typed query.
    fn query(&self, query: ViewerQuery) -> Result<ViewerQueryResult, ViewerModelError>;

    /// Execute one typed command.
    fn command(&mut self, command: ViewerCommand) -> Result<ViewerCommandResult, ViewerModelError>;
}

/// In-process application-service implementation used by tests and the first web shell.
#[derive(Default)]
pub struct InMemoryViewerService {
    artifacts: BTreeMap<ArtifactId, ViewerArtifactFile>,
    runs: BTreeMap<RunId, RunWorkspace>,
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
            ViewerArtifact::ScenarioBundle(bundle) => Some(bundle),
            _ => None,
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
            .filter(|record| step_limit.is_none_or(|limit| record.step <= limit))
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
            .filter(|record| step_limit.is_none_or(|limit| record.step <= limit))
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
}

impl ViewerApplicationService for InMemoryViewerService {
    fn query(&self, query: ViewerQuery) -> Result<ViewerQueryResult, ViewerModelError> {
        match query {
            ViewerQuery::ListArtifacts => Ok(ViewerQueryResult::ArtifactInventory {
                artifacts: self
                    .artifacts
                    .iter()
                    .map(|(artifact_id, artifact)| ArtifactInventoryEntry {
                        artifact_id: artifact_id.clone(),
                        kind: artifact.kind(),
                        label: format!("{artifact_id}: {:?}", artifact.kind()),
                    })
                    .collect(),
            }),
            ViewerQuery::LoadArtifact { artifact_id } => {
                let artifact = self.artifacts.get(&artifact_id).cloned().ok_or_else(|| {
                    ViewerModelError::NotFound {
                        kind: "artifact".to_string(),
                        id: artifact_id.clone(),
                    }
                })?;
                Ok(ViewerQueryResult::ArtifactFile { artifact })
            }
            ViewerQuery::ScenarioSummary { artifact_id } => {
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
            ViewerQuery::BranchLineage { run_id } => {
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
                                patch_count: u64::try_from(branch.patches.len())
                                    .unwrap_or(u64::MAX),
                            })
                            .collect(),
                    },
                })
            }
            ViewerQuery::GraphProjection(request) => {
                let run =
                    self.runs
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
            ViewerQuery::Search(query) => {
                let needle = query.text.to_lowercase();
                let mut matches = Vec::new();
                for (artifact_id, artifact) in &self.artifacts {
                    let kind_match = format!("{:?}", artifact.kind()).to_lowercase();
                    if query.domain.is_none() || query.domain == Some(SearchDomain::Artifact) {
                        if artifact_id.to_lowercase().contains(&needle)
                            || kind_match.contains(&needle)
                        {
                            matches.push(SearchResult {
                                artifact_id: artifact_id.clone(),
                                domain: SearchDomain::Artifact,
                                label: artifact_id.clone(),
                                detail: format!("{:?}", artifact.kind()),
                                branch_id: None,
                                step: None,
                            });
                        }
                    }

                    if let ViewerArtifact::ScenarioBundle(bundle) = &artifact.artifact {
                        if query.domain.is_none() || query.domain == Some(SearchDomain::Role) {
                            for role in bundle
                                .trace_roles()
                                .into_iter()
                                .filter(|role| role.to_lowercase().contains(&needle))
                            {
                                matches.push(SearchResult {
                                    artifact_id: artifact_id.clone(),
                                    domain: SearchDomain::Role,
                                    label: role.clone(),
                                    detail: "trace role".to_string(),
                                    branch_id: Some("root".to_string()),
                                    step: None,
                                });
                            }
                        }
                        if query.domain.is_none() || query.domain == Some(SearchDomain::Step) {
                            for record in &bundle.result.trace.records {
                                if record.role.to_lowercase().contains(&needle) {
                                    matches.push(SearchResult {
                                        artifact_id: artifact_id.clone(),
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
                if query.domain.is_none() || query.domain == Some(SearchDomain::Branch) {
                    for (run_id, run) in &self.runs {
                        for (branch_id, branch) in &run.branches {
                            if branch_id.to_lowercase().contains(&needle) {
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
                Ok(ViewerQueryResult::SearchResults { matches })
            }
            ViewerQuery::HistoricalInspection(state) => {
                Ok(ViewerQueryResult::HistoricalInspection { state })
            }
        }
    }

    fn command(&mut self, command: ViewerCommand) -> Result<ViewerCommandResult, ViewerModelError> {
        match command {
            ViewerCommand::ImportArtifact {
                artifact_id,
                artifact,
            } => {
                artifact.validate()?;
                self.artifacts.insert(artifact_id.clone(), artifact.clone());
                if matches!(artifact.artifact, ViewerArtifact::ScenarioBundle(_)) {
                    let workspace = self.ensure_run_workspace(&artifact_id);
                    workspace.root_artifact_id = Some(artifact_id.clone());
                }
                Ok(ViewerCommandResult::ArtifactImported { artifact_id })
            }
            ViewerCommand::CreateBranch {
                run_id,
                branch_id,
                parent_branch_id,
                from_step,
                patch,
            } => {
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
            ViewerCommand::UpdateBranch {
                run_id,
                branch_id,
                patch,
            } => {
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
            ViewerCommand::DeleteBranch { run_id, branch_id } => {
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
            ViewerCommand::RequestRerun { run_id, branch_id } => {
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
        }
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
            },
        }
    }

    #[test]
    fn viewer_artifact_file_round_trips_and_validates_version() {
        let artifact = ViewerArtifactFile::new(ViewerArtifact::ScenarioBundle(
            ScenarioBundleArtifact::new(None, sample_result(), None),
        ));
        let file = NamedTempFile::new().expect("temp file");
        artifact.write_json(file.path()).expect("write artifact");
        let loaded = ViewerArtifactFile::load_json(file.path()).expect("load artifact");
        assert_eq!(loaded.kind(), ViewerArtifactKind::ScenarioBundle);
        assert_eq!(loaded.schema_version, artifact.schema_version);
        assert_eq!(loaded.format, artifact.format);
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
        let artifact = ViewerArtifactFile::new(ViewerArtifact::ScenarioBundle(
            ScenarioBundleArtifact::new(None, sample_result(), None),
        ));
        let mut service = InMemoryViewerService::new();
        service
            .command(ViewerCommand::ImportArtifact {
                artifact_id: "run/demo".to_string(),
                artifact,
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
        let artifact = ViewerArtifactFile::new(ViewerArtifact::ScenarioBundle(
            ScenarioBundleArtifact::new(None, sample_result(), None),
        ));
        let mut service = InMemoryViewerService::new();
        service
            .command(ViewerCommand::ImportArtifact {
                artifact_id: "run/demo".to_string(),
                artifact,
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
}
