//! Data types and interactive state for the Telltale viewer UI.

use dioxus::prelude::spawn;
use std::collections::BTreeMap;
use std::future::Future;
use std::pin::Pin;
use std::sync::{Arc, Mutex};
use telltale_macros::{actor_owned, observed_only, strong_reference, weak_identifier};
use telltale_simulator::scenario::{ExecutionRegime, ResolvedTheoremProfile};
use telltale_viewer::{
    create_branch_command, delete_branch_command, minimize_branch_command, mocked_rerun_command,
    update_branch_command, ArtifactId, BranchId, EffectTraceArtifact, ExperimentSuiteReport,
    GraphProjection, GraphProjectionKind, MinimizationResult, SearchResult,
    SemanticComparisonResult, SweepExplorerView, TheoremAwareCounterexample,
    ViewerExtensionManifest, ViewerReport,
};

type BoxedTask = Pin<Box<dyn Future<Output = ()> + 'static>>;

#[weak_identifier("artifact_id")]
pub type SelectedArtifactId = ArtifactId;

#[weak_identifier("branch_id")]
pub type SelectedBranchId = BranchId;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ViewerPage {
    Overview,
    Graph,
    Insight,
    Sweeps,
    Effects,
}

impl ViewerPage {
    #[must_use]
    pub const fn label(self) -> &'static str {
        match self {
            Self::Overview => "Artifacts",
            Self::Graph => "Graphs",
            Self::Insight => "Insights",
            Self::Sweeps => "Sweeps",
            Self::Effects => "Effects",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HarnessMode {
    Normal,
    Deterministic,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ViewerReadinessState {
    Loading,
    Ready,
    Degraded,
}

impl ViewerReadinessState {
    pub(crate) fn label(self) -> &'static str {
        match self {
            Self::Loading => "Loading",
            Self::Ready => "Ready",
            Self::Degraded => "Degraded",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ViewerPublicationDiagnostics {
    pub readiness: ViewerReadinessState,
    pub harness_mode: HarnessMode,
    pub artifact_count: usize,
    pub scenario_count: usize,
    pub active_page: ViewerPage,
    pub active_artifact: Option<SelectedArtifactId>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ViewerGraphWorkspace {
    pub projections: Vec<GraphProjection>,
    pub active_projection: usize,
    pub active_branch: SelectedBranchId,
    pub active_step: u64,
    pub selected_node: Option<String>,
    pub selected_edge: Option<String>,
    pub layout: GraphLayoutState,
    pub search_query: String,
    pub search_results: Vec<SearchResult>,
    pub command_log: Vec<String>,
}

impl ViewerGraphWorkspace {
    pub(crate) fn active_projection(&self) -> Option<&GraphProjection> {
        self.projections.get(self.active_projection)
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct GraphLayoutState {
    pub positions: BTreeMap<String, GraphNodeLayout>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GraphNodeLayout {
    pub x: i32,
    pub y: i32,
}

#[derive(Clone, Debug, PartialEq)]
pub struct RunInsightWorkspace {
    pub theorem_profile: Option<ResolvedTheoremProfile>,
    pub execution_regime: Option<ExecutionRegime>,
    pub semantic_comparison: Option<SemanticComparisonResult>,
    pub counterexample: Option<TheoremAwareCounterexample>,
    pub watch_expressions: Vec<WatchExpression>,
    pub annotations: Vec<RunAnnotation>,
    pub provenance: BranchProvenance,
    pub run_diff: RunDiffSnapshot,
    pub causality: Vec<CausalityEvent>,
    pub bookmarks: Vec<RunBookmark>,
    pub archive_status: String,
    pub minimization: Option<MinimizationResult>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SweepExplorerWorkspace {
    pub explorer: SweepExplorerView,
    pub all_cases: Vec<telltale_viewer::SweepCaseResult>,
    pub suite: ExperimentSuiteReport,
    pub selected_case: Option<String>,
    pub active_filter: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EffectWorkspace {
    pub effect_trace: EffectTraceArtifact,
    pub mock_command_log: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WatchExpression {
    pub label: String,
    pub value: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RunAnnotation {
    pub target: AnnotationTarget,
    pub text: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AnnotationTarget {
    Step(u64),
    Branch(SelectedBranchId),
    Artifact(SelectedArtifactId),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BranchProvenance {
    pub run_id: String,
    pub parent_branch: Option<SelectedBranchId>,
    pub patch_count: u64,
    pub rerun_requested: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RunDiffSnapshot {
    pub baseline_branch: SelectedBranchId,
    pub candidate_branch: SelectedBranchId,
    pub changed_steps: u64,
    pub command_count: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CausalityEvent {
    pub step: u64,
    pub label: String,
    pub detail: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RunBookmark {
    pub branch_id: SelectedBranchId,
    pub step: u64,
    pub label: String,
}

#[derive(Clone, Debug, PartialEq)]
pub struct ViewerWorkspace {
    pub report: ViewerReport,
    pub graph: ViewerGraphWorkspace,
    pub insights: RunInsightWorkspace,
    pub sweeps: SweepExplorerWorkspace,
    pub effects: EffectWorkspace,
    pub extensions: ViewerExtensionManifest,
    pub diagnostics: ViewerPublicationDiagnostics,
    pub pages: Vec<ViewerPage>,
}

#[derive(Clone)]
pub struct ViewerTaskRuntime {
    spawn: Arc<dyn Fn(BoxedTask) + Send + Sync>,
}

impl ViewerTaskRuntime {
    #[must_use]
    pub fn dioxus() -> Self {
        Self {
            spawn: Arc::new(|future| {
                spawn(async move {
                    future.await;
                });
            }),
        }
    }
}

#[actor_owned("viewer_shell_tasks")]
#[derive(Clone)]
pub struct ViewerTaskOwner {
    runtime: ViewerTaskRuntime,
    labels: Arc<Mutex<Vec<String>>>,
}

impl ViewerTaskOwner {
    #[must_use]
    pub fn new(runtime: ViewerTaskRuntime) -> Self {
        Self {
            runtime,
            labels: Arc::new(Mutex::new(Vec::new())),
        }
    }

    /// Spawn one named UI task through the current runtime.
    ///
    /// # Panics
    ///
    /// Panics if the internal task-label lock has been poisoned.
    pub fn spawn_named<F>(&self, label: impl Into<String>, future: F)
    where
        F: Future<Output = ()> + 'static,
    {
        self.labels
            .lock()
            .expect("viewer task labels lock poisoned")
            .push(label.into());
        (self.runtime.spawn)(Box::pin(future));
    }

    /// Return the labels recorded for spawned tasks.
    ///
    /// # Panics
    ///
    /// Panics if the internal task-label lock has been poisoned.
    #[must_use]
    pub fn labels(&self) -> Vec<String> {
        self.labels
            .lock()
            .expect("viewer task labels lock poisoned")
            .clone()
    }
}

#[strong_reference("viewer_workspace")]
pub struct WorkspaceHandle {
    pub workspace: ViewerWorkspace,
}

#[observed_only]
#[derive(Clone, PartialEq)]
pub struct InteractiveViewerState {
    pub workspace: ViewerWorkspace,
    pub active_page: ViewerPage,
    branch_counter: u64,
}

impl InteractiveViewerState {
    #[must_use]
    pub fn from_workspace(workspace: ViewerWorkspace) -> Self {
        Self {
            active_page: workspace.diagnostics.active_page,
            workspace,
            branch_counter: 0,
        }
    }

    pub(crate) fn projection_step_limit(&self) -> u64 {
        self.workspace
            .graph
            .projections
            .iter()
            .flat_map(|projection| projection.nodes.iter().filter_map(|node| node.step))
            .max()
            .unwrap_or(0)
    }

    pub(crate) fn branch_lineage_projection_mut(&mut self) -> Option<&mut GraphProjection> {
        self.workspace
            .graph
            .projections
            .iter_mut()
            .find(|projection| projection.kind == GraphProjectionKind::BranchLineage)
    }

    pub fn set_page(&mut self, page: ViewerPage) {
        self.active_page = page;
        self.workspace.diagnostics.active_page = page;
    }

    pub fn select_artifact(&mut self, artifact_id: String) {
        self.workspace.diagnostics.active_artifact = Some(artifact_id);
    }

    pub fn select_projection(&mut self, index: usize) {
        if index < self.workspace.graph.projections.len() {
            self.workspace.graph.active_projection = index;
            self.workspace.graph.active_step = self
                .projection_step_limit()
                .min(self.workspace.graph.active_step);
        }
    }

    pub fn step_forward(&mut self) {
        let limit = self.projection_step_limit();
        if self.workspace.graph.active_step < limit {
            self.workspace.graph.active_step += 1;
            self.workspace.graph.selected_node =
                self.workspace
                    .graph
                    .active_projection()
                    .and_then(|projection| {
                        projection
                            .nodes
                            .iter()
                            .find(|node| node.step == Some(self.workspace.graph.active_step))
                            .map(|node| node.id.clone())
                    });
        }
    }

    pub fn step_backward(&mut self) {
        if self.workspace.graph.active_step > 0 {
            self.workspace.graph.active_step -= 1;
            self.workspace.graph.selected_node =
                self.workspace
                    .graph
                    .active_projection()
                    .and_then(|projection| {
                        projection
                            .nodes
                            .iter()
                            .find(|node| node.step == Some(self.workspace.graph.active_step))
                            .map(|node| node.id.clone())
                    });
        }
    }

    pub fn jump_to_step(&mut self, step: u64) {
        self.workspace.graph.active_step = step.min(self.projection_step_limit());
        self.workspace.graph.selected_node =
            self.workspace
                .graph
                .active_projection()
                .and_then(|projection| {
                    projection
                        .nodes
                        .iter()
                        .find(|node| node.step == Some(self.workspace.graph.active_step))
                        .map(|node| node.id.clone())
                });
    }

    pub fn fork_branch_from_current_step(&mut self) {
        self.branch_counter = self.branch_counter.saturating_add(1);
        let parent_branch = self.workspace.graph.active_branch.clone();
        let branch_id = format!("branch/{}", self.branch_counter);
        let active_step = self.workspace.graph.active_step;
        let command = create_branch_command(
            self.workspace.insights.provenance.run_id.clone(),
            branch_id.clone(),
            parent_branch.clone(),
            active_step,
        );
        self.workspace
            .graph
            .command_log
            .push(format!("{command:?}"));
        if let Some(projection) = self.branch_lineage_projection_mut() {
            projection.nodes.push(telltale_viewer::GraphNode {
                id: branch_id.clone(),
                label: branch_id.clone(),
                category: "branch".to_string(),
                step: Some(active_step),
            });
            projection.edges.push(telltale_viewer::GraphEdge {
                from: parent_branch.clone(),
                to: branch_id.clone(),
                label: "fork".to_string(),
                step: Some(active_step),
            });
        }
        self.workspace.graph.active_branch = branch_id.clone();
        self.workspace.insights.provenance.parent_branch = Some(parent_branch);
        self.workspace.insights.provenance.patch_count = self
            .workspace
            .insights
            .provenance
            .patch_count
            .saturating_add(1);
        self.workspace.insights.run_diff.candidate_branch = branch_id.clone();
        self.workspace.insights.run_diff.changed_steps = self.workspace.graph.active_step;
        self.workspace.insights.run_diff.command_count =
            u64::try_from(self.workspace.graph.command_log.len()).unwrap_or(u64::MAX);
        self.workspace.insights.annotations.push(RunAnnotation {
            target: AnnotationTarget::Branch(branch_id.clone()),
            text: format!(
                "Forked a deterministic branch at step {}",
                self.workspace.graph.active_step
            ),
        });
    }

    pub fn update_active_branch(&mut self) {
        if self.workspace.graph.active_branch == "root" {
            self.workspace
                .graph
                .command_log
                .push("cannot update root branch".to_string());
            return;
        }
        let branch_id = self.workspace.graph.active_branch.clone();
        let command = update_branch_command(
            self.workspace.insights.provenance.run_id.clone(),
            branch_id.clone(),
            self.workspace.graph.active_step,
        );
        self.workspace
            .graph
            .command_log
            .push(format!("{command:?}"));
        self.workspace.insights.provenance.patch_count = self
            .workspace
            .insights
            .provenance
            .patch_count
            .saturating_add(1);
        self.workspace.insights.annotations.push(RunAnnotation {
            target: AnnotationTarget::Branch(branch_id.clone()),
            text: format!("Updated branch `{branch_id}` through a typed patch command."),
        });
        self.workspace.insights.run_diff.command_count =
            u64::try_from(self.workspace.graph.command_log.len()).unwrap_or(u64::MAX);
    }

    pub fn delete_active_branch(&mut self) {
        if self.workspace.graph.active_branch == "root" {
            self.workspace
                .graph
                .command_log
                .push("cannot delete root branch".to_string());
            return;
        }
        let branch_id = self.workspace.graph.active_branch.clone();
        let command = delete_branch_command(
            self.workspace.insights.provenance.run_id.clone(),
            branch_id.clone(),
        );
        self.workspace
            .graph
            .command_log
            .push(format!("{command:?}"));
        if let Some(projection) = self.branch_lineage_projection_mut() {
            if let Some(node) = projection
                .nodes
                .iter_mut()
                .find(|node| node.id == branch_id)
            {
                node.category = "branch_deleted".to_string();
                node.label = format!("{branch_id} (deleted)");
            }
        }
        self.workspace.graph.active_branch = "root".to_string();
        self.workspace.insights.annotations.push(RunAnnotation {
            target: AnnotationTarget::Branch(branch_id.clone()),
            text: format!("Deleted branch `{branch_id}` through a typed command."),
        });
        self.workspace.insights.run_diff.candidate_branch = "root".to_string();
        self.workspace.insights.run_diff.command_count =
            u64::try_from(self.workspace.graph.command_log.len()).unwrap_or(u64::MAX);
    }

    pub fn search(&mut self, query: &str) {
        self.workspace.graph.search_query = query.to_string();
        let needle = query.to_lowercase();
        self.workspace.graph.search_results = self
            .workspace
            .graph
            .projections
            .iter()
            .flat_map(|projection| {
                projection
                    .nodes
                    .iter()
                    .filter(|node| {
                        node.label.to_lowercase().contains(&needle)
                            || node.id.to_lowercase().contains(&needle)
                    })
                    .map(|node| SearchResult {
                        artifact_id: self
                            .workspace
                            .diagnostics
                            .active_artifact
                            .clone()
                            .unwrap_or_else(|| "demo-run".to_string()),
                        domain: telltale_viewer::SearchDomain::EventLabel,
                        label: node.label.clone(),
                        detail: format!("{:?}", projection.kind),
                        branch_id: Some(self.workspace.graph.active_branch.clone()),
                        step: node.step,
                    })
            })
            .collect();
    }

    pub fn reload_archive(&mut self) {
        self.workspace.insights.archive_status = "reloaded from archived artifact set".to_string();
        self.workspace.insights.annotations.push(RunAnnotation {
            target: AnnotationTarget::Artifact(
                self.workspace
                    .diagnostics
                    .active_artifact
                    .clone()
                    .unwrap_or_else(|| "demo-run".to_string()),
            ),
            text: "Reloaded the archived artifact set and preserved deterministic viewer state."
                .to_string(),
        });
    }

    pub fn add_bookmark(&mut self) {
        self.workspace.insights.bookmarks.push(RunBookmark {
            branch_id: self.workspace.graph.active_branch.clone(),
            step: self.workspace.graph.active_step,
            label: format!(
                "bookmark:{}@{}",
                self.workspace.graph.active_branch, self.workspace.graph.active_step
            ),
        });
    }

    pub fn filter_sweeps(&mut self, needle: &str) {
        self.workspace.sweeps.active_filter = needle.to_string();
        let lowered = needle.to_lowercase();
        self.workspace.sweeps.explorer.visible_cases = self
            .workspace
            .sweeps
            .all_cases
            .iter()
            .filter(|case| {
                needle.is_empty()
                    || case.case_id.to_lowercase().contains(&lowered)
                    || case.artifact_id.to_lowercase().contains(&lowered)
            })
            .cloned()
            .collect();
    }

    pub fn drill_into_sweep_case(&mut self, case_id: &str) {
        self.workspace.sweeps.selected_case = Some(case_id.to_string());
        if let Some(case) = self
            .workspace
            .sweeps
            .explorer
            .visible_cases
            .iter()
            .find(|case| case.case_id == case_id)
        {
            self.workspace.diagnostics.active_artifact = Some(case.artifact_id.clone());
            self.workspace.graph.active_branch = "root".to_string();
            self.workspace.insights.run_diff.candidate_branch = "root".to_string();
        }
        self.set_page(ViewerPage::Overview);
    }

    pub fn request_mocked_rerun(&mut self) {
        let command = mocked_rerun_command(
            self.workspace.insights.provenance.run_id.clone(),
            self.workspace.graph.active_branch.clone(),
            "ready",
        );
        self.workspace
            .effects
            .mock_command_log
            .push(format!("{command:?}"));
    }

    pub fn request_minimization(&mut self) {
        let artifact_id = self
            .workspace
            .diagnostics
            .active_artifact
            .clone()
            .unwrap_or_else(|| "demo-run".to_string());
        let command = minimize_branch_command(
            format!(
                "minimize:{artifact_id}:{}",
                self.workspace.graph.active_branch
            ),
            artifact_id,
            self.workspace.graph.active_branch.clone(),
        );
        self.workspace
            .effects
            .mock_command_log
            .push(format!("{command:?}"));
    }
}
