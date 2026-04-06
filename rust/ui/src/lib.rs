//! Portable Dioxus UI core for the Telltale simulator tooling webapp.
//!
//! This crate owns reusable layout, routing state, and rendering helpers while
//! keeping browser APIs in `telltale-web` and semantic artifact truth in
//! `telltale-viewer`.

#![allow(missing_docs)]
#![allow(clippy::incompatible_msrv)]

use dioxus::prelude::*;
use dioxus_shadcn::components::badge::{Badge as ShadBadge, BadgeVariant};
use dioxus_shadcn::components::card::Card as ShadCard;
use dioxus_shadcn::components::scroll_area::{ScrollArea, ScrollAreaViewport};
use std::collections::BTreeMap;
use std::future::Future;
use std::pin::Pin;
use std::sync::{Arc, Mutex};
use telltale_machine::ProtocolMachineSemanticObjects;
use telltale_macros::{
    actor_owned, authoritative_source, observed_only, strong_reference, weak_identifier,
};
use telltale_simulator::analysis::NormalizedObservability;
use telltale_simulator::contracts::ContractCheckReport;
use telltale_simulator::decision::{
    DecisionCertificate, DecisionKind, DecisionOutcome, DecisionReport,
};
use telltale_simulator::environment::EnvironmentTrace;
use telltale_simulator::fault::AdversarySummary;
use telltale_simulator::reconfiguration::ReconfigurationSummary;
use telltale_simulator::runner::{
    CriticalCapacityPhase, CriticalCapacitySummary, ScenarioAnalysisArtifact,
    ScenarioReplayArtifact, ScenarioResult, ScenarioStats, SchedulerBoundMode,
    SchedulerEnvelopeStatus, SchedulerFairnessRequirement, SchedulerProfileSummary,
    TheoremProgressSummary,
};
use telltale_simulator::scenario::{
    DurabilitySpec, ExecutionBackend, ExecutionRegime, ResolvedExecutionBackend,
    ResolvedSchedulerPolicy, ResolvedTheoremProfile, Scenario, TheoremAssumptionBundle,
    TheoremEligibility, TheoremEnvelopeProfile, TheoremProfileSpec, TheoremSchedulerProfile,
};
use telltale_simulator::trace::Trace;
use telltale_viewer::{
    create_branch_command, delete_branch_command, minimize_branch_command, mocked_rerun_command,
    update_branch_command, ArtifactId, BranchId, EffectTraceArtifact, ExperimentSuiteCase,
    ExperimentSuiteDefinition, ExperimentSuiteReport, GraphProjection, GraphProjectionKind,
    GraphProjectionRequest, InMemoryViewerService, MinimizationResult, RegressionThreshold,
    ScenarioBundleArtifact, ScenarioBundleSummary, SearchResult, SemanticComparisonRequest,
    SemanticComparisonResult, SweepCaseSpec, SweepExplorerRequest, SweepExplorerView,
    TheoremAwareCounterexample, ViewerApplicationService, ViewerArtifact, ViewerArtifactFile,
    ViewerCommand, ViewerExtensionDescriptor, ViewerExtensionManifest, ViewerExtensionSlot,
    ViewerModelError, ViewerQuery, ViewerQueryResult, ViewerReport,
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
    fn label(self) -> &'static str {
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

impl ViewerPublicationDiagnostics {
    fn status_tone(&self) -> &'static str {
        match self.readiness {
            ViewerReadinessState::Ready => "success",
            ViewerReadinessState::Loading => "muted",
            ViewerReadinessState::Degraded => "warning",
        }
    }
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
    fn active_projection(&self) -> Option<&GraphProjection> {
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

#[observed_only]
/// Load one deterministic viewer workspace from the typed viewer application service.
///
/// # Errors
///
/// Returns `ViewerModelError` when the underlying service cannot load the report or
/// graph projections needed to seed the portable UI workspace.
pub fn load_workspace_from_service(
    service: &impl ViewerApplicationService,
    harness_mode: HarnessMode,
) -> Result<ViewerWorkspace, ViewerModelError> {
    let report = ViewerReport::load(service)?;
    let first_scenario = report.scenario_summaries.first();
    let active_artifact = first_scenario.map(|scenario| scenario.artifact_id.clone());
    let active_branch = first_scenario
        .map(|scenario| scenario.summary.root_branch_id.clone())
        .unwrap_or_else(|| "root".to_string());
    let run_id = active_artifact
        .clone()
        .unwrap_or_else(|| "demo".to_string());

    let projections = load_projections(service, &run_id, &active_branch);
    let semantic_comparison = load_primary_comparison(service, &report);
    let counterexample =
        load_primary_counterexample(service, &report, semantic_comparison.as_ref());
    let minimization =
        load_primary_minimization(service, active_artifact.as_deref(), &active_branch);
    let sweeps = load_sweep_workspace(service, &report)?;
    let effects = load_effect_workspace(
        service,
        active_artifact.as_deref().unwrap_or("demo-run"),
        &active_branch,
    )?;
    let extensions = load_extensions(service)?;
    let insights = build_insights(
        first_scenario,
        active_artifact.as_ref(),
        &active_branch,
        &run_id,
        &projections,
        semantic_comparison,
        counterexample,
        minimization,
    );
    let diagnostics = build_publication_diagnostics(&report, harness_mode, active_artifact);

    Ok(ViewerWorkspace {
        report,
        graph: ViewerGraphWorkspace {
            layout: deterministic_layout(&projections),
            projections,
            active_projection: 0,
            active_branch,
            active_step: 0,
            selected_node: None,
            selected_edge: None,
            search_query: String::new(),
            search_results: Vec::new(),
            command_log: Vec::new(),
        },
        insights,
        sweeps,
        effects,
        extensions,
        diagnostics,
        pages: vec![
            ViewerPage::Overview,
            ViewerPage::Graph,
            ViewerPage::Insight,
            ViewerPage::Sweeps,
            ViewerPage::Effects,
        ],
    })
}

fn load_extensions(
    service: &impl ViewerApplicationService,
) -> Result<ViewerExtensionManifest, ViewerModelError> {
    match service.query(ViewerQuery::ExtensionManifest)? {
        ViewerQueryResult::ExtensionManifest { manifest } => Ok(*manifest),
        _ => Err(ViewerModelError::UnexpectedQueryShape {
            expected: "extension_manifest".to_string(),
        }),
    }
}

fn load_primary_comparison(
    service: &impl ViewerApplicationService,
    report: &ViewerReport,
) -> Option<SemanticComparisonResult> {
    let scenario_ids = report
        .scenario_summaries
        .iter()
        .map(|scenario| scenario.artifact_id.clone())
        .collect::<Vec<_>>();
    let [baseline_artifact_id, candidate_artifact_id, ..] = scenario_ids.as_slice() else {
        return None;
    };
    match service
        .query(ViewerQuery::SemanticComparison(SemanticComparisonRequest {
            baseline_artifact_id: baseline_artifact_id.clone(),
            candidate_artifact_id: candidate_artifact_id.clone(),
        }))
        .ok()?
    {
        ViewerQueryResult::SemanticComparison { comparison } => Some(*comparison),
        _ => None,
    }
}

fn load_primary_counterexample(
    service: &impl ViewerApplicationService,
    report: &ViewerReport,
    comparison: Option<&SemanticComparisonResult>,
) -> Option<TheoremAwareCounterexample> {
    if let Some(comparison) = comparison {
        let request = SemanticComparisonRequest {
            baseline_artifact_id: comparison.baseline_artifact_id.clone(),
            candidate_artifact_id: comparison.candidate_artifact_id.clone(),
        };
        if let Ok(ViewerQueryResult::Counterexample { counterexample }) =
            service.query(ViewerQuery::ComparisonCounterexample(request))
        {
            return Some(*counterexample);
        }
    }
    let artifact_id = report.scenario_summaries.first()?.artifact_id.clone();
    match service
        .query(ViewerQuery::ArtifactCounterexample { artifact_id })
        .ok()?
    {
        ViewerQueryResult::Counterexample { counterexample } => Some(*counterexample),
        _ => None,
    }
}

fn load_primary_minimization(
    service: &impl ViewerApplicationService,
    artifact_id: Option<&str>,
    branch_id: &str,
) -> Option<MinimizationResult> {
    let artifact_id = artifact_id?;
    let request_id = format!("minimize:{artifact_id}:{branch_id}");
    match service
        .query(ViewerQuery::Minimization { request_id })
        .ok()?
    {
        ViewerQueryResult::Minimization { result } => Some(*result),
        _ => None,
    }
}

fn load_sweep_workspace(
    service: &impl ViewerApplicationService,
    report: &ViewerReport,
) -> Result<SweepExplorerWorkspace, ViewerModelError> {
    let first = report
        .scenario_summaries
        .first()
        .ok_or_else(|| ViewerModelError::NotFound {
            kind: "scenario_summary".to_string(),
            id: "root".to_string(),
        })?;
    let sweep_id = format!("sweep/{}", first.summary.scenario_name);
    let explorer = match service.query(ViewerQuery::SweepExplorer(SweepExplorerRequest {
        sweep_id: sweep_id.clone(),
        filter_text: None,
        group_by: Some("theorem_profile".to_string()),
        max_results: Some(8),
    }))? {
        ViewerQueryResult::SweepExplorer { explorer } => *explorer,
        _ => {
            return Err(ViewerModelError::UnexpectedQueryShape {
                expected: "sweep_explorer".to_string(),
            });
        }
    };
    let suite_id = format!("suite/{}", first.summary.scenario_name);
    let suite = match service.query(ViewerQuery::ExperimentSuite {
        suite_id: suite_id.clone(),
    })? {
        ViewerQueryResult::ExperimentSuite { suite } => *suite,
        _ => {
            return Err(ViewerModelError::UnexpectedQueryShape {
                expected: "experiment_suite".to_string(),
            });
        }
    };
    Ok(SweepExplorerWorkspace {
        all_cases: explorer.visible_cases.clone(),
        explorer,
        suite,
        selected_case: None,
        active_filter: String::new(),
    })
}

fn load_effect_workspace(
    service: &impl ViewerApplicationService,
    artifact_id: &str,
    branch_id: &str,
) -> Result<EffectWorkspace, ViewerModelError> {
    match service.query(ViewerQuery::EffectTrace {
        artifact_id: artifact_id.to_string(),
        branch_id: branch_id.to_string(),
    })? {
        ViewerQueryResult::EffectTrace { effect_trace } => Ok(EffectWorkspace {
            effect_trace: *effect_trace,
            mock_command_log: Vec::new(),
        }),
        _ => Err(ViewerModelError::UnexpectedQueryShape {
            expected: "effect_trace".to_string(),
        }),
    }
}

fn load_projections(
    service: &impl ViewerApplicationService,
    run_id: &str,
    active_branch: &str,
) -> Vec<GraphProjection> {
    let mut projections = Vec::new();
    for kind in [
        GraphProjectionKind::ChoreographyStructure,
        GraphProjectionKind::InstantiatedProtocol,
        GraphProjectionKind::ExecutionTimeline,
        GraphProjectionKind::BranchLineage,
    ] {
        if let Ok(ViewerQueryResult::GraphProjection { projection }) =
            service.query(ViewerQuery::GraphProjection(GraphProjectionRequest {
                run_id: run_id.to_string(),
                branch_id: active_branch.to_string(),
                step: None,
                kind,
            }))
        {
            projections.push(projection);
        }
    }
    if projections.is_empty() {
        projections.push(GraphProjection {
            run_id: run_id.to_string(),
            branch_id: active_branch.to_string(),
            step: Some(0),
            kind: GraphProjectionKind::BranchLineage,
            nodes: Vec::new(),
            edges: Vec::new(),
        });
    }
    projections
}

fn build_insights(
    first_scenario: Option<&telltale_viewer::ViewerScenarioReport>,
    active_artifact: Option<&SelectedArtifactId>,
    active_branch: &str,
    run_id: &str,
    projections: &[GraphProjection],
    semantic_comparison: Option<SemanticComparisonResult>,
    counterexample: Option<TheoremAwareCounterexample>,
    minimization: Option<MinimizationResult>,
) -> RunInsightWorkspace {
    let total_steps = projections
        .iter()
        .flat_map(|projection| projection.nodes.iter().filter_map(|node| node.step))
        .max()
        .unwrap_or(0);
    RunInsightWorkspace {
        theorem_profile: first_scenario.map(|scenario| scenario.summary.theorem_profile.clone()),
        execution_regime: first_scenario.map(|scenario| match scenario.summary.execution_backend {
            ResolvedExecutionBackend::Canonical => ExecutionRegime::CanonicalExact,
            ResolvedExecutionBackend::Threaded => ExecutionRegime::ThreadedExact,
        }),
        semantic_comparison,
        counterexample,
        watch_expressions: build_watch_expressions(first_scenario),
        annotations: build_initial_annotations(active_artifact),
        provenance: BranchProvenance {
            run_id: run_id.to_string(),
            parent_branch: None,
            patch_count: 0,
            rerun_requested: false,
        },
        run_diff: RunDiffSnapshot {
            baseline_branch: "root".to_string(),
            candidate_branch: active_branch.to_string(),
            changed_steps: total_steps,
            command_count: 0,
        },
        causality: projections
            .iter()
            .find(|projection| projection.kind == GraphProjectionKind::ExecutionTimeline)
            .map(causality_from_projection)
            .unwrap_or_default(),
        bookmarks: vec![RunBookmark {
            branch_id: active_branch.to_string(),
            step: 0,
            label: "initial step".to_string(),
        }],
        archive_status: "loaded from artifact archive".to_string(),
        minimization,
    }
}

fn build_watch_expressions(
    first_scenario: Option<&telltale_viewer::ViewerScenarioReport>,
) -> Vec<WatchExpression> {
    first_scenario
        .map(|scenario| {
            vec![
                WatchExpression {
                    label: "sampled steps".to_string(),
                    value: scenario.summary.total_steps_sampled.to_string(),
                },
                WatchExpression {
                    label: "obs events".to_string(),
                    value: scenario.summary.total_obs_events.to_string(),
                },
            ]
        })
        .unwrap_or_default()
}

fn build_initial_annotations(active_artifact: Option<&SelectedArtifactId>) -> Vec<RunAnnotation> {
    active_artifact
        .map(|artifact_id| {
            vec![RunAnnotation {
                target: AnnotationTarget::Artifact(artifact_id.clone()),
                text: "Loaded through the typed viewer query surface.".to_string(),
            }]
        })
        .unwrap_or_default()
}

fn build_publication_diagnostics(
    report: &ViewerReport,
    harness_mode: HarnessMode,
    active_artifact: Option<SelectedArtifactId>,
) -> ViewerPublicationDiagnostics {
    ViewerPublicationDiagnostics {
        readiness: if report.artifacts.is_empty() {
            ViewerReadinessState::Loading
        } else {
            ViewerReadinessState::Ready
        },
        harness_mode,
        artifact_count: report.artifacts.len(),
        scenario_count: report.scenario_summaries.len(),
        active_page: ViewerPage::Overview,
        active_artifact,
    }
}

fn usize_to_i32(value: usize) -> i32 {
    i32::try_from(value).unwrap_or(i32::MAX)
}

fn deterministic_layout(projections: &[GraphProjection]) -> GraphLayoutState {
    let mut positions = BTreeMap::new();
    for projection in projections {
        let total = usize_to_i32(projection.nodes.len().max(1));
        for (index, node) in projection.nodes.iter().enumerate() {
            let index = usize_to_i32(index);
            positions.entry(node.id.clone()).or_insert(GraphNodeLayout {
                x: 80 + (index * 520 / total),
                y: 110 + ((index % 2) * 90),
            });
        }
    }
    GraphLayoutState { positions }
}

fn causality_from_projection(projection: &GraphProjection) -> Vec<CausalityEvent> {
    projection
        .nodes
        .iter()
        .filter_map(|node| {
            node.step.map(|step| CausalityEvent {
                step,
                label: node.label.clone(),
                detail: format!(
                    "projection node `{}` became visible at step {step}",
                    node.id
                ),
            })
        })
        .collect()
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

    fn projection_step_limit(&self) -> u64 {
        self.workspace
            .graph
            .active_projection()
            .and_then(|projection| projection.nodes.iter().filter_map(|node| node.step).max())
            .unwrap_or(0)
    }

    fn branch_lineage_projection_mut(&mut self) -> Option<&mut GraphProjection> {
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

#[observed_only]
#[component]
pub fn TelltaleUiRoot(workspace: ViewerWorkspace) -> Element {
    let mut state = use_signal(|| InteractiveViewerState::from_workspace(workspace));
    rsx! {
        InteractiveViewerFrame {
            state: state(),
            on_navigate: move |page| {
                let mut next = state();
                next.set_page(page);
                state.set(next);
            },
            on_select_projection: move |index| {
                let mut next = state();
                next.select_projection(index);
                state.set(next);
            },
            on_step_forward: move |_| {
                let mut next = state();
                next.step_forward();
                state.set(next);
            },
            on_step_backward: move |_| {
                let mut next = state();
                next.step_backward();
                state.set(next);
            },
            on_jump_to_step: move |step| {
                let mut next = state();
                next.jump_to_step(step);
                state.set(next);
            },
            on_fork_branch: move |_| {
                let mut next = state();
                next.fork_branch_from_current_step();
                state.set(next);
            },
            on_update_branch: move |_| {
                let mut next = state();
                next.update_active_branch();
                state.set(next);
            },
            on_delete_branch: move |_| {
                let mut next = state();
                next.delete_active_branch();
                state.set(next);
            },
            on_search: move |query: String| {
                let mut next = state();
                next.search(&query);
                state.set(next);
            },
            on_reload_archive: move |_| {
                let mut next = state();
                next.reload_archive();
                state.set(next);
            },
            on_add_bookmark: move |_| {
                let mut next = state();
                next.add_bookmark();
                state.set(next);
            },
            on_filter_sweeps: move |needle: String| {
                let mut next = state();
                next.filter_sweeps(&needle);
                state.set(next);
            },
            on_drill_sweep_case: move |case_id: String| {
                let mut next = state();
                next.drill_into_sweep_case(&case_id);
                state.set(next);
            },
            on_request_mocked_rerun: move |_| {
                let mut next = state();
                next.request_mocked_rerun();
                state.set(next);
            },
            on_request_minimization: move |_| {
                let mut next = state();
                next.request_minimization();
                state.set(next);
            },
        }
    }
}

#[observed_only]
#[component]
fn InteractiveViewerFrame(
    state: InteractiveViewerState,
    on_navigate: EventHandler<ViewerPage>,
    on_select_projection: EventHandler<usize>,
    on_step_forward: EventHandler<()>,
    on_step_backward: EventHandler<()>,
    on_jump_to_step: EventHandler<u64>,
    on_fork_branch: EventHandler<()>,
    on_update_branch: EventHandler<()>,
    on_delete_branch: EventHandler<()>,
    on_search: EventHandler<String>,
    on_reload_archive: EventHandler<()>,
    on_add_bookmark: EventHandler<()>,
    on_filter_sweeps: EventHandler<String>,
    on_drill_sweep_case: EventHandler<String>,
    on_request_mocked_rerun: EventHandler<()>,
    on_request_minimization: EventHandler<()>,
) -> Element {
    rsx! {
        ViewerFrame {
            workspace: state.workspace.clone(),
            active_page: state.active_page,
            on_navigate,
        }
        if matches!(state.active_page, ViewerPage::Graph) {
            GraphControlsOverlay {
                state: state.clone(),
                on_select_projection,
                on_step_forward,
                on_step_backward,
                on_jump_to_step,
                on_fork_branch,
                on_update_branch,
                on_delete_branch,
                on_search,
            }
        }
        if matches!(state.active_page, ViewerPage::Insight) {
            InsightControlsOverlay {
                state: state.clone(),
                on_reload_archive,
                on_add_bookmark,
            }
        }
        if matches!(state.active_page, ViewerPage::Sweeps) {
            SweepControlsOverlay {
                state: state.clone(),
                on_filter_sweeps,
                on_drill_sweep_case,
            }
        }
        if matches!(state.active_page, ViewerPage::Effects) {
            EffectControlsOverlay {
                state,
                on_request_mocked_rerun,
                on_request_minimization,
            }
        }
    }
}

#[observed_only]
#[component]
pub fn ViewerFrame(
    workspace: ViewerWorkspace,
    active_page: ViewerPage,
    on_navigate: EventHandler<ViewerPage>,
) -> Element {
    let publication = ViewerPublicationDiagnostics {
        active_page,
        ..workspace.diagnostics.clone()
    };
    let shell_mode = match publication.harness_mode {
        HarnessMode::Normal => "normal",
        HarnessMode::Deterministic => "deterministic",
    };
    rsx! {
        main {
            id: "tt-app-shell",
            class: "tt-shell",
            "data-harness-mode": "{shell_mode}",
            "data-readiness": "{publication.readiness.label()}",
            div {
                class: "tt-shell__sidebar",
                ScrollArea {
                    ScrollAreaViewport {
                        SidebarControls { workspace: workspace.clone(), publication: publication.clone() }
                    }
                }
            }
            div {
                class: "tt-shell__main",
                TopNav { pages: workspace.pages.clone(), active_page, on_navigate }
                section {
                    class: "tt-shell__content",
                    ScrollArea {
                        ScrollAreaViewport {
                            match active_page {
                                ViewerPage::Overview => rsx! { OverviewPage { workspace: workspace.clone() } },
                                ViewerPage::Graph => rsx! { GraphPage { workspace: workspace.clone() } },
                                ViewerPage::Insight => rsx! { InsightPage { workspace: workspace.clone() } },
                                ViewerPage::Sweeps => rsx! { SweepsPage { workspace: workspace.clone() } },
                                ViewerPage::Effects => rsx! { EffectsPage { workspace: workspace.clone() } },
                            }
                        }
                    }
                }
            }
        }
    }
}

#[component]
fn SidebarControls(
    workspace: ViewerWorkspace,
    publication: ViewerPublicationDiagnostics,
) -> Element {
    let active_artifact = publication
        .active_artifact
        .clone()
        .unwrap_or_else(|| "none".to_string());
    rsx! {
        Panel {
            title: "Viewer",
            subtitle: "Reusable simulator shell",
            children: rsx! {
                StatusBadge {
                    tone: publication.status_tone(),
                    label: format!("{} / {} scenarios", publication.artifact_count, publication.scenario_count)
                }
                InspectorSection {
                    title: "Selection".to_string(),
                    children: rsx! {
                        KeyValueLine { label: "Page".to_string(), value: publication.active_page.label().to_string() }
                        KeyValueLine { label: "Artifact".to_string(), value: active_artifact }
                    }
                }
                InspectorSection {
                    title: "Artifacts".to_string(),
                    children: rsx! {
                        for artifact in workspace.report.artifacts.iter().take(5) {
                            div { class: "tt-list-row", "{artifact.label}" }
                        }
                    }
                }
            }
        }
    }
}

#[component]
fn TopNav(
    pages: Vec<ViewerPage>,
    active_page: ViewerPage,
    on_navigate: EventHandler<ViewerPage>,
) -> Element {
    rsx! {
        nav {
            id: "tt-top-nav",
            class: "tt-top-nav",
            Toolbar {
                label: "Navigation",
                children: rsx! {
                    for page in pages {
                        button {
                            class: if page == active_page { "tt-nav-btn tt-nav-btn--active" } else { "tt-nav-btn" },
                            onclick: move |_| on_navigate.call(page),
                            "{page.label()}"
                        }
                    }
                }
            }
        }
    }
}

#[component]
fn OverviewPage(workspace: ViewerWorkspace) -> Element {
    let overview_extensions = workspace
        .extensions
        .descriptors
        .iter()
        .filter(|descriptor| descriptor.slot == ViewerExtensionSlot::OverviewPanel)
        .cloned()
        .collect::<Vec<ViewerExtensionDescriptor>>();
    rsx! {
        div {
            class: "tt-page-grid",
            Panel {
                title: "Artifact Inventory",
                subtitle: "Typed query surface summaries",
                children: rsx! {
                    for artifact in &workspace.report.artifacts {
                        Card {
                            title: artifact.label.clone(),
                            subtitle: format!("{:?}", artifact.kind),
                            children: rsx! {}
                        }
                    }
                }
            }
            Panel {
                title: "Scenario Summaries",
                subtitle: "Canonical report model",
                children: rsx! {
                    for scenario in &workspace.report.scenario_summaries {
                        ScenarioSummaryCard { scenario: scenario.summary.clone() }
                    }
                }
            }
            if !overview_extensions.is_empty() {
                Panel {
                    title: "Downstream Extensions",
                    subtitle: "Portable overlay slots for downstream consumers",
                    children: rsx! {
                        for descriptor in overview_extensions {
                            div { class: "tt-note", "{descriptor.title}: {descriptor.summary}" }
                        }
                    }
                }
            }
        }
    }
}

#[component]
fn ScenarioSummaryCard(scenario: ScenarioBundleSummary) -> Element {
    rsx! {
        Card {
            title: scenario.scenario_name.clone(),
            subtitle: format!("{:?}", scenario.execution_backend),
            children: rsx! {
                div { class: "tt-card__metric", "Steps sampled: {scenario.total_steps_sampled}" }
                div { class: "tt-card__metric", "Obs events: {scenario.total_obs_events}" }
                div { class: "tt-card__metric", "Effect events: {scenario.total_effect_events}" }
            }
        }
    }
}

#[observed_only]
#[component]
fn GraphPage(workspace: ViewerWorkspace) -> Element {
    let graph_extensions = workspace
        .extensions
        .descriptors
        .iter()
        .filter(|descriptor| descriptor.slot == ViewerExtensionSlot::GraphAnnotation)
        .cloned()
        .collect::<Vec<ViewerExtensionDescriptor>>();
    let projection = workspace
        .graph
        .active_projection()
        .cloned()
        .unwrap_or(GraphProjection {
            run_id: "empty".to_string(),
            branch_id: "root".to_string(),
            step: Some(0),
            kind: GraphProjectionKind::BranchLineage,
            nodes: Vec::new(),
            edges: Vec::new(),
        });
    rsx! {
        div {
            class: "tt-page-grid tt-page-grid--wide",
            Panel {
                title: "Graph Workspace",
                subtitle: format!(
                    "{:?} / branch {} / step {}",
                    projection.kind, workspace.graph.active_branch, workspace.graph.active_step
                ),
                children: rsx! {
                    GraphCanvas {
                        projection: projection.clone(),
                        active_step: workspace.graph.active_step,
                        layout: workspace.graph.layout.clone(),
                    }
                    if !workspace.graph.search_query.is_empty() {
                        InspectorSection {
                            title: format!("Search: {}", workspace.graph.search_query),
                            children: rsx! {
                                for hit in &workspace.graph.search_results {
                                    div { class: "tt-list-row", "{hit.label} [{hit.detail}]" }
                                }
                            }
                        }
                    }
                }
            }
            Panel {
                title: "Projection Catalog",
                subtitle: "Deterministic graph inputs",
                children: rsx! {
                    for item in &workspace.graph.projections {
                        Card {
                            title: format!("{:?}", item.kind),
                            subtitle: format!("{} nodes / {} edges", item.nodes.len(), item.edges.len()),
                            children: rsx! {
                                div { class: "tt-card__metric", "run: {item.run_id}" }
                                div { class: "tt-card__metric", "branch: {item.branch_id}" }
                                div { class: "tt-card__metric", "step cap: {item.nodes.iter().filter_map(|node| node.step).max().unwrap_or(0)}" }
                            }
                        }
                    }
                }
            }
            Panel {
                title: "Command Log",
                subtitle: "Typed branch commands emitted by the graph workspace",
                children: rsx! {
                    for command in &workspace.graph.command_log {
                        div { class: "tt-list-row", "{command:?}" }
                    }
                }
            }
            if !graph_extensions.is_empty() {
                Panel {
                    title: "Graph Extensions",
                    subtitle: "Downstream graph annotations and badges",
                    children: rsx! {
                        for descriptor in graph_extensions {
                            div { class: "tt-note", "{descriptor.title}: {descriptor.summary}" }
                        }
                    }
                }
            }
        }
    }
}

#[component]
fn GraphCanvas(projection: GraphProjection, active_step: u64, layout: GraphLayoutState) -> Element {
    let visible_nodes = projection
        .nodes
        .iter()
        .filter(|node| node.step.map_or(true, |step| step <= active_step))
        .cloned()
        .collect::<Vec<_>>();
    let visible_edges = projection
        .edges
        .iter()
        .filter(|edge| edge.step.map_or(true, |step| step <= active_step))
        .cloned()
        .collect::<Vec<_>>();
    let total = usize_to_i32(visible_nodes.len().max(1));
    rsx! {
        div {
            class: "tt-graph-shell",
            svg {
                class: "tt-graph",
                view_box: "0 0 640 320",
                for (index, edge) in visible_edges.iter().enumerate().map(|(index, edge)| (usize_to_i32(index), edge)) {
                    line {
                        key: "{index}",
                        x1: "{layout.positions.get(&edge.from).map(|point| point.x).unwrap_or(60 + (index * 90) % 520)}",
                        y1: "{layout.positions.get(&edge.from).map(|point| point.y).unwrap_or(60 + (index * 40) % 180)}",
                        x2: "{layout.positions.get(&edge.to).map(|point| point.x).unwrap_or(150 + (index * 90) % 520)}",
                        y2: "{layout.positions.get(&edge.to).map(|point| point.y).unwrap_or(120 + (index * 40) % 180)}",
                        class: "tt-graph__edge",
                    }
                    text {
                        x: "{100 + (index * 90) % 520}",
                        y: "{82 + (index * 40) % 180}",
                        class: "tt-graph__edge-label",
                        "{edge.label}"
                    }
                }
                for (index, node) in visible_nodes.iter().enumerate().map(|(index, node)| (usize_to_i32(index), node)) {
                    circle {
                        key: "{node.id}",
                        cx: "{layout.positions.get(&node.id).map(|point| point.x).unwrap_or(80 + (index * 520 / total))}",
                        cy: "{layout.positions.get(&node.id).map(|point| point.y).unwrap_or(110 + ((index % 2) * 90))}",
                        r: "24",
                        class: "tt-graph__node"
                    }
                    text {
                        x: "{layout.positions.get(&node.id).map(|point| point.x - 28).unwrap_or(52 + (index * 520 / total))}",
                        y: "{layout.positions.get(&node.id).map(|point| point.y + 4).unwrap_or(114 + ((index % 2) * 90))}",
                        class: "tt-graph__node-label",
                        "{node.label}"
                    }
                }
            }
        }
    }
}

#[observed_only]
#[component]
fn InsightPage(workspace: ViewerWorkspace) -> Element {
    let insight_extensions = workspace
        .extensions
        .descriptors
        .iter()
        .filter(|descriptor| {
            matches!(
                descriptor.slot,
                ViewerExtensionSlot::InsightPanel | ViewerExtensionSlot::TimeTravelPanel
            )
        })
        .cloned()
        .collect::<Vec<ViewerExtensionDescriptor>>();
    rsx! {
        div {
            class: "tt-page-grid",
            Panel {
                title: "Regime",
                subtitle: "Execution and theorem profile",
                children: rsx! {
                    KeyValueLine {
                        label: "Execution regime".to_string(),
                        value: workspace
                            .insights
                            .execution_regime
                            .map(|regime| format!("{regime:?}"))
                            .unwrap_or_else(|| "unknown".to_string())
                    }
                    KeyValueLine {
                        label: "Theorem scheduler".to_string(),
                        value: workspace
                            .insights
                            .theorem_profile
                            .as_ref()
                            .map(|profile| format!("{:?}", profile.scheduler_profile))
                            .unwrap_or_else(|| "none".to_string())
                    }
                }
            }
            Panel {
                title: "Watch Expressions",
                subtitle: "Pinned semantic facts",
                children: rsx! {
                    for watch in &workspace.insights.watch_expressions {
                        KeyValueLine { label: watch.label.clone(), value: watch.value.clone() }
                    }
                }
            }
            Panel {
                title: "Provenance",
                subtitle: "Branch lineage and notes",
                children: rsx! {
                    KeyValueLine { label: "Run".to_string(), value: workspace.insights.provenance.run_id.clone() }
                    KeyValueLine { label: "Patches".to_string(), value: workspace.insights.provenance.patch_count.to_string() }
                    KeyValueLine { label: "Archive".to_string(), value: workspace.insights.archive_status.clone() }
                    for annotation in &workspace.insights.annotations {
                        div { class: "tt-note", "{annotation.text}" }
                    }
                }
            }
            Panel {
                title: "Run Diff",
                subtitle: "Baseline vs active branch",
                children: rsx! {
                    KeyValueLine { label: "Baseline".to_string(), value: workspace.insights.run_diff.baseline_branch.clone() }
                    KeyValueLine { label: "Candidate".to_string(), value: workspace.insights.run_diff.candidate_branch.clone() }
                    KeyValueLine { label: "Changed steps".to_string(), value: workspace.insights.run_diff.changed_steps.to_string() }
                    KeyValueLine { label: "Command count".to_string(), value: workspace.insights.run_diff.command_count.to_string() }
                    if let Some(comparison) = &workspace.insights.semantic_comparison {
                        KeyValueLine { label: "Semantic relation".to_string(), value: format!("{:?}", comparison.relation) }
                        KeyValueLine { label: "Comparison summary".to_string(), value: comparison.summary.clone() }
                    }
                }
            }
            Panel {
                title: "Causality",
                subtitle: "Visible outcome explanation chain",
                children: rsx! {
                    for event in &workspace.insights.causality {
                        div { class: "tt-note", "{event.step}: {event.label} [{event.detail}]" }
                    }
                }
            }
            Panel {
                title: "Bookmarks",
                subtitle: "Pinned branches and historical steps",
                children: rsx! {
                    for bookmark in &workspace.insights.bookmarks {
                        div { class: "tt-note", "{bookmark.label}" }
                    }
                }
            }
            Panel {
                title: "Counterexample",
                subtitle: "Theorem-aware semantic evidence",
                children: rsx! {
                    if let Some(counterexample) = &workspace.insights.counterexample {
                        KeyValueLine { label: "Summary".to_string(), value: counterexample.summary.clone() }
                        KeyValueLine {
                            label: "Failed assumption".to_string(),
                            value: counterexample
                                .first_failed_assumption
                                .clone()
                                .unwrap_or_else(|| "none".to_string())
                        }
                        if let Some(divergence) = &counterexample.divergence {
                            div { class: "tt-note", "{divergence.label}: {divergence.baseline_detail} -> {divergence.candidate_detail}" }
                        }
                    } else {
                        div { class: "tt-note", "No counterexample loaded." }
                    }
                }
            }
            Panel {
                title: "Minimization",
                subtitle: "Reduced deterministic witness",
                children: rsx! {
                    if let Some(minimization) = &workspace.insights.minimization {
                        KeyValueLine { label: "Summary".to_string(), value: minimization.summary.clone() }
                        KeyValueLine { label: "Minimized steps".to_string(), value: minimization.minimized_steps.to_string() }
                    } else {
                        div { class: "tt-note", "No minimization request loaded." }
                    }
                }
            }
            if !insight_extensions.is_empty() {
                Panel {
                    title: "Extension Panels",
                    subtitle: "Downstream overlays without shell forks",
                    children: rsx! {
                        for descriptor in insight_extensions {
                            div { class: "tt-note", "{descriptor.title}: {descriptor.summary}" }
                        }
                    }
                }
            }
        }
    }
}

#[observed_only]
#[component]
fn SweepsPage(workspace: ViewerWorkspace) -> Element {
    rsx! {
        div {
            class: "tt-page-grid tt-page-grid--wide",
            Panel {
                title: "Sweep Explorer",
                subtitle: "Filtering, outliers, and drill-down over deterministic result sets",
                children: rsx! {
                    KeyValueLine { label: "Sweep".to_string(), value: workspace.sweeps.explorer.sweep_id.clone() }
                    KeyValueLine { label: "Visible cases".to_string(), value: workspace.sweeps.explorer.visible_cases.len().to_string() }
                    KeyValueLine { label: "Outliers".to_string(), value: workspace.sweeps.explorer.outlier_case_ids.len().to_string() }
                    for case in &workspace.sweeps.explorer.visible_cases {
                        div { class: "tt-note", "{case.case_id} [{case.artifact_id}]" }
                    }
                }
            }
            Panel {
                title: "Suite Baselines",
                subtitle: "Baseline-vs-candidate regression reporting",
                children: rsx! {
                    KeyValueLine { label: "Suite".to_string(), value: workspace.sweeps.suite.definition.suite_id.clone() }
                    for case in &workspace.sweeps.suite.cases {
                        div { class: "tt-note", "{case.case_id}: {case.threshold_passed}" }
                    }
                }
            }
        }
    }
}

#[observed_only]
#[component]
fn EffectsPage(workspace: ViewerWorkspace) -> Element {
    rsx! {
        div {
            class: "tt-page-grid tt-page-grid--wide",
            Panel {
                title: "Effect Trace",
                subtitle: "Typed requests, resolutions, and replay-visible outcomes",
                children: rsx! {
                    KeyValueLine { label: "Artifact".to_string(), value: workspace.effects.effect_trace.artifact_id.clone() }
                    KeyValueLine { label: "Branch".to_string(), value: workspace.effects.effect_trace.branch_id.clone() }
                    for entry in &workspace.effects.effect_trace.entries {
                        div { class: "tt-note", "{entry.step}: {entry.kind} [{entry.detail}]" }
                    }
                }
            }
            Panel {
                title: "Effect Overrides",
                subtitle: "Mocked rerun commands attached to this branch",
                children: rsx! {
                    for override_spec in &workspace.effects.effect_trace.overrides {
                        div { class: "tt-note", "{override_spec.operation}: {override_spec.mode:?}" }
                    }
                    for command in &workspace.effects.mock_command_log {
                        div { class: "tt-note", "{command}" }
                    }
                }
            }
        }
    }
}

#[observed_only]
#[component]
fn GraphControlsOverlay(
    state: InteractiveViewerState,
    on_select_projection: EventHandler<usize>,
    on_step_forward: EventHandler<()>,
    on_step_backward: EventHandler<()>,
    on_jump_to_step: EventHandler<u64>,
    on_fork_branch: EventHandler<()>,
    on_update_branch: EventHandler<()>,
    on_delete_branch: EventHandler<()>,
    on_search: EventHandler<String>,
) -> Element {
    let max_step = state.projection_step_limit();
    rsx! {
        section {
            class: "tt-shell__overlay",
            div {
                class: "tt-page-grid",
                Panel {
                    title: "Time Travel",
                    subtitle: "Deterministic replay stepping",
                    children: rsx! {
                        Toolbar {
                            label: "History",
                            children: rsx! {
                                button { class: "tt-nav-btn", onclick: move |_| on_step_backward.call(()), "Step -" }
                                button { class: "tt-nav-btn", onclick: move |_| on_step_forward.call(()), "Step +" }
                                for step in 0..=max_step {
                                    button {
                                        class: if step == state.workspace.graph.active_step { "tt-nav-btn tt-nav-btn--active" } else { "tt-nav-btn" },
                                        onclick: move |_| on_jump_to_step.call(step),
                                        "{step}"
                                    }
                                }
                            }
                        }
                    }
                }
                Panel {
                    title: "Projection Switcher",
                    subtitle: "Graph views over one authoritative run",
                    children: rsx! {
                        for (index, projection) in state.workspace.graph.projections.iter().enumerate() {
                            button {
                                class: if index == state.workspace.graph.active_projection { "tt-nav-btn tt-nav-btn--active" } else { "tt-nav-btn" },
                                onclick: move |_| on_select_projection.call(index),
                                "{projection.kind:?}"
                            }
                        }
                    }
                }
                Panel {
                    title: "Branch Commands",
                    subtitle: "Typed branch/scenario patch emission",
                    children: rsx! {
                        Toolbar {
                            label: "Branch",
                            children: rsx! {
                                button { class: "tt-nav-btn", onclick: move |_| on_fork_branch.call(()), "Fork Here" }
                                button { class: "tt-nav-btn", onclick: move |_| on_update_branch.call(()), "Update Branch" }
                                button { class: "tt-nav-btn", onclick: move |_| on_delete_branch.call(()), "Delete Branch" }
                            }
                        }
                    }
                }
                Panel {
                    title: "Search",
                    subtitle: "Node, role, and branch lookup",
                    children: rsx! {
                        Toolbar {
                            label: "Lookup",
                            children: rsx! {
                                button { class: "tt-nav-btn", onclick: move |_| on_search.call("alpha".to_string()), "Find alpha" }
                                button { class: "tt-nav-btn", onclick: move |_| on_search.call("branch".to_string()), "Find branch" }
                            }
                        }
                    }
                }
            }
        }
    }
}

#[observed_only]
#[component]
fn InsightControlsOverlay(
    state: InteractiveViewerState,
    on_reload_archive: EventHandler<()>,
    on_add_bookmark: EventHandler<()>,
) -> Element {
    rsx! {
        section {
            class: "tt-shell__overlay",
            div {
                class: "tt-page-grid",
                Panel {
                    title: "Archive Controls",
                    subtitle: "Reload exact artifact sets and fork new runs",
                    children: rsx! {
                        Toolbar {
                            label: "Archive",
                            children: rsx! {
                                button { class: "tt-nav-btn", onclick: move |_| on_reload_archive.call(()), "Reload Archive" }
                                button { class: "tt-nav-btn", onclick: move |_| on_add_bookmark.call(()), "Bookmark Step" }
                            }
                        }
                    }
                }
                Panel {
                    title: "Active Branch",
                    subtitle: "Insight focus",
                    children: rsx! {
                        KeyValueLine { label: "Branch".to_string(), value: state.workspace.graph.active_branch.clone() }
                        KeyValueLine { label: "Step".to_string(), value: state.workspace.graph.active_step.to_string() }
                    }
                }
            }
        }
    }
}

#[observed_only]
#[component]
fn SweepControlsOverlay(
    state: InteractiveViewerState,
    on_filter_sweeps: EventHandler<String>,
    on_drill_sweep_case: EventHandler<String>,
) -> Element {
    let first_case_id = state
        .workspace
        .sweeps
        .explorer
        .visible_cases
        .first()
        .map(|case| case.case_id.clone());
    rsx! {
        section {
            class: "tt-shell__overlay",
            div {
                class: "tt-page-grid",
                Panel {
                    title: "Sweep Controls",
                    subtitle: "Filter, outliers, and drill-down",
                    children: rsx! {
                        Toolbar {
                            label: "Sweep",
                            children: rsx! {
                                button { class: "tt-nav-btn", onclick: move |_| on_filter_sweeps.call("baseline".to_string()), "Filter baseline" }
                                button { class: "tt-nav-btn", onclick: move |_| on_filter_sweeps.call(String::new()), "Clear Filter" }
                                if let Some(case_id) = first_case_id.clone() {
                                    button {
                                        class: "tt-nav-btn",
                                        onclick: move |_| on_drill_sweep_case.call(case_id.clone()),
                                        "Open {case_id}"
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

#[observed_only]
#[component]
fn EffectControlsOverlay(
    state: InteractiveViewerState,
    on_request_mocked_rerun: EventHandler<()>,
    on_request_minimization: EventHandler<()>,
) -> Element {
    rsx! {
        section {
            class: "tt-shell__overlay",
            div {
                class: "tt-page-grid",
                Panel {
                    title: "Effect Commands",
                    subtitle: "Mocked reruns and witness reduction",
                    children: rsx! {
                        Toolbar {
                            label: "Effects",
                            children: rsx! {
                                button { class: "tt-nav-btn", onclick: move |_| on_request_mocked_rerun.call(()), "Mock Rerun" }
                                button { class: "tt-nav-btn", onclick: move |_| on_request_minimization.call(()), "Minimize" }
                            }
                        }
                    }
                }
                Panel {
                    title: "Active Target",
                    subtitle: "Effect scope",
                    children: rsx! {
                        KeyValueLine { label: "Artifact".to_string(), value: state.workspace.effects.effect_trace.artifact_id.clone() }
                        KeyValueLine { label: "Branch".to_string(), value: state.workspace.effects.effect_trace.branch_id.clone() }
                    }
                }
            }
        }
    }
}

#[component]
fn Panel(title: String, subtitle: String, children: Element) -> Element {
    rsx! {
        ShadCard {
            class: Some("tt-panel".to_string()),
            div {
                class: "tt-panel__header",
                h2 { class: "tt-panel__title", "{title}" }
                p { class: "tt-panel__subtitle", "{subtitle}" }
            }
            div { class: "tt-panel__body", {children} }
        }
    }
}

#[component]
fn Card(title: String, subtitle: String, children: Element) -> Element {
    rsx! {
        ShadCard {
            class: Some("tt-card".to_string()),
            h3 { class: "tt-card__title", "{title}" }
            p { class: "tt-card__subtitle", "{subtitle}" }
            div { class: "tt-card__body", {children} }
        }
    }
}

#[component]
fn Toolbar(label: &'static str, children: Element) -> Element {
    rsx! {
        div {
            class: "tt-toolbar",
            span { class: "tt-toolbar__label", "{label}" }
            div { class: "tt-toolbar__controls", {children} }
        }
    }
}

#[component]
fn InspectorSection(title: String, children: Element) -> Element {
    rsx! {
        section {
            class: "tt-inspector",
            h3 { class: "tt-inspector__title", "{title}" }
            div { class: "tt-inspector__body", {children} }
        }
    }
}

fn badge_variant(tone: &str) -> BadgeVariant {
    match tone {
        "success" => BadgeVariant::Default,
        "warning" => BadgeVariant::Outline,
        _ => BadgeVariant::Secondary,
    }
}

#[component]
fn StatusBadge(tone: &'static str, label: String) -> Element {
    rsx! {
        ShadBadge {
            variant: badge_variant(tone),
            class: Some(format!("tt-badge tt-badge--{tone}")),
            "{label}"
        }
    }
}

#[component]
fn KeyValueLine(label: String, value: String) -> Element {
    rsx! {
        div {
            class: "tt-key-value",
            span { class: "tt-key-value__label", "{label}" }
            span { class: "tt-key-value__value", "{value}" }
        }
    }
}

#[authoritative_source("viewer_demo_workspace")]
/// Build the deterministic demo workspace shown by the first shared viewer shell.
///
/// # Panics
///
/// Panics if the typed viewer service fails to load the built-in demo artifacts.
#[must_use]
pub fn demo_workspace() -> ViewerWorkspace {
    let service = demo_service();
    load_workspace_from_service(&service, HarnessMode::Deterministic)
        .expect("demo workspace should load through the typed viewer service")
}

fn demo_scenario() -> Scenario {
    Scenario {
        name: "demo_mesh".to_string(),
        roles: vec!["alpha".to_string(), "beta".to_string(), "gamma".to_string()],
        steps: 4,
        execution: telltale_simulator::scenario::ExecutionSpec {
            backend: ExecutionBackend::Canonical,
            scheduler_policy: telltale_simulator::scenario::SchedulerPolicySpec::Cooperative,
            scheduler_concurrency: Some(1),
            worker_threads: Some(1),
        },
        seed: 7,
        network: None,
        field: None,
        reconfigurations: Vec::new(),
        adversaries: Vec::new(),
        properties: None,
        checkpoint_interval: None,
        theorem: TheoremProfileSpec::default(),
        durability: DurabilitySpec::default(),
        extensions: BTreeMap::new(),
    }
}

fn demo_alternate_bundle() -> ViewerArtifactFile {
    let mut alternate_scenario = demo_scenario();
    alternate_scenario.name = "demo_mesh_alt".to_string();
    alternate_scenario.theorem = TheoremProfileSpec {
        assumption_bundle: TheoremAssumptionBundle::ObservedTransport,
        ..TheoremProfileSpec::default()
    };
    let mut alternate_result = sample_result();
    alternate_result
        .trace
        .records
        .push(telltale_simulator::trace::StepRecord {
            step: 3,
            role: "alpha".to_string(),
            state: Vec::new(),
        });
    alternate_result.stats.theorem_profile.assumption_bundle =
        TheoremAssumptionBundle::ObservedTransport;
    alternate_result.stats.theorem_profile.eligibility_reason =
        Some("observed transport is not theorem-exact".to_string());
    ViewerArtifactFile::new(ViewerArtifact::ScenarioBundle(Box::new(
        ScenarioBundleArtifact::new(
            Some(alternate_scenario),
            alternate_result,
            Some(ContractCheckReport::pass()),
        ),
    )))
}

fn import_demo_artifacts(service: &mut InMemoryViewerService) {
    let scenario_bundle = ViewerArtifactFile::new(ViewerArtifact::ScenarioBundle(Box::new(
        ScenarioBundleArtifact::new(
            Some(demo_scenario()),
            sample_result(),
            Some(ContractCheckReport::pass()),
        ),
    )));
    let decision_report = ViewerArtifactFile::new(ViewerArtifact::DecisionReport(DecisionReport {
        kind: DecisionKind::TheoremEligibility,
        outcome: DecisionOutcome::Certified(DecisionCertificate::TheoremEligibility {
            eligibility: TheoremEligibility::Exact,
        }),
    }));
    let environment_trace =
        ViewerArtifactFile::new(ViewerArtifact::EnvironmentTrace(EnvironmentTrace::default()));

    for (artifact_id, artifact, message) in [
        ("demo-run", scenario_bundle, "scenario bundle should import"),
        (
            "demo-run-alt",
            demo_alternate_bundle(),
            "alternate scenario bundle should import",
        ),
        (
            "demo-decision",
            decision_report,
            "decision report should import",
        ),
        (
            "demo-environment",
            environment_trace,
            "environment trace should import",
        ),
    ] {
        service
            .command(ViewerCommand::ImportArtifact {
                artifact_id: artifact_id.to_string(),
                artifact: Box::new(artifact),
            })
            .expect(message);
    }
}

fn configure_demo_sweep(service: &mut InMemoryViewerService) {
    service
        .command(ViewerCommand::ExecuteSweep {
            sweep_id: "sweep/demo_mesh".to_string(),
            baseline_artifact_id: Some("demo-run".to_string()),
            cases: vec![
                SweepCaseSpec {
                    case_id: "baseline".to_string(),
                    artifact_id: "demo-run".to_string(),
                    parameters: BTreeMap::from([("seed".to_string(), "7".to_string())]),
                },
                SweepCaseSpec {
                    case_id: "observed".to_string(),
                    artifact_id: "demo-run-alt".to_string(),
                    parameters: BTreeMap::from([(
                        "assumption_bundle".to_string(),
                        "observed_transport".to_string(),
                    )]),
                },
            ],
        })
        .expect("demo sweep should execute");
}

fn configure_demo_suite(service: &mut InMemoryViewerService) {
    service
        .command(ViewerCommand::ExecuteExperimentSuite {
            definition: ExperimentSuiteDefinition {
                suite_id: "suite/demo_mesh".to_string(),
                threshold: RegressionThreshold {
                    max_changed_steps: 0,
                    allow_normalization_only: true,
                },
                cases: vec![ExperimentSuiteCase {
                    case_id: "baseline-vs-observed".to_string(),
                    baseline_artifact_id: "demo-run".to_string(),
                    candidate_artifact_id: "demo-run-alt".to_string(),
                }],
            },
        })
        .expect("demo suite should execute");
}

fn configure_demo_effects_and_extensions(service: &mut InMemoryViewerService) {
    service
        .command(ViewerCommand::RequestMinimization {
            request: telltale_viewer::MinimizationRequest {
                request_id: "minimize:demo-run:root".to_string(),
                artifact_id: "demo-run".to_string(),
                branch_id: "root".to_string(),
                strategy: telltale_viewer::MinimizationStrategy::FirstDivergencePrefix,
            },
        })
        .expect("demo minimization should execute");
    service
        .command(mocked_rerun_command(
            "demo-run".to_string(),
            "root".to_string(),
            "ready",
        ))
        .expect("demo mocked rerun should queue");
    service
        .command(ViewerCommand::RegisterExtensions {
            manifest: ViewerExtensionManifest {
                descriptors: vec![
                    ViewerExtensionDescriptor {
                        id: "demo.overview.policy".to_string(),
                        title: "Policy Overlay".to_string(),
                        slot: ViewerExtensionSlot::OverviewPanel,
                        summary: "Downstream policies can add summary cards here.".to_string(),
                    },
                    ViewerExtensionDescriptor {
                        id: "demo.graph.annotations".to_string(),
                        title: "Graph Badges".to_string(),
                        slot: ViewerExtensionSlot::GraphAnnotation,
                        summary: "Domain-specific graph annotations belong in this slot."
                            .to_string(),
                    },
                    ViewerExtensionDescriptor {
                        id: "demo.insight.panel".to_string(),
                        title: "Insight Overlay".to_string(),
                        slot: ViewerExtensionSlot::InsightPanel,
                        summary: "Downstream reports can extend the insight page here.".to_string(),
                    },
                ],
            },
        })
        .expect("demo extensions should register");
}

fn demo_service() -> InMemoryViewerService {
    let mut service = InMemoryViewerService::new();
    import_demo_artifacts(&mut service);
    configure_demo_sweep(&mut service);
    configure_demo_suite(&mut service);
    configure_demo_effects_and_extensions(&mut service);
    service
}

fn sample_result() -> ScenarioResult {
    ScenarioResult {
        trace: Trace {
            records: vec![
                telltale_simulator::trace::StepRecord {
                    step: 0,
                    role: "alpha".to_string(),
                    state: Vec::new(),
                },
                telltale_simulator::trace::StepRecord {
                    step: 1,
                    role: "beta".to_string(),
                    state: Vec::new(),
                },
                telltale_simulator::trace::StepRecord {
                    step: 2,
                    role: "gamma".to_string(),
                    state: Vec::new(),
                },
            ],
        },
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
            semantic_objects: ProtocolMachineSemanticObjects::default(),
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
                productive_step_count: 3,
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
            reconfiguration_summary: ReconfigurationSummary::default(),
            environment_trace: EnvironmentTrace::default(),
            adversary_summary: AdversarySummary::default(),
            assumption_diagnostics: Vec::new(),
            durable_recovery: None,
            backend: ResolvedExecutionBackend::Canonical,
            scheduler_concurrency: 1,
            worker_threads: 1,
            rounds_executed: 3,
            final_tick: 3,
            total_obs_events: 0,
            total_invoked_events: 0,
            checkpoint_writes: 0,
            checkpoint_error: None,
        },
    }
}
