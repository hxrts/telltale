//! Portable Dioxus UI core for the Telltale simulator tooling webapp.
//!
//! This crate owns reusable layout, routing state, and rendering helpers while
//! keeping browser APIs in `telltale-web` and semantic artifact truth in
//! `telltale-viewer`.

#![allow(missing_docs)]

use dioxus::prelude::*;
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
    ExecutionBackend, ExecutionRegime, ResolvedExecutionBackend, ResolvedSchedulerPolicy,
    ResolvedTheoremProfile, Scenario, TheoremAssumptionBundle, TheoremEligibility,
    TheoremEnvelopeProfile, TheoremProfileSpec, TheoremSchedulerProfile,
};
use telltale_simulator::trace::Trace;
use telltale_viewer::{
    ArtifactId, BranchId, GraphProjection, GraphProjectionKind, GraphProjectionRequest,
    InMemoryViewerService, ScenarioBundleArtifact, ScenarioBundleSummary, ViewerApplicationService,
    ViewerArtifact, ViewerArtifactFile, ViewerCommand, ViewerModelError, ViewerQuery,
    ViewerQueryResult, ViewerReport,
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
}

impl ViewerPage {
    pub const fn label(self) -> &'static str {
        match self {
            Self::Overview => "Artifacts",
            Self::Graph => "Graphs",
            Self::Insight => "Insights",
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
}

impl ViewerGraphWorkspace {
    fn active_projection(&self) -> Option<&GraphProjection> {
        self.projections.get(self.active_projection)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RunInsightWorkspace {
    pub theorem_profile: Option<ResolvedTheoremProfile>,
    pub execution_regime: Option<ExecutionRegime>,
    pub watch_expressions: Vec<WatchExpression>,
    pub annotations: Vec<RunAnnotation>,
    pub provenance: BranchProvenance,
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
pub struct ViewerWorkspace {
    pub report: ViewerReport,
    pub graph: ViewerGraphWorkspace,
    pub insights: RunInsightWorkspace,
    pub diagnostics: ViewerPublicationDiagnostics,
    pub pages: Vec<ViewerPage>,
}

#[observed_only]
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

    let mut projections = Vec::new();
    for kind in [
        GraphProjectionKind::ChoreographyStructure,
        GraphProjectionKind::InstantiatedProtocol,
        GraphProjectionKind::ExecutionTimeline,
        GraphProjectionKind::BranchLineage,
    ] {
        if let Ok(ViewerQueryResult::GraphProjection { projection }) =
            service.query(ViewerQuery::GraphProjection(GraphProjectionRequest {
                run_id: run_id.clone(),
                branch_id: active_branch.clone(),
                step: None,
                kind,
            }))
        {
            projections.push(projection);
        }
    }
    if projections.is_empty() {
        projections.push(GraphProjection {
            run_id: run_id.clone(),
            branch_id: active_branch.clone(),
            step: Some(0),
            kind: GraphProjectionKind::BranchLineage,
            nodes: Vec::new(),
            edges: Vec::new(),
        });
    }

    let insights = RunInsightWorkspace {
        theorem_profile: first_scenario.map(|scenario| scenario.summary.theorem_profile.clone()),
        execution_regime: first_scenario.map(|scenario| match scenario.summary.execution_backend {
            ResolvedExecutionBackend::Canonical => ExecutionRegime::CanonicalExact,
            ResolvedExecutionBackend::Threaded => ExecutionRegime::ThreadedExact,
        }),
        watch_expressions: first_scenario
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
            .unwrap_or_default(),
        annotations: active_artifact
            .as_ref()
            .map(|artifact_id| {
                vec![RunAnnotation {
                    target: AnnotationTarget::Artifact(artifact_id.clone()),
                    text: "Loaded through the typed viewer query surface.".to_string(),
                }]
            })
            .unwrap_or_default(),
        provenance: BranchProvenance {
            run_id,
            parent_branch: None,
            patch_count: 0,
            rerun_requested: false,
        },
    };

    let diagnostics = ViewerPublicationDiagnostics {
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
    };

    Ok(ViewerWorkspace {
        report,
        graph: ViewerGraphWorkspace {
            projections,
            active_projection: 0,
            active_branch,
            active_step: 0,
            selected_node: None,
            selected_edge: None,
        },
        insights,
        diagnostics,
        pages: vec![ViewerPage::Overview, ViewerPage::Graph, ViewerPage::Insight],
    })
}

#[derive(Clone)]
pub struct ViewerTaskRuntime {
    spawn: Arc<dyn Fn(BoxedTask) + Send + Sync>,
}

impl ViewerTaskRuntime {
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
    pub fn new(runtime: ViewerTaskRuntime) -> Self {
        Self {
            runtime,
            labels: Arc::new(Mutex::new(Vec::new())),
        }
    }

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

#[component]
pub fn TelltaleUiRoot(workspace: ViewerWorkspace) -> Element {
    let mut active_page = use_signal(|| workspace.diagnostics.active_page);
    rsx! {
        ViewerFrame {
            workspace,
            active_page: active_page(),
            on_navigate: move |page| active_page.set(page),
        }
    }
}

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
                SidebarControls { workspace: workspace.clone(), publication: publication.clone() }
            }
            div {
                class: "tt-shell__main",
                TopNav { pages: workspace.pages.clone(), active_page, on_navigate }
                section {
                    class: "tt-shell__content",
                    match active_page {
                        ViewerPage::Overview => rsx! { OverviewPage { workspace: workspace.clone() } },
                        ViewerPage::Graph => rsx! { GraphPage { workspace: workspace.clone() } },
                        ViewerPage::Insight => rsx! { InsightPage { workspace: workspace.clone() } },
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

#[component]
fn GraphPage(workspace: ViewerWorkspace) -> Element {
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
                subtitle: format!("{:?} / branch {}", projection.kind, projection.branch_id),
                children: rsx! {
                    GraphCanvas { projection: projection.clone() }
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
                            }
                        }
                    }
                }
            }
        }
    }
}

#[component]
fn GraphCanvas(projection: GraphProjection) -> Element {
    let total = projection.nodes.len().max(1) as i32;
    rsx! {
        div {
            class: "tt-graph-shell",
            svg {
                class: "tt-graph",
                view_box: "0 0 640 320",
                for (index, edge) in projection.edges.iter().enumerate() {
                    line {
                        key: "{index}",
                        x1: "{60 + ((index as i32) * 90) % 520}",
                        y1: "{60 + ((index as i32) * 40) % 180}",
                        x2: "{150 + ((index as i32) * 90) % 520}",
                        y2: "{120 + ((index as i32) * 40) % 180}",
                        class: "tt-graph__edge",
                    }
                    text {
                        x: "{100 + ((index as i32) * 90) % 520}",
                        y: "{82 + ((index as i32) * 40) % 180}",
                        class: "tt-graph__edge-label",
                        "{edge.label}"
                    }
                }
                for (index, node) in projection.nodes.iter().enumerate() {
                    circle {
                        key: "{node.id}",
                        cx: "{80 + ((index as i32) * 520 / total)}",
                        cy: "{110 + (((index as i32) % 2) * 90)}",
                        r: "24",
                        class: "tt-graph__node"
                    }
                    text {
                        x: "{52 + ((index as i32) * 520 / total)}",
                        y: "{114 + (((index as i32) % 2) * 90)}",
                        class: "tt-graph__node-label",
                        "{node.label}"
                    }
                }
            }
        }
    }
}

#[component]
fn InsightPage(workspace: ViewerWorkspace) -> Element {
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
                    for annotation in &workspace.insights.annotations {
                        div { class: "tt-note", "{annotation.text}" }
                    }
                }
            }
        }
    }
}

#[component]
fn Panel(title: String, subtitle: String, children: Element) -> Element {
    rsx! {
        section {
            class: "tt-panel",
            header {
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
        article {
            class: "tt-card",
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

#[component]
fn StatusBadge(tone: &'static str, label: String) -> Element {
    rsx! {
        span { class: "tt-badge tt-badge--{tone}", "{label}" }
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
pub fn demo_workspace() -> ViewerWorkspace {
    let service = demo_service();
    load_workspace_from_service(&service, HarnessMode::Deterministic)
        .expect("demo workspace should load through the typed viewer service")
}

fn demo_service() -> InMemoryViewerService {
    let mut service = InMemoryViewerService::new();
    let scenario = Scenario {
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
        extensions: BTreeMap::new(),
    };
    let scenario_bundle =
        ViewerArtifactFile::new(ViewerArtifact::ScenarioBundle(ScenarioBundleArtifact::new(
            Some(scenario),
            sample_result(),
            Some(ContractCheckReport::pass()),
        )));
    let decision_report = ViewerArtifactFile::new(ViewerArtifact::DecisionReport(DecisionReport {
        kind: DecisionKind::TheoremEligibility,
        outcome: DecisionOutcome::Certified(DecisionCertificate::TheoremEligibility {
            eligibility: TheoremEligibility::Exact,
        }),
    }));
    let environment_trace =
        ViewerArtifactFile::new(ViewerArtifact::EnvironmentTrace(EnvironmentTrace::default()));

    service
        .command(ViewerCommand::ImportArtifact {
            artifact_id: "demo-run".to_string(),
            artifact: scenario_bundle,
        })
        .expect("scenario bundle should import");
    service
        .command(ViewerCommand::ImportArtifact {
            artifact_id: "demo-decision".to_string(),
            artifact: decision_report,
        })
        .expect("decision report should import");
    service
        .command(ViewerCommand::ImportArtifact {
            artifact_id: "demo-environment".to_string(),
            artifact: environment_trace,
        })
        .expect("environment trace should import");
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
