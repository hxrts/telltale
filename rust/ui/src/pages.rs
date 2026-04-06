//! Page components for the viewer content area.

use crate::components::*;
use crate::types::*;
use dioxus::prelude::*;
use dioxus_shadcn::components::separator::Separator;
use telltale_macros::observed_only;
use telltale_viewer::{
    GraphProjection, GraphProjectionKind, ScenarioBundleSummary, ViewerExtensionDescriptor,
    ViewerExtensionSlot,
};

#[component]
pub(crate) fn OverviewPage(workspace: ViewerWorkspace, on_select_artifact: EventHandler<String>) -> Element {
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
                    if workspace.report.artifacts.is_empty() {
                        EmptyState { message: "No artifacts loaded." }
                    }
                    for artifact in &workspace.report.artifacts {
                        {
                            let artifact_id = artifact.artifact_id.clone();
                            rsx! {
                                div {
                                    class: "cursor-pointer",
                                    onclick: move |_| on_select_artifact.call(artifact_id.clone()),
                                    Card {
                                        title: artifact.label.clone(),
                                        subtitle: format!("{:?}", artifact.kind),
                                        children: rsx! {
                                            KeyValueLine { label: "Kind".to_string(), value: format!("{:?}", artifact.kind) }
                                        }
                                    }
                                }
                            }
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
                            KeyValueLine { label: descriptor.title.clone(), value: descriptor.summary.clone() }
                        }
                    }
                }
            }
        }
    }
}

#[component]
pub(crate) fn ScenarioSummaryCard(scenario: ScenarioBundleSummary) -> Element {
    rsx! {
        Card {
            title: scenario.scenario_name.clone(),
            subtitle: format!("{:?}", scenario.execution_backend),
            children: rsx! {
                KeyValueLine { label: "Steps sampled".to_string(), value: scenario.total_steps_sampled.to_string() }
                KeyValueLine { label: "Obs events".to_string(), value: scenario.total_obs_events.to_string() }
                KeyValueLine { label: "Effect events".to_string(), value: scenario.total_effect_events.to_string() }
            }
        }
    }
}

#[observed_only]
#[component]
pub(crate) fn GraphPage(workspace: ViewerWorkspace) -> Element {
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
                    div {
                        class: "flex justify-end mb-2",
                        button {
                            r#type: "button",
                            class: "inline-flex h-7 items-center justify-center whitespace-nowrap rounded-sm border border-border bg-background px-3 text-xs font-sans font-medium leading-none text-foreground transition-colors hover:bg-accent hover:text-accent-foreground",
                            onclick: move |_| call_js("__tt_fit_graph", &[]),
                            "Re-center"
                        }
                    }
                    GraphCanvas {
                        projection: projection.clone(),
                        active_step: workspace.graph.active_step,
                        layout: workspace.graph.layout.clone(),
                    }
                    if !workspace.graph.search_query.is_empty() {
                        Separator {}
                        h3 {
                            class: "text-[0.625rem] font-sans font-semibold uppercase tracking-[0.08em] text-muted-foreground mb-2",
                            "Search: {workspace.graph.search_query}"
                        }
                        for hit in &workspace.graph.search_results {
                            KeyValueLine { label: hit.label.clone(), value: hit.detail.clone() }
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
                                KeyValueLine { label: "Run".to_string(), value: item.run_id.clone() }
                                KeyValueLine { label: "Branch".to_string(), value: item.branch_id.clone() }
                                KeyValueLine { label: "Step cap".to_string(), value: item.nodes.iter().filter_map(|node| node.step).max().unwrap_or(0).to_string() }
                            }
                        }
                    }
                }
            }
            Panel {
                title: "Command Log",
                subtitle: "Typed branch commands emitted by the graph workspace",
                children: rsx! {
                    if workspace.graph.command_log.is_empty() {
                        EmptyState { message: "No commands emitted." }
                    }
                    for (index, command) in workspace.graph.command_log.iter().enumerate() {
                        Card {
                            title: format!("#{index}"),
                            subtitle: String::new(),
                            children: rsx! {
                                CodeBlock { content: pretty_json(command) }
                            }
                        }
                    }
                }
            }
            if !graph_extensions.is_empty() {
                Panel {
                    title: "Graph Extensions",
                    subtitle: "Downstream graph annotations and badges",
                    children: rsx! {
                        for descriptor in graph_extensions {
                            KeyValueLine { label: descriptor.title.clone(), value: descriptor.summary.clone() }
                        }
                    }
                }
            }
        }
    }
}

#[component]
pub(crate) fn GraphCanvas(
    projection: GraphProjection,
    active_step: u64,
    layout: GraphLayoutState,
) -> Element {
    let container_id = "tt-cytoscape-container";

    use_effect({
        let projection = projection.clone();
        move || {
            call_js("__tt_init_graph", &[container_id]);

            #[derive(serde::Serialize)]
            struct JsNode {
                id: String,
                label: String,
                category: String,
                step: Option<u64>,
            }
            #[derive(serde::Serialize)]
            struct JsEdge {
                from: String,
                to: String,
                label: String,
                step: Option<u64>,
            }

            let nodes: Vec<JsNode> = projection
                .nodes
                .iter()
                .map(|n| JsNode {
                    id: n.id.clone(),
                    label: n.label.clone(),
                    category: n.category.clone(),
                    step: n.step,
                })
                .collect();
            let edges: Vec<JsEdge> = projection
                .edges
                .iter()
                .map(|e| JsEdge {
                    from: e.from.clone(),
                    to: e.to.clone(),
                    label: e.label.clone(),
                    step: e.step,
                })
                .collect();

            let nodes_json = serde_json::to_string(&nodes).unwrap_or_default();
            let edges_json = serde_json::to_string(&edges).unwrap_or_default();
            call_js("__tt_update_graph", &[&nodes_json, &edges_json]);
        }
    });

    use_effect({
        let step_str = active_step.to_string();
        move || {
            call_js("__tt_filter_graph_step", &[&step_str]);
        }
    });

    rsx! {
        div {
            id: "{container_id}",
            class: "tt-cytoscape",
        }
    }
}

#[observed_only]
#[component]
pub(crate) fn InsightPage(workspace: ViewerWorkspace) -> Element {
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
                        p { class: "text-xs text-muted-foreground py-0.5", "{annotation.text}" }
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
                    if workspace.insights.causality.is_empty() {
                        EmptyState { message: "No causality events." }
                    }
                    for event in &workspace.insights.causality {
                        KeyValueLine { label: format!("Step {}", event.step), value: event.label.clone() }
                    }
                }
            }
            Panel {
                title: "Bookmarks",
                subtitle: "Pinned branches and historical steps",
                children: rsx! {
                    if workspace.insights.bookmarks.is_empty() {
                        EmptyState { message: "No bookmarks." }
                    }
                    for bookmark in &workspace.insights.bookmarks {
                        KeyValueLine { label: format!("Step {}", bookmark.step), value: bookmark.label.clone() }
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
                            Card {
                                title: divergence.label.clone(),
                                subtitle: "baseline -> candidate".to_string(),
                                children: rsx! {
                                    CodeBlock { content: format!("{}\n---\n{}", pretty_json(&divergence.baseline_detail), pretty_json(&divergence.candidate_detail)) }
                                }
                            }
                        }
                    } else {
                        EmptyState { message: "No counterexample loaded." }
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
                        EmptyState { message: "No minimization request." }
                    }
                }
            }
            if !insight_extensions.is_empty() {
                Panel {
                    title: "Extension Panels",
                    subtitle: "Downstream overlays without shell forks",
                    children: rsx! {
                        for descriptor in insight_extensions {
                            KeyValueLine { label: descriptor.title.clone(), value: descriptor.summary.clone() }
                        }
                    }
                }
            }
        }
    }
}

#[observed_only]
#[component]
pub(crate) fn SweepsPage(workspace: ViewerWorkspace) -> Element {
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
                    if let Some(selected) = &workspace.sweeps.selected_case {
                        KeyValueLine { label: "Selected".to_string(), value: selected.clone() }
                    }
                    for case in &workspace.sweeps.explorer.visible_cases {
                        Card {
                            title: case.case_id.clone(),
                            subtitle: case.artifact_id.clone(),
                            children: rsx! {
                                for (key, value) in &case.parameters {
                                    KeyValueLine { label: key.clone(), value: value.clone() }
                                }
                            }
                        }
                    }
                }
            }
            Panel {
                title: "Suite Baselines",
                subtitle: "Baseline-vs-candidate regression reporting",
                children: rsx! {
                    KeyValueLine { label: "Suite".to_string(), value: workspace.sweeps.suite.definition.suite_id.clone() }
                    for case in &workspace.sweeps.suite.cases {
                        KeyValueLine {
                            label: case.case_id.clone(),
                            value: (if case.threshold_passed { "passed" } else { "failed" }).to_string()
                        }
                    }
                }
            }
        }
    }
}

#[observed_only]
#[component]
pub(crate) fn EffectsPage(workspace: ViewerWorkspace) -> Element {
    rsx! {
        div {
            class: "tt-page-grid tt-page-grid--wide",
            Panel {
                title: "Effect Trace",
                subtitle: "Typed requests, resolutions, and replay-visible outcomes",
                children: rsx! {
                    KeyValueLine { label: "Artifact".to_string(), value: workspace.effects.effect_trace.artifact_id.clone() }
                    KeyValueLine { label: "Branch".to_string(), value: workspace.effects.effect_trace.branch_id.clone() }
                    Separator {}
                    if workspace.effects.effect_trace.entries.is_empty() {
                        EmptyState { message: "No effect trace entries." }
                    }
                    for entry in &workspace.effects.effect_trace.entries {
                        Card {
                            title: format!("Step {}: {}", entry.step, entry.kind),
                            subtitle: String::new(),
                            children: rsx! {
                                CodeBlock { content: pretty_json(&entry.detail) }
                            }
                        }
                    }
                }
            }
            Panel {
                title: "Effect Overrides",
                subtitle: "Mocked rerun commands attached to this branch",
                children: rsx! {
                    if workspace.effects.effect_trace.overrides.is_empty() && workspace.effects.mock_command_log.is_empty() {
                        EmptyState { message: "No overrides." }
                    }
                    for override_spec in &workspace.effects.effect_trace.overrides {
                        Card {
                            title: override_spec.operation.clone(),
                            subtitle: format!("{:?}", override_spec.mode),
                            children: rsx! {}
                        }
                    }
                    for command in &workspace.effects.mock_command_log {
                        Card {
                            title: "Command".to_string(),
                            subtitle: String::new(),
                            children: rsx! {
                                CodeBlock { content: pretty_json(command) }
                            }
                        }
                    }
                }
            }
        }
    }
}
