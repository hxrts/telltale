//! Workspace loading from the typed viewer application service.

use crate::types::*;
use std::collections::BTreeMap;
use telltale_macros::observed_only;
use telltale_simulator::scenario::{ExecutionRegime, ResolvedExecutionBackend};
use telltale_viewer::{
    GraphProjection, GraphProjectionKind, GraphProjectionRequest,
    SemanticComparisonRequest, SemanticComparisonResult,
    SweepExplorerRequest, ViewerApplicationService, ViewerExtensionManifest,
    MinimizationResult, TheoremAwareCounterexample, ViewerModelError, ViewerQuery, ViewerQueryResult, ViewerReport,
};

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

    let default_projection = projections
        .iter()
        .position(|p| p.kind == GraphProjectionKind::ExecutionTimeline)
        .unwrap_or(0);
    Ok(ViewerWorkspace {
        report,
        graph: ViewerGraphWorkspace {
            layout: deterministic_layout(&projections),
            projections,
            active_projection: default_projection,
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

