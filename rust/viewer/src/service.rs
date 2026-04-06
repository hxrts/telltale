//! Application service trait and in-memory implementation.

use crate::error::ViewerModelError;
use crate::types::*;
use serde::Serialize;
use std::collections::BTreeMap;
use telltale_macros::authoritative_source;
use telltale_simulator::analysis::{compare_observability, ObservabilityRelation};
use telltale_simulator::decision::{
    decide_theorem_eligibility, DecisionCounterexample, DecisionKind, DecisionOutcome,
    DecisionReport,
};

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
