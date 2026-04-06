//! Integration tests for the viewer artifact, query, command, and service surfaces.

use std::collections::BTreeMap;
use telltale_simulator::analysis::NormalizedObservability;
use telltale_simulator::environment::EnvironmentTrace;
use telltale_simulator::runner::{
    CriticalCapacityPhase, CriticalCapacitySummary, ScenarioAnalysisArtifact,
    ScenarioReplayArtifact, ScenarioResult, ScenarioStats, SchedulerBoundMode,
    SchedulerEnvelopeStatus, SchedulerFairnessRequirement, SchedulerProfileSummary,
    TheoremProgressSummary,
};
use telltale_simulator::scenario::{
    ExecutionRegime, ResolvedExecutionBackend, ResolvedSchedulerPolicy, ResolvedTheoremProfile,
    TheoremAssumptionBundle, TheoremEligibility, TheoremEnvelopeProfile, TheoremSchedulerProfile,
};
use telltale_simulator::trace::Trace;
use telltale_viewer::*;
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
    let decoded = serde_json::from_str::<ScenarioBranchPatch>(&json).expect("deserialize patch");
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
