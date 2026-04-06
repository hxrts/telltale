//! Demo workspace and fixture data for the viewer.

use crate::loading::load_workspace_from_service;
use crate::types::*;
use std::collections::BTreeMap;
use telltale_macros::authoritative_source;
use telltale_machine::ProtocolMachineSemanticObjects;
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
    mocked_rerun_command, ExperimentSuiteCase,
    ExperimentSuiteDefinition, InMemoryViewerService,
    RegressionThreshold, ScenarioBundleArtifact, SweepCaseSpec, ViewerApplicationService,
    ViewerArtifact, ViewerArtifactFile, ViewerCommand,
    ViewerExtensionDescriptor, ViewerExtensionManifest, ViewerExtensionSlot,
};

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
