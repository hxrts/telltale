//! Cross-surface classification and fail-closed assurance tests.

use std::collections::BTreeMap;

use telltale_machine::coroutine::Value;
use telltale_machine::model::effects::{
    EffectFailure, EffectHandler, EffectResult, SendDecision, SendDecisionInput,
};
use telltale_machine::runtime::loader::CodeImage;
use telltale_machine::{ObsEvent, ProtocolMachineConfig};
use telltale_simulator::analysis::{compare_observability, ObservabilityRelation};
use telltale_simulator::approximation::{
    run_approximation, ApproximationAdmissibility, ApproximationFamily, ApproximationScope,
    ApproximationSpec,
};
use telltale_simulator::decision::{decide_theorem_eligibility, theorem_eligibility_from_result};
use telltale_simulator::distributed::{
    DistributedExecutionRegime, DistributedSimBuilder, NestedExecutionContract,
};
use telltale_simulator::harness::{BatchConfig, DirectAdapter, HarnessSpec, SimulationHarness};
use telltale_simulator::reconfiguration::{
    ReconfigurationAction, ReconfigurationEffect, ReconfigurationFootprint, ReconfigurationRecord,
};
use telltale_simulator::runner::run_with_scenario;
use telltale_simulator::scenario::{
    Scenario, TheoremAssumptionBundle, TheoremEligibility, TheoremSchedulerProfile,
};
use telltale_simulator::sweep::{run_sweep, SweepAxis, SweepConfig};
use telltale_types::{GlobalType, Label, LocalTypeR};

#[derive(Debug, Clone, Copy)]
struct PassthroughHandler;

impl EffectHandler for PassthroughHandler {
    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        label: &str,
        _state: &[Value],
    ) -> EffectResult<Value> {
        EffectResult::success(Value::Str(label.to_string()))
    }

    fn send_decision(&self, input: SendDecisionInput<'_>) -> EffectResult<SendDecision> {
        EffectResult::success(SendDecision::Deliver(input.payload.unwrap_or(Value::Unit)))
    }

    fn handle_recv(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &mut Vec<Value>,
        _payload: &Value,
    ) -> EffectResult<()> {
        EffectResult::success(())
    }

    fn handle_choose(
        &self,
        _role: &str,
        _partner: &str,
        labels: &[String],
        _state: &[Value],
    ) -> EffectResult<String> {
        match labels.first().cloned() {
            Some(label) => EffectResult::success(label),
            None => EffectResult::failure(EffectFailure::invalid_input("no labels available")),
        }
    }

    fn step(&self, _role: &str, _state: &mut Vec<Value>) -> EffectResult<()> {
        EffectResult::success(())
    }
}

fn finite_protocol() -> (GlobalType, BTreeMap<String, LocalTypeR>) {
    let global = GlobalType::send(
        "A",
        "B",
        Label::new("msg"),
        GlobalType::send("B", "A", Label::new("ack"), GlobalType::End),
    );

    let mut local_types = BTreeMap::new();
    local_types.insert(
        "A".to_string(),
        LocalTypeR::Send {
            partner: "B".into(),
            branches: vec![(
                Label::new("msg"),
                None,
                LocalTypeR::Recv {
                    partner: "B".into(),
                    branches: vec![(Label::new("ack"), None, LocalTypeR::End)],
                },
            )],
        },
    );
    local_types.insert(
        "B".to_string(),
        LocalTypeR::Recv {
            partner: "A".into(),
            branches: vec![(
                Label::new("msg"),
                None,
                LocalTypeR::Send {
                    partner: "A".into(),
                    branches: vec![(Label::new("ack"), None, LocalTypeR::End)],
                },
            )],
        },
    );
    (global, local_types)
}

fn scenario_with_network(
    name: &str,
    assumption_bundle: TheoremAssumptionBundle,
    base_latency_ms: u64,
    loss_probability: &str,
) -> Scenario {
    let assumption_bundle = match assumption_bundle {
        TheoremAssumptionBundle::Auto => "auto",
        TheoremAssumptionBundle::FaultFreeTransport => "fault_free_transport",
        TheoremAssumptionBundle::ObservedTransport => "observed_transport",
        TheoremAssumptionBundle::PartialSynchrony => "partial_synchrony",
        TheoremAssumptionBundle::ByzantineEnvelope => "byzantine_envelope",
    };
    let toml = format!(
        r#"
name = "{name}"
roles = ["A", "B"]
steps = 4
seed = 13

[execution]
backend = "canonical"
scheduler_concurrency = 1
worker_threads = 1

[theorem]
assumption_bundle = "{assumption_bundle}"

[network]
base_latency_ms = {base_latency_ms}
latency_variance = "0.0"
loss_probability = "{loss_probability}"

[field]
layer = "mean_field"

[field.params]
beta = "1.0"
species = ["up", "down"]
initial_state = ["0.5", "0.5"]
step_size = "0.01"
"#
    );
    Scenario::parse(&toml).expect("parse network scenario")
}

#[test]
fn theorem_eligibility_and_manifest_classification_fail_closed_consistently() {
    let (global, local_types) = finite_protocol();
    let scenario = scenario_with_network(
        "classification_ineligible",
        TheoremAssumptionBundle::FaultFreeTransport,
        1,
        "0.0",
    );

    let theorem = scenario
        .resolved_theorem_profile()
        .expect("resolve theorem profile");
    assert_eq!(theorem.eligibility, TheoremEligibility::Ineligible);
    assert_eq!(
        theorem.assumption_bundle,
        TheoremAssumptionBundle::FaultFreeTransport
    );

    let offline = decide_theorem_eligibility(&scenario);
    let direct = run_with_scenario(
        &local_types,
        &global,
        &BTreeMap::new(),
        &scenario,
        &PassthroughHandler,
    )
    .expect("direct run");
    let runtime = theorem_eligibility_from_result(&direct);

    let adapter = DirectAdapter::new(&PassthroughHandler);
    let harness = SimulationHarness::new(&adapter);
    let spec = HarnessSpec::new(local_types.clone(), global.clone(), scenario.clone());
    let batch = harness.run_batch_with(
        std::slice::from_ref(&spec),
        BatchConfig {
            parallelism: Some(1),
        },
    );
    let sweep = run_sweep(
        &harness,
        &spec,
        &SweepConfig {
            batch: BatchConfig {
                parallelism: Some(1),
            },
            axes: vec![SweepAxis::SchedulerProfile {
                values: vec![TheoremSchedulerProfile::CanonicalExact],
            }],
        },
    )
    .expect("run sweep");
    let approximation = run_approximation(
        &local_types,
        &global,
        &BTreeMap::new(),
        &scenario,
        &PassthroughHandler,
        &ApproximationSpec {
            family: ApproximationFamily::MeanField,
            scope: ApproximationScope::MeanFieldLimit,
            non_goals: vec!["not_authoritative_replay".to_string()],
        },
    )
    .expect("run approximation");

    assert_eq!(offline, runtime);
    assert_eq!(
        batch.manifest.runs[0].execution_regime,
        Some(direct.stats.execution_regime)
    );
    assert_eq!(
        batch.manifest.runs[0].theorem_profile.as_ref(),
        Some(&direct.stats.theorem_profile)
    );
    assert_eq!(
        sweep.manifest.runs[0].execution_regime,
        Some(direct.stats.execution_regime)
    );
    assert_eq!(
        sweep.manifest.runs[0].theorem_profile.as_ref(),
        Some(&direct.stats.theorem_profile)
    );
    assert_eq!(sweep.manifest.runs[0].theorem_eligibility, runtime);
    assert_eq!(
        approximation.manifest.execution_regime,
        direct.stats.execution_regime
    );
    assert_eq!(
        approximation.manifest.theorem_profile,
        direct.stats.theorem_profile
    );
    assert_eq!(
        approximation.manifest.admissibility,
        ApproximationAdmissibility::Unsupported
    );
}

#[test]
fn normalized_equivalence_and_true_divergence_stay_distinct() {
    let left_obs = vec![
        ObsEvent::Opened {
            tick: 2,
            session: 0,
            roles: vec!["A".to_string(), "B".to_string()],
        },
        ObsEvent::Opened {
            tick: 1,
            session: 1,
            roles: vec!["C".to_string(), "D".to_string()],
        },
    ];
    let right_obs = vec![
        ObsEvent::Opened {
            tick: 7,
            session: 1,
            roles: vec!["C".to_string(), "D".to_string()],
        },
        ObsEvent::Opened {
            tick: 9,
            session: 0,
            roles: vec!["A".to_string(), "B".to_string()],
        },
    ];
    let left_normalized = telltale_simulator::normalized_observability(&left_obs, &[]);
    let right_normalized = telltale_simulator::normalized_observability(&right_obs, &[]);

    let normalized_equivalent = compare_observability(
        &left_obs,
        &[],
        &left_normalized,
        &right_obs,
        &[],
        &right_normalized,
    );
    assert_eq!(
        normalized_equivalent.relation,
        ObservabilityRelation::EquivalentUnderNormalization
    );

    let left_reconfiguration = vec![ReconfigurationRecord {
        operation_id: "reconfiguration:0".to_string(),
        tick: 1,
        logical_step: 1,
        action: ReconfigurationAction::Handoff {
            handoff_id: "h1".to_string(),
            from_role: "A".to_string(),
            to_role: "B".to_string(),
        },
        effect: ReconfigurationEffect::default(),
        footprint: ReconfigurationFootprint {
            roles: vec!["A".to_string(), "B".to_string()],
            links: Vec::new(),
        },
    }];
    let right_reconfiguration = vec![ReconfigurationRecord {
        operation_id: "reconfiguration:0".to_string(),
        tick: 1,
        logical_step: 1,
        action: ReconfigurationAction::Handoff {
            handoff_id: "h1".to_string(),
            from_role: "A".to_string(),
            to_role: "C".to_string(),
        },
        effect: ReconfigurationEffect::default(),
        footprint: ReconfigurationFootprint {
            roles: vec!["A".to_string(), "C".to_string()],
            links: Vec::new(),
        },
    }];
    let divergent_left_normalized =
        telltale_simulator::normalized_observability(&left_obs, &left_reconfiguration);
    let divergent_right_normalized =
        telltale_simulator::normalized_observability(&left_obs, &right_reconfiguration);
    let divergent = compare_observability(
        &left_obs,
        &left_reconfiguration,
        &divergent_left_normalized,
        &left_obs,
        &right_reconfiguration,
        &divergent_right_normalized,
    );
    assert_eq!(
        divergent.relation,
        ObservabilityRelation::SafetyVisibleDivergence
    );
}

#[test]
fn distributed_manifests_publish_explicit_observed_only_classification() {
    let (inner_global, inner_locals) = finite_protocol();
    let inner_image = CodeImage::from_local_types(&inner_locals, &inner_global);
    let (outer_global, outer_locals) = finite_protocol();
    let outer_image = CodeImage::from_local_types(&outer_locals, &outer_global);

    let simulation = DistributedSimBuilder::new()
        .add_site("A", vec![inner_image.clone()])
        .add_site("B", vec![inner_image])
        .inter_site(outer_image)
        .execution_contract(NestedExecutionContract {
            outer_scheduler_concurrency: 2,
            inner_rounds_per_step: 2,
        })
        .build(&ProtocolMachineConfig::default())
        .expect("build distributed simulation");

    let manifest = simulation.manifest();
    assert_eq!(
        manifest.execution_regime,
        DistributedExecutionRegime::NestedObserved
    );
    assert_eq!(
        manifest.theorem_profile.assumption_bundle,
        TheoremAssumptionBundle::ObservedTransport
    );
    assert_eq!(
        manifest.theorem_profile.eligibility,
        TheoremEligibility::Ineligible
    );
    assert!(manifest
        .theorem_profile
        .eligibility_reason
        .as_deref()
        .is_some_and(|reason| reason.contains("observed-only")));
}

#[test]
fn generated_helper_surfaces_do_not_look_authoritative() {
    let source = std::fs::read_to_string(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src/generated.rs"),
    )
    .expect("read generated helper source");
    let report_block = source
        .split("pub struct GeneratedEffectSimulationReport")
        .nth(1)
        .expect("generated report definition");
    for banned in [
        "theorem_profile",
        "execution_regime",
        "checkpoint",
        "normalized_observability",
    ] {
        assert!(
            !report_block.contains(banned),
            "generated helper report must not expose authoritative simulator field `{banned}`",
        );
    }
}
