//! Persistence, serialization, and long-horizon determinism tests.

use std::collections::BTreeMap;
use std::process::id as process_id;

use telltale_machine::coroutine::Value;
use telltale_machine::model::effects::{
    EffectFailure, EffectHandler, EffectResult, SendDecision, SendDecisionInput,
};
use telltale_machine::runtime::loader::CodeImage;
use telltale_simulator::approximation::{
    run_approximation, ApproximationFamily, ApproximationManifest, ApproximationScope,
    ApproximationSpec,
};
use telltale_simulator::distributed::{DistributedSimBuilder, NestedExecutionContract};
use telltale_simulator::environment::{
    EnvironmentModels, EnvironmentSnapshot, LinkAdmissionDecision, LinkAdmissionModel, MediumModel,
    MediumOutcomeKind, MediumResolution, MobilityModel, NodeCapabilityModel, NodeCapabilityState,
    NodePose, PotentialLink, TopologyModel, TransmissionIntent,
};
use telltale_simulator::harness::{
    BatchConfig, DirectAdapter, HarnessSpec, HostAdapter, SimulationHarness,
};
use telltale_simulator::persistence::PersistedReplayArtifact;
use telltale_simulator::reconfiguration::{
    ReconfigurationAction, ReconfigurationEffect, ReconfigurationEffectKind,
    ReconfigurationFootprint, ReconfigurationRecord,
};
use telltale_simulator::runner::{
    canonical_replay_scenario, resume_with_checkpoint_artifact, run_with_scenario,
    ScenarioReplayArtifact, ScenarioResult,
};
use telltale_simulator::scenario::{Scenario, TheoremAssumptionBundle, TheoremSchedulerProfile};
use telltale_simulator::sweep::{run_sweep, SweepAxis, SweepConfig};
use telltale_simulator::{
    compare_observability, normalized_observability, BatchRunManifest, DistributedRunManifest,
    ObservabilityRelation, SweepManifest,
};
use telltale_types::{FixedQ32, GlobalType, Label, LocalTypeR};
use tempfile::tempdir;

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

fn loop_protocol() -> (GlobalType, BTreeMap<String, LocalTypeR>) {
    let global = GlobalType::mu(
        "loop",
        GlobalType::send(
            "A",
            "B",
            Label::new("msg"),
            GlobalType::send("B", "A", Label::new("ack"), GlobalType::var("loop")),
        ),
    );

    let mut local_types = BTreeMap::new();
    local_types.insert(
        "A".to_string(),
        LocalTypeR::mu(
            "loop",
            LocalTypeR::Send {
                partner: "B".into(),
                branches: vec![(
                    Label::new("msg"),
                    None,
                    LocalTypeR::Recv {
                        partner: "B".into(),
                        branches: vec![(Label::new("ack"), None, LocalTypeR::var("loop"))],
                    },
                )],
            },
        ),
    );
    local_types.insert(
        "B".to_string(),
        LocalTypeR::mu(
            "loop",
            LocalTypeR::Recv {
                partner: "A".into(),
                branches: vec![(
                    Label::new("msg"),
                    None,
                    LocalTypeR::Send {
                        partner: "A".into(),
                        branches: vec![(Label::new("ack"), None, LocalTypeR::var("loop"))],
                    },
                )],
            },
        ),
    );

    (global, local_types)
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

fn scenario_name(prefix: &str) -> String {
    format!("{prefix}_{}", process_id())
}

fn middleware_heavy_scenario(name: &str, theorem_bundle: TheoremAssumptionBundle) -> Scenario {
    let assumption_bundle = match theorem_bundle {
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
steps = 14
seed = 41
checkpoint_interval = 2

[execution]
backend = "canonical"
scheduler_concurrency = 1
worker_threads = 1

[theorem]
assumption_bundle = "{assumption_bundle}"

[network]
base_latency_ms = 1
latency_variance = "0.0"
loss_probability = "0.0"

[[adversaries]]
id = "timing_once"
trigger = {{ at_tick = 2 }}
action = {{ type = "timing_disturbance", ticks = 1 }}
budget = {{ total = 1, mode = "activation", assumption_failure = "fairness_failure" }}

[[adversaries]]
id = "hold_once"
trigger = {{ at_tick = 4 }}
action = {{ type = "withholding" }}
budget = {{ total = 1, mode = "activation", assumption_failure = "budget_exhaustion" }}

[[reconfigurations]]
trigger = {{ at_tick = 1 }}
action = {{ type = "handoff", handoff_id = "handoff#1", from_role = "A", to_role = "B" }}

[[reconfigurations]]
trigger = {{ at_tick = 5 }}
action = {{ type = "delegation", scope = "delegate#1", from_role = "B", to_role = "A" }}
effect = {{ kind = "transition_choreography", budget_cost = 1 }}

[properties]
invariants = ["no_faults", "simplex"]

[field]
layer = "mean_field"

[field.params]
beta = "1.0"
species = ["up", "down"]
initial_state = ["0.5", "0.5"]
step_size = "0.01"
"#
    );
    Scenario::parse(&toml).expect("parse middleware-heavy scenario")
}

fn finite_theorem_scenario(name: &str, theorem_bundle: TheoremAssumptionBundle) -> Scenario {
    let assumption_bundle = match theorem_bundle {
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
seed = 7

[execution]
backend = "canonical"
scheduler_concurrency = 1
worker_threads = 1

[theorem]
assumption_bundle = "{assumption_bundle}"
scheduler_profile = "canonical_exact"

[network]
base_latency_ms = 1
latency_variance = "0.0"
loss_probability = "0.0"

[field]
layer = "mean_field"

[field.params]
beta = "1.0"
species = ["up", "down"]
initial_state = ["0.5", "0.5"]
step_size = "0.01"
"#
    );
    Scenario::parse(&toml).expect("parse finite theorem scenario")
}

fn assert_authoritative_equivalence(left: &ScenarioResult, right: &ScenarioResult) {
    assert_eq!(left.replay.theorem_profile, right.replay.theorem_profile);
    assert_eq!(left.replay.obs_trace, right.replay.obs_trace);
    assert_eq!(left.replay.effect_trace, right.replay.effect_trace);
    assert_eq!(
        left.replay.output_condition_trace,
        right.replay.output_condition_trace
    );
    assert_eq!(left.replay.semantic_objects, right.replay.semantic_objects);
    assert_eq!(
        left.replay.reconfiguration_trace,
        right.replay.reconfiguration_trace
    );
    assert_eq!(
        left.replay.environment_trace,
        right.replay.environment_trace
    );
    assert_eq!(left.analysis, right.analysis);
    assert_eq!(left.violations, right.violations);
}

#[derive(Debug, Clone, Copy)]
struct FakeTopologyModel;

impl TopologyModel for FakeTopologyModel {
    fn potential_links(
        &self,
        snapshot: &EnvironmentSnapshot,
    ) -> Result<Vec<PotentialLink>, String> {
        Ok(vec![PotentialLink {
            tick: snapshot.tick,
            from: "A".to_string(),
            to: "B".to_string(),
            reachable: true,
            reason: Some("stable_fake_range".to_string()),
        }])
    }
}

#[derive(Debug, Clone, Copy)]
struct FakeMediumModel;

impl MediumModel for FakeMediumModel {
    fn resolve_transmissions(
        &self,
        _snapshot: &EnvironmentSnapshot,
        transmissions: &[TransmissionIntent],
    ) -> Result<Vec<MediumResolution>, String> {
        Ok(transmissions
            .iter()
            .cloned()
            .map(|transmission| MediumResolution {
                transmission,
                outcome: MediumOutcomeKind::DeliverNow,
                reason: Some("fake_medium_clear".to_string()),
            })
            .collect())
    }
}

#[derive(Debug, Clone, Copy)]
struct FakeMobilityModel;

impl MobilityModel for FakeMobilityModel {
    fn advance(
        &self,
        snapshot: &EnvironmentSnapshot,
    ) -> Result<BTreeMap<String, NodePose>, String> {
        let tick = FixedQ32::from_ratio(i64::try_from(snapshot.tick).unwrap_or(0), 1)
            .expect("tick representable");
        Ok(BTreeMap::from([
            (
                "A".to_string(),
                NodePose {
                    coordinates: vec![tick, FixedQ32::zero()],
                    orientation: vec![FixedQ32::zero()],
                },
            ),
            (
                "B".to_string(),
                NodePose {
                    coordinates: vec![FixedQ32::one(), FixedQ32::zero()],
                    orientation: vec![FixedQ32::half()],
                },
            ),
        ]))
    }
}

#[derive(Debug, Clone, Copy)]
struct FakeNodeCapabilityModel;

impl NodeCapabilityModel for FakeNodeCapabilityModel {
    fn node_capabilities(
        &self,
        _snapshot: &EnvironmentSnapshot,
    ) -> Result<BTreeMap<String, NodeCapabilityState>, String> {
        Ok(BTreeMap::from([(
            "A".to_string(),
            NodeCapabilityState {
                connection_slots: Some(1),
                queue_budget: Some(4),
                duty_cycle_budget: Some(10),
                memory_ceiling: Some(64),
                energy_budget: Some(100),
                custom_limits: BTreeMap::new(),
            },
        )]))
    }
}

#[derive(Debug, Clone, Copy)]
struct FakeAdmissionModel;

impl LinkAdmissionModel for FakeAdmissionModel {
    fn evaluate_links(
        &self,
        snapshot: &EnvironmentSnapshot,
        reachability: &[PotentialLink],
        _capabilities: &BTreeMap<String, NodeCapabilityState>,
    ) -> Result<Vec<LinkAdmissionDecision>, String> {
        Ok(reachability
            .iter()
            .map(|link| LinkAdmissionDecision {
                tick: snapshot.tick,
                from: link.from.clone(),
                to: link.to.clone(),
                admitted: link.reachable,
                reason: Some("fake_capacity_ok".to_string()),
            })
            .collect())
    }
}

struct FakeEnvironmentAdapter {
    handler: PassthroughHandler,
    topology: FakeTopologyModel,
    medium: FakeMediumModel,
    mobility: FakeMobilityModel,
    node_capabilities: FakeNodeCapabilityModel,
    admission: FakeAdmissionModel,
}

impl HostAdapter for FakeEnvironmentAdapter {
    fn effect_handler(&self) -> &dyn EffectHandler {
        &self.handler
    }

    fn environment_models(
        &self,
        _scenario: &Scenario,
    ) -> Result<Option<EnvironmentModels<'_>>, String> {
        Ok(Some(EnvironmentModels {
            topology: Some(&self.topology),
            medium: Some(&self.medium),
            mobility: Some(&self.mobility),
            node_capabilities: Some(&self.node_capabilities),
            link_admission: Some(&self.admission),
        }))
    }
}

#[test]
fn persisted_checkpoint_files_round_trip_through_the_typed_loader() {
    let (global, local_types) = loop_protocol();
    let scenario = middleware_heavy_scenario(
        &scenario_name("phase22_disk_checkpoint"),
        TheoremAssumptionBundle::ObservedTransport,
    );
    let full = run_with_scenario(
        &local_types,
        &global,
        &BTreeMap::new(),
        &scenario,
        &PassthroughHandler,
    )
    .expect("full run");
    let checkpoint = full
        .replay
        .checkpoints
        .iter()
        .find(|checkpoint| checkpoint.tick == 4)
        .expect("checkpoint at tick 4")
        .clone();

    let tmp = tempdir().expect("tempdir");
    let path = tmp.path().join("checkpoint_4.cbor");
    PersistedReplayArtifact::checkpoint(checkpoint.clone())
        .write_to_path(&path)
        .expect("write persisted checkpoint");
    let loaded = PersistedReplayArtifact::from_path(&path)
        .expect("load persisted checkpoint")
        .into_checkpoint_artifact()
        .expect("checkpoint payload");
    let resumed =
        resume_with_checkpoint_artifact(&scenario, &loaded, &PassthroughHandler, None, None)
            .expect("resume loaded checkpoint");
    let resumed_in_memory =
        resume_with_checkpoint_artifact(&scenario, &checkpoint, &PassthroughHandler, None, None)
            .expect("resume in-memory checkpoint");

    assert_authoritative_equivalence(&resumed_in_memory, &resumed);
    assert_authoritative_equivalence(&full, &resumed);
}

#[test]
fn public_artifacts_survive_serde_round_trips() {
    let (global, local_types) = loop_protocol();
    let scenario = middleware_heavy_scenario(
        &scenario_name("phase22_serde"),
        TheoremAssumptionBundle::ObservedTransport,
    );
    let result = run_with_scenario(
        &local_types,
        &global,
        &BTreeMap::new(),
        &scenario,
        &PassthroughHandler,
    )
    .expect("run scenario");

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
            axes: vec![SweepAxis::Seed {
                values: vec![scenario.seed],
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

    let distributed_manifest = {
        let (inner_global, inner_locals) = finite_protocol();
        let inner_image = CodeImage::from_local_types(&inner_locals, &inner_global);
        let outer_image = CodeImage::from_local_types(&inner_locals, &inner_global);
        DistributedSimBuilder::new()
            .add_site("A", vec![inner_image.clone()])
            .add_site("B", vec![inner_image])
            .inter_site(outer_image)
            .execution_contract(NestedExecutionContract::default())
            .build(&telltale_machine::ProtocolMachineConfig::default())
            .expect("build distributed simulation")
            .report()
            .manifest
    };

    let result_roundtrip: ScenarioResult =
        serde_json::from_slice(&serde_json::to_vec(&result).expect("serialize scenario result"))
            .expect("deserialize scenario result");
    let replay_roundtrip: ScenarioReplayArtifact = serde_json::from_slice(
        &serde_json::to_vec(&result.replay).expect("serialize scenario replay"),
    )
    .expect("deserialize scenario replay");
    let batch_roundtrip: BatchRunManifest = serde_json::from_slice(
        &serde_json::to_vec(&batch.manifest).expect("serialize batch manifest"),
    )
    .expect("deserialize batch manifest");
    let sweep_roundtrip: SweepManifest = serde_json::from_slice(
        &serde_json::to_vec(&sweep.manifest).expect("serialize sweep manifest"),
    )
    .expect("deserialize sweep manifest");
    let approximation_roundtrip: ApproximationManifest = serde_json::from_slice(
        &serde_json::to_vec(&approximation.manifest).expect("serialize approximation manifest"),
    )
    .expect("deserialize approximation manifest");
    let distributed_roundtrip: DistributedRunManifest = serde_json::from_slice(
        &serde_json::to_vec(&distributed_manifest).expect("serialize distributed manifest"),
    )
    .expect("deserialize distributed manifest");

    assert_eq!(result_roundtrip, result);
    assert_eq!(replay_roundtrip, result.replay);
    assert_eq!(batch_roundtrip, batch.manifest);
    assert_eq!(sweep_roundtrip, sweep.manifest);
    assert_eq!(approximation_roundtrip, approximation.manifest);
    assert_eq!(distributed_roundtrip, distributed_manifest);
}

#[test]
fn batch_and_sweep_manifests_are_json_stable_across_reruns() {
    let (global, local_types) = finite_protocol();
    let scenario = finite_theorem_scenario(
        &scenario_name("phase22_manifest_stability"),
        TheoremAssumptionBundle::ObservedTransport,
    );
    let spec = HarnessSpec::new(local_types, global, scenario);
    let adapter = DirectAdapter::new(&PassthroughHandler);
    let harness = SimulationHarness::new(&adapter);
    let batch_config = BatchConfig {
        parallelism: Some(2),
    };
    let sweep_config = SweepConfig {
        batch: batch_config,
        axes: vec![
            SweepAxis::Seed { values: vec![7, 9] },
            SweepAxis::SchedulerProfile {
                values: vec![
                    TheoremSchedulerProfile::CanonicalExact,
                    TheoremSchedulerProfile::ThreadedExact,
                ],
            },
        ],
    };

    let batch_a = harness.run_batch_with(std::slice::from_ref(&spec), batch_config);
    let batch_b = harness.run_batch_with(std::slice::from_ref(&spec), batch_config);
    let sweep_a = run_sweep(&harness, &spec, &sweep_config).expect("first sweep");
    let sweep_b = run_sweep(&harness, &spec, &sweep_config).expect("second sweep");

    assert_eq!(
        serde_json::to_string(&batch_a.manifest).expect("serialize batch a"),
        serde_json::to_string(&batch_b.manifest).expect("serialize batch b")
    );
    assert_eq!(
        serde_json::to_string(&sweep_a.manifest).expect("serialize sweep a"),
        serde_json::to_string(&sweep_b.manifest).expect("serialize sweep b")
    );
}

#[test]
fn replay_loader_fails_closed_for_corruption_and_mismatch() {
    let (global, local_types) = loop_protocol();
    let scenario = middleware_heavy_scenario(
        &scenario_name("phase22_negative_replay"),
        TheoremAssumptionBundle::ObservedTransport,
    );
    let result = run_with_scenario(
        &local_types,
        &global,
        &BTreeMap::new(),
        &scenario,
        &PassthroughHandler,
    )
    .expect("run scenario");
    let checkpoint = result
        .replay
        .checkpoints
        .iter()
        .find(|checkpoint| checkpoint.tick == 4)
        .expect("checkpoint at tick 4")
        .clone();

    let corrupt = PersistedReplayArtifact::from_slice(b"not cbor");
    assert!(corrupt
        .expect_err("corrupt bytes should fail")
        .contains("decode persisted replay artifact"));

    #[derive(serde::Serialize)]
    #[serde(rename_all = "snake_case", tag = "kind", content = "payload")]
    enum LegacyPayload {
        Checkpoint(LegacyCheckpointArtifact),
    }
    #[derive(serde::Serialize)]
    struct LegacyCheckpointArtifact {
        tick: u64,
        machine_state: Vec<u8>,
    }
    #[derive(serde::Serialize)]
    struct LegacyPersistedReplayArtifact {
        schema_version: String,
        payload: LegacyPayload,
    }

    let legacy_bytes = serde_cbor::to_vec(&LegacyPersistedReplayArtifact {
        schema_version: "telltale.simulator.persisted_replay.v1".to_string(),
        payload: LegacyPayload::Checkpoint(LegacyCheckpointArtifact {
            tick: checkpoint.tick,
            machine_state: checkpoint.machine_state.clone(),
        }),
    })
    .expect("serialize legacy checkpoint artifact");
    let legacy_checkpoint = PersistedReplayArtifact::from_slice(&legacy_bytes)
        .expect("decode legacy-shaped checkpoint")
        .into_checkpoint_artifact()
        .expect("checkpoint payload");
    let missing_middleware = resume_with_checkpoint_artifact(
        &scenario,
        &legacy_checkpoint,
        &PassthroughHandler,
        None,
        None,
    )
    .expect_err("checkpoint without middleware should fail closed");
    assert!(missing_middleware.contains("missing exact middleware state"));

    let mismatched_scenario = Scenario::parse(
        r#"
name = "mismatch_roles"
roles = ["A", "C"]
steps = 6
seed = 41

[execution]
backend = "canonical"
scheduler_concurrency = 1
worker_threads = 1
"#,
    )
    .expect("parse mismatched scenario");
    let mismatch = resume_with_checkpoint_artifact(
        &mismatched_scenario,
        &checkpoint,
        &PassthroughHandler,
        None,
        None,
    )
    .expect_err("checkpoint/scenario role mismatch should fail closed");
    assert!(mismatch.contains("checkpoint roles"));
}

#[test]
fn multiple_checkpoint_resumes_converge_to_the_same_final_result() {
    let (global, local_types) = loop_protocol();
    let scenario = middleware_heavy_scenario(
        &scenario_name("phase22_multi_checkpoint"),
        TheoremAssumptionBundle::ObservedTransport,
    );
    let full = run_with_scenario(
        &local_types,
        &global,
        &BTreeMap::new(),
        &scenario,
        &PassthroughHandler,
    )
    .expect("full run");

    for tick in [2u64, 4, 6] {
        let checkpoint = full
            .replay
            .checkpoints
            .iter()
            .find(|checkpoint| checkpoint.tick == tick)
            .unwrap_or_else(|| panic!("checkpoint at tick {tick}"));
        let resumed =
            resume_with_checkpoint_artifact(&scenario, checkpoint, &PassthroughHandler, None, None)
                .unwrap_or_else(|err| panic!("resume from tick {tick}: {err}"));
        assert_authoritative_equivalence(&full, &resumed);
    }
}

#[test]
fn theorem_profile_reclassification_changes_only_classification() {
    let (global, local_types) = finite_protocol();
    let scenarios = [
        finite_theorem_scenario(
            &scenario_name("phase22_reclass_auto"),
            TheoremAssumptionBundle::Auto,
        ),
        finite_theorem_scenario(
            &scenario_name("phase22_reclass_observed"),
            TheoremAssumptionBundle::ObservedTransport,
        ),
        finite_theorem_scenario(
            &scenario_name("phase22_reclass_faultfree"),
            TheoremAssumptionBundle::FaultFreeTransport,
        ),
    ];

    let results: Vec<_> = scenarios
        .iter()
        .map(|scenario| {
            run_with_scenario(
                &local_types,
                &global,
                &BTreeMap::new(),
                scenario,
                &PassthroughHandler,
            )
            .expect("run theorem reclassification scenario")
        })
        .collect();

    for pair in results.windows(2) {
        assert_eq!(pair[0].replay.obs_trace, pair[1].replay.obs_trace);
        assert_eq!(pair[0].replay.effect_trace, pair[1].replay.effect_trace);
        assert_eq!(pair[0].analysis, pair[1].analysis);
        assert_eq!(pair[0].violations, pair[1].violations);
    }
    assert!(
        results
            .windows(2)
            .any(|pair| pair[0].stats.theorem_profile != pair[1].stats.theorem_profile),
        "declared theorem bundles should reclassify at least one run"
    );
}

#[test]
fn long_horizon_exact_runs_are_byte_stable() {
    let (global, local_types) = loop_protocol();
    let scenario = middleware_heavy_scenario(
        &scenario_name("phase22_long_horizon"),
        TheoremAssumptionBundle::ObservedTransport,
    );

    let first = run_with_scenario(
        &local_types,
        &global,
        &BTreeMap::new(),
        &scenario,
        &PassthroughHandler,
    )
    .expect("first run");
    let second = run_with_scenario(
        &local_types,
        &global,
        &BTreeMap::new(),
        &scenario,
        &PassthroughHandler,
    )
    .expect("second run");

    assert_eq!(
        serde_json::to_vec(&first).expect("serialize first run"),
        serde_json::to_vec(&second).expect("serialize second run")
    );
}

#[test]
fn distributed_manifest_vocabulary_stays_aligned_with_other_artifacts() {
    let (global, local_types) = finite_protocol();
    let scenario = finite_theorem_scenario(
        &scenario_name("phase22_vocab"),
        TheoremAssumptionBundle::ObservedTransport,
    );
    let direct = run_with_scenario(
        &local_types,
        &global,
        &BTreeMap::new(),
        &scenario,
        &PassthroughHandler,
    )
    .expect("direct run");
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
            axes: vec![SweepAxis::Seed {
                values: vec![scenario.seed],
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
    let inner_image = CodeImage::from_local_types(&local_types, &global);
    let distributed = DistributedSimBuilder::new()
        .add_site("A", vec![inner_image.clone()])
        .add_site("B", vec![inner_image])
        .inter_site(CodeImage::from_local_types(&local_types, &global))
        .execution_contract(NestedExecutionContract::default())
        .build(&telltale_machine::ProtocolMachineConfig::default())
        .expect("build distributed")
        .report();

    assert_eq!(
        batch.manifest.runs[0]
            .theorem_profile
            .as_ref()
            .map(|profile| profile.assumption_bundle),
        Some(direct.stats.theorem_profile.assumption_bundle)
    );
    assert_eq!(
        sweep.manifest.runs[0]
            .theorem_profile
            .as_ref()
            .map(|profile| profile.eligibility),
        Some(direct.stats.theorem_profile.eligibility)
    );
    assert_eq!(
        approximation.manifest.theorem_profile.assumption_bundle,
        direct.stats.theorem_profile.assumption_bundle
    );
    assert_eq!(
        distributed.manifest.theorem_profile.assumption_bundle,
        TheoremAssumptionBundle::ObservedTransport
    );
    assert_eq!(
        serde_json::to_value(&distributed.manifest).expect("serialize distributed manifest")
            ["theorem_profile"]["assumption_bundle"],
        serde_json::json!("observed_transport")
    );
}

#[test]
fn threaded_exact_environment_runs_match_canonical_replay_with_theorem_overrides() {
    let (global, local_types) = finite_protocol();
    let mut threaded = finite_theorem_scenario(
        &scenario_name("phase22_threaded_env"),
        TheoremAssumptionBundle::ObservedTransport,
    );
    threaded.execution.backend = telltale_simulator::scenario::ExecutionBackend::Threaded;
    threaded.execution.scheduler_concurrency = Some(1);
    threaded.execution.worker_threads = Some(3);
    threaded.theorem.scheduler_profile = TheoremSchedulerProfile::ThreadedExact;

    let adapter = FakeEnvironmentAdapter {
        handler: PassthroughHandler,
        topology: FakeTopologyModel,
        medium: FakeMediumModel,
        mobility: FakeMobilityModel,
        node_capabilities: FakeNodeCapabilityModel,
        admission: FakeAdmissionModel,
    };
    let harness = SimulationHarness::new(&adapter);
    let threaded_spec = HarnessSpec::new(local_types.clone(), global.clone(), threaded.clone());
    let threaded_result = harness.run(&threaded_spec).expect("threaded exact env run");

    let replay_scenario = canonical_replay_scenario(&threaded);
    let replay_spec = HarnessSpec::new(local_types, global, replay_scenario);
    let replayed = harness.run(&replay_spec).expect("canonical replay env run");

    assert_eq!(
        threaded_result.analysis.normalized_observability,
        replayed.analysis.normalized_observability
    );
    assert_eq!(
        threaded_result.stats.theorem_progress,
        replayed.stats.theorem_progress
    );
    assert_eq!(
        threaded_result.replay.environment_trace,
        replayed.replay.environment_trace
    );
    assert_eq!(
        threaded_result.replay.semantic_objects,
        replayed.replay.semantic_objects
    );
    assert_eq!(threaded_result.replay.obs_trace, replayed.replay.obs_trace);
}

#[test]
fn reconfiguration_normalization_matrix_separates_equivalence_from_divergence() {
    let base = vec![telltale_machine::ObsEvent::Opened {
        tick: 1,
        session: 0,
        roles: vec!["A".to_string(), "B".to_string()],
    }];
    let equivalent_left = vec![ReconfigurationRecord {
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
    let equivalent_right = equivalent_left.clone();
    let divergent_effect = vec![ReconfigurationRecord {
        effect: ReconfigurationEffect {
            kind: ReconfigurationEffectKind::TransitionChoreography,
            budget_cost: 3,
        },
        ..equivalent_left[0].clone()
    }];
    let divergent_footprint = vec![ReconfigurationRecord {
        footprint: ReconfigurationFootprint {
            roles: vec!["A".to_string(), "C".to_string()],
            links: Vec::new(),
        },
        action: ReconfigurationAction::Handoff {
            handoff_id: "h1".to_string(),
            from_role: "A".to_string(),
            to_role: "C".to_string(),
        },
        ..equivalent_left[0].clone()
    }];

    let cases = [
        (
            &equivalent_left,
            &equivalent_right,
            ObservabilityRelation::ExactRawMatch,
        ),
        (
            &equivalent_left,
            &divergent_effect,
            ObservabilityRelation::SafetyVisibleDivergence,
        ),
        (
            &equivalent_left,
            &divergent_footprint,
            ObservabilityRelation::SafetyVisibleDivergence,
        ),
    ];

    for (left, right, expected) in cases {
        let left_norm = normalized_observability(&base, left);
        let right_norm = normalized_observability(&base, right);
        let comparison = compare_observability(&base, left, &left_norm, &base, right, &right_norm);
        assert_eq!(comparison.relation, expected);
    }
}
