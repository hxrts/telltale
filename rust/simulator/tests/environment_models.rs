//! Integration tests for external environment-model hooks.

use std::collections::BTreeMap;

use telltale_machine::coroutine::Value;
use telltale_machine::model::effects::{
    EffectHandler, EffectResult, SendDecision, SendDecisionInput,
};
use telltale_simulator::environment::{
    EnvironmentArtifact, EnvironmentModels, EnvironmentSnapshot, LinkAdmissionDecision,
    LinkAdmissionModel, MediumModel, MediumOutcomeKind, MediumResolution, MobilityModel,
    NodeCapabilityModel, NodeCapabilityState, NodePose, PotentialLink, TopologyModel,
    TransmissionIntent,
};
use telltale_simulator::harness::{HarnessSpec, HostAdapter, SimulationHarness};
use telltale_simulator::scenario::{ExecutionSpec, Scenario};
use telltale_types::{FixedQ32, GlobalType, Label, LocalTypeR};

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
        EffectResult::success(labels.first().cloned().unwrap_or_default())
    }

    fn step(&self, _role: &str, _state: &mut Vec<Value>) -> EffectResult<()> {
        EffectResult::success(())
    }
}

struct FakeTopologyModel;

impl TopologyModel for FakeTopologyModel {
    fn potential_links(
        &self,
        snapshot: &EnvironmentSnapshot,
    ) -> Result<Vec<PotentialLink>, String> {
        Ok(vec![
            PotentialLink {
                tick: snapshot.tick,
                from: "A".to_string(),
                to: "B".to_string(),
                reachable: true,
                reason: Some("within_fake_range".to_string()),
            },
            PotentialLink {
                tick: snapshot.tick,
                from: "B".to_string(),
                to: "A".to_string(),
                reachable: false,
                reason: Some("blocked_fake_return_path".to_string()),
            },
        ])
    }
}

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

struct FakeNodeCapabilityModel;

impl NodeCapabilityModel for FakeNodeCapabilityModel {
    fn node_capabilities(
        &self,
        _snapshot: &EnvironmentSnapshot,
    ) -> Result<BTreeMap<String, NodeCapabilityState>, String> {
        Ok(BTreeMap::from([
            (
                "A".to_string(),
                NodeCapabilityState {
                    connection_slots: Some(1),
                    queue_budget: Some(4),
                    duty_cycle_budget: Some(10),
                    memory_ceiling: Some(64),
                    energy_budget: Some(100),
                    custom_limits: BTreeMap::from([("relay_budget".to_string(), 2)]),
                },
            ),
            (
                "B".to_string(),
                NodeCapabilityState {
                    connection_slots: Some(0),
                    queue_budget: Some(2),
                    duty_cycle_budget: Some(8),
                    memory_ceiling: Some(64),
                    energy_budget: Some(95),
                    custom_limits: BTreeMap::new(),
                },
            ),
        ]))
    }
}

struct FakeAdmissionModel;

impl LinkAdmissionModel for FakeAdmissionModel {
    fn evaluate_links(
        &self,
        snapshot: &EnvironmentSnapshot,
        reachability: &[PotentialLink],
        capabilities: &BTreeMap<String, NodeCapabilityState>,
    ) -> Result<Vec<LinkAdmissionDecision>, String> {
        Ok(reachability
            .iter()
            .map(|link| {
                let admitted = link.reachable
                    && capabilities
                        .get(&link.from)
                        .and_then(|state| state.connection_slots)
                        .unwrap_or(0)
                        > 0;
                LinkAdmissionDecision {
                    tick: snapshot.tick,
                    from: link.from.clone(),
                    to: link.to.clone(),
                    admitted,
                    reason: if admitted {
                        Some("fake_capacity_ok".to_string())
                    } else {
                        Some("fake_capacity_rejected".to_string())
                    },
                }
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

    fn initial_states(
        &self,
        _scenario: &Scenario,
    ) -> Result<Option<BTreeMap<String, Vec<FixedQ32>>>, String> {
        Ok(Some(BTreeMap::from([
            ("A".to_string(), vec![FixedQ32::half()]),
            ("B".to_string(), vec![FixedQ32::half()]),
        ])))
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

fn finite_protocol() -> (GlobalType, BTreeMap<String, LocalTypeR>) {
    let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
    let mut local_types = BTreeMap::new();
    local_types.insert(
        "A".to_string(),
        LocalTypeR::Send {
            partner: "B".into(),
            branches: vec![(Label::new("msg"), None, LocalTypeR::End)],
        },
    );
    local_types.insert(
        "B".to_string(),
        LocalTypeR::Recv {
            partner: "A".into(),
            branches: vec![(Label::new("msg"), None, LocalTypeR::End)],
        },
    );
    (global, local_types)
}

fn scenario_without_builtin_field() -> Scenario {
    Scenario {
        name: "external_environment_models".to_string(),
        roles: vec!["A".to_string(), "B".to_string()],
        steps: 3,
        execution: ExecutionSpec::default(),
        seed: 11,
        network: None,
        field: None,
        reconfigurations: Vec::new(),
        adversaries: Vec::new(),
        properties: None,
        checkpoint_interval: None,
        theorem: telltale_simulator::scenario::TheoremProfileSpec::default(),
        extensions: BTreeMap::from([(
            "fake_external_env".to_string(),
            toml::Value::Table(toml::map::Map::from_iter([(
                "profile".to_string(),
                toml::Value::String("test".to_string()),
            )])),
        )]),
    }
}

#[test]
fn external_environment_models_emit_domain_neutral_environment_trace() {
    let (global_type, local_types) = finite_protocol();
    let spec = HarnessSpec::new(local_types, global_type, scenario_without_builtin_field());
    let adapter = FakeEnvironmentAdapter {
        handler: PassthroughHandler,
        topology: FakeTopologyModel,
        medium: FakeMediumModel,
        mobility: FakeMobilityModel,
        node_capabilities: FakeNodeCapabilityModel,
        admission: FakeAdmissionModel,
    };
    let harness = SimulationHarness::new(&adapter);
    let result = harness
        .run(&spec)
        .expect("environment-enabled run succeeds");
    let trace = &result.replay.environment_trace.records;

    assert!(trace.iter().any(|record| matches!(
        record,
        EnvironmentArtifact::Mobility { role, .. } if role == "A"
    )));
    assert!(trace.iter().any(|record| matches!(
        record,
        EnvironmentArtifact::Capability { role, .. } if role == "B"
    )));
    assert!(trace.iter().any(|record| matches!(
        record,
        EnvironmentArtifact::Reachability { from, to, reachable, .. }
        if from == "A" && to == "B" && *reachable
    )));
    assert!(trace.iter().any(|record| matches!(
        record,
        EnvironmentArtifact::Admission { from, to, admitted, .. }
        if from == "B" && to == "A" && !*admitted
    )));
    assert!(trace.iter().any(|record| matches!(
        record,
        EnvironmentArtifact::Medium { outcome, .. }
        if *outcome == MediumOutcomeKind::DeliverNow
    )));
}

#[test]
fn composed_environment_models_are_deterministic_for_same_seed_and_snapshot() {
    let (global_type, local_types) = finite_protocol();
    let spec = HarnessSpec::new(local_types, global_type, scenario_without_builtin_field());
    let adapter = FakeEnvironmentAdapter {
        handler: PassthroughHandler,
        topology: FakeTopologyModel,
        medium: FakeMediumModel,
        mobility: FakeMobilityModel,
        node_capabilities: FakeNodeCapabilityModel,
        admission: FakeAdmissionModel,
    };
    let harness = SimulationHarness::new(&adapter);

    let first = harness.run(&spec).expect("first environment-enabled run");
    let second = harness.run(&spec).expect("second environment-enabled run");

    assert_eq!(
        first.replay.environment_trace,
        second.replay.environment_trace
    );
    assert_eq!(first.replay.obs_trace, second.replay.obs_trace);
    assert_eq!(first.replay.effect_trace, second.replay.effect_trace);
    assert_eq!(
        first.replay.semantic_objects,
        second.replay.semantic_objects
    );
    assert_eq!(first.analysis, second.analysis);
}
