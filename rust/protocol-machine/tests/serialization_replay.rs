#![cfg(not(target_arch = "wasm32"))]
#![allow(missing_docs)]

use cfg_if::cfg_if;

#[allow(dead_code, unreachable_pub)]
#[path = "support/mod.rs"]
mod test_support;

use std::collections::BTreeMap;
use std::sync::Arc;
use std::time::Duration;
use telltale_types::{GlobalType, LocalTypeR};
use telltale_protocol_machine::effect::{
    EffectFailure, EffectHandler, EffectResult, EffectTraceEntry, RecordingEffectHandler,
    SendDecision, SendDecisionInput, TopologyPerturbation,
};
use telltale_protocol_machine::trace::normalize_trace_v1;
use telltale_protocol_machine::{CanonicalHandleKind, DelegationStatus, SemanticAuditRecord};
use telltale_protocol_machine::{ObsEvent, ProtocolMachine, ProtocolMachineConfig};
use test_support::{simple_send_recv_image, PassthroughHandler};

cfg_if! {
    if #[cfg(feature = "multi-thread")] {
        use telltale_protocol_machine::ThreadedProtocolMachine;
    }
}

#[derive(Debug, Clone)]
struct OrderedTopologyHandler {
    events_by_tick: BTreeMap<u64, Vec<TopologyPerturbation>>,
}

impl OrderedTopologyHandler {
    fn new(events_by_tick: BTreeMap<u64, Vec<TopologyPerturbation>>) -> Self {
        Self { events_by_tick }
    }
}

impl EffectHandler for OrderedTopologyHandler {
    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        label: &str,
        _state: &[telltale_protocol_machine::Value],
    ) -> EffectResult<telltale_protocol_machine::Value> {
        EffectResult::success(telltale_protocol_machine::Value::Str(label.to_string()))
    }

    fn send_decision(&self, input: SendDecisionInput<'_>) -> EffectResult<SendDecision> {
        EffectResult::success(SendDecision::Deliver(
            input.payload.unwrap_or(telltale_protocol_machine::Value::Unit),
        ))
    }

    fn handle_recv(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &mut Vec<telltale_protocol_machine::Value>,
        _payload: &telltale_protocol_machine::Value,
    ) -> EffectResult<()> {
        EffectResult::success(())
    }

    fn handle_choose(
        &self,
        _role: &str,
        _partner: &str,
        labels: &[String],
        _state: &[telltale_protocol_machine::Value],
    ) -> EffectResult<String> {
        match labels.first().cloned() {
            Some(label) => EffectResult::success(label),
            None => EffectResult::failure(EffectFailure::invalid_input("no labels")),
        }
    }

    fn step(&self, _role: &str, _state: &mut Vec<telltale_protocol_machine::Value>) -> EffectResult<()> {
        EffectResult::success(())
    }

    fn topology_events(&self, tick: u64) -> EffectResult<Vec<TopologyPerturbation>> {
        EffectResult::success(self.events_by_tick.get(&tick).cloned().unwrap_or_default())
    }
}

#[test]
fn canonical_replay_fragment_is_stable_for_identical_runs() {
    let image = simple_send_recv_image("A", "B", "m");
    let handler = PassthroughHandler;

    let mut vm_a = ProtocolMachine::new(ProtocolMachineConfig::default());
    vm_a.load_choreography(&image).expect("load vm_a");
    vm_a.run(&handler, 64).expect("run vm_a");

    let mut vm_b = ProtocolMachine::new(ProtocolMachineConfig::default());
    vm_b.load_choreography(&image).expect("load vm_b");
    vm_b.run(&handler, 64).expect("run vm_b");

    let lhs = serde_json::to_string(&vm_a.canonical_replay_fragment())
        .expect("serialize canonical replay fragment lhs");
    let rhs = serde_json::to_string(&vm_b.canonical_replay_fragment())
        .expect("serialize canonical replay fragment rhs");
    assert_eq!(lhs, rhs, "canonical replay fragments should match");
    assert!(
        vm_a.canonical_replay_fragment()
            .semantic_audit_log
            .iter()
            .any(|record| matches!(record, SemanticAuditRecord::EffectObservation { .. })),
        "canonical replay fragments should retain structured semantic audit records"
    );
    assert!(
        vm_a.canonical_replay_fragment()
            .semantic_audit_log
            .iter()
            .any(|record| matches!(record, SemanticAuditRecord::Publication { .. })),
        "canonical replay fragments should retain canonical publication records"
    );
    assert!(
        vm_a.canonical_replay_fragment()
            .semantic_objects
            .schema_version
            == telltale_protocol_machine::SEMANTIC_OBJECTS_SCHEMA_VERSION,
        "canonical replay fragments should retain canonical semantic-object bundles"
    );
    assert!(
        !vm_a
            .canonical_replay_fragment()
            .semantic_objects
            .publication_events
            .is_empty(),
        "canonical replay fragments should retain canonical publication events"
    );
}

#[test]
fn canonical_replay_fragment_sorts_topology_state() {
    let image = simple_send_recv_image("A", "B", "m");
    let mut events = BTreeMap::new();
    events.insert(
        1,
        vec![
            TopologyPerturbation::Timeout {
                site: "B".to_string(),
                duration: Duration::from_millis(2),
            },
            TopologyPerturbation::Crash {
                site: "A".to_string(),
            },
            TopologyPerturbation::Partition {
                from: "B".to_string(),
                to: "A".to_string(),
            },
        ],
    );
    let handler = OrderedTopologyHandler::new(events);

    let mut vm = ProtocolMachine::new(ProtocolMachineConfig::default());
    vm.load_choreography(&image).expect("load vm");
    vm.step_round(&handler, 1)
        .expect("step with topology events");

    let fragment = vm.canonical_replay_fragment();
    assert_eq!(
        fragment.schema_version,
        telltale_protocol_machine::serialization::SERIALIZATION_SCHEMA_VERSION
    );
    assert!(fragment.crashed_sites.windows(2).all(|w| w[0] <= w[1]));
    assert!(fragment.partitioned_edges.windows(2).all(|w| w[0] <= w[1]));
    assert!(
        fragment.semantic_audit_log.iter().any(|record| matches!(
            record,
            SemanticAuditRecord::TimeoutIssued { site, .. } if site == "B"
        )),
        "topology-triggered timeout should be preserved in semantic audit records"
    );
    assert!(
        fragment.semantic_audit_log.iter().any(|record| matches!(
            record,
            SemanticAuditRecord::EffectObservation {
                effect_interface: Some(interface),
                effect_operation: Some(operation),
                ..
            } if interface == "Runtime" && operation == "topologyEvents"
        )),
        "topology ingress should remain visible as a structured effect observation"
    );
    assert_eq!(
        fragment.semantic_objects.schema_version,
        telltale_protocol_machine::SEMANTIC_OBJECTS_SCHEMA_VERSION
    );
}

#[test]
fn vm_config_schema_versions_remain_compatible() {
    let default_cfg = serde_json::to_value(ProtocolMachineConfig::default())
        .expect("serialize default ProtocolMachine config");

    let mut missing_version = default_cfg.clone();
    missing_version
        .as_object_mut()
        .expect("config object")
        .remove("config_schema_version");
    let decoded_missing: ProtocolMachineConfig =
        serde_json::from_value(missing_version).expect("decode config without schema version");
    assert_eq!(decoded_missing.config_schema_version, 1);

    let mut v2_cfg = default_cfg;
    v2_cfg
        .as_object_mut()
        .expect("config object")
        .insert("config_schema_version".to_string(), serde_json::json!(2));
    let decoded_v2: ProtocolMachineConfig =
        serde_json::from_value(v2_cfg).expect("decode schema version 2");
    assert_eq!(decoded_v2.config_schema_version, 2);

    let vm = ProtocolMachine::new(decoded_v2);
    assert_eq!(vm.config().config_schema_version, 2);
}

#[test]
fn normalize_trace_v1_emits_versioned_payload() {
    let trace = vec![ObsEvent::Halted {
        tick: 4,
        coro_id: 7,
    }];
    let normalized = normalize_trace_v1(&trace);
    assert_eq!(normalized.schema_version, 1);
    assert_eq!(normalized.events.len(), 1);
}

#[test]
fn run_replay_shared_accepts_arc_backed_trace() {
    let image = simple_send_recv_image("A", "B", "m");
    let handler = PassthroughHandler;
    let recording = RecordingEffectHandler::new(&handler);

    let mut baseline = ProtocolMachine::new(ProtocolMachineConfig::default());
    baseline.load_choreography(&image).expect("load baseline");
    baseline.run(&recording, 64).expect("run baseline");
    let baseline_obs = baseline.canonical_replay_fragment().obs_trace;
    let baseline_effect_semantics: Vec<_> = baseline
        .effect_trace()
        .iter()
        .map(|entry| {
            (
                entry.effect_kind.clone(),
                entry.inputs.clone(),
                entry.outputs.clone(),
                entry.ordering_key,
            )
        })
        .collect();
    let replay_trace: Arc<[EffectTraceEntry]> = Arc::from(recording.effect_trace());

    let mut replay_vm = ProtocolMachine::new(ProtocolMachineConfig::default());
    replay_vm
        .load_choreography(&image)
        .expect("load replay ProtocolMachine");
    replay_vm
        .run_replay_shared(&handler, replay_trace, 64)
        .expect("run replay ProtocolMachine");
    let replay_obs = replay_vm.canonical_replay_fragment().obs_trace;
    let replay_effect_semantics: Vec<_> = replay_vm
        .effect_trace()
        .iter()
        .map(|entry| {
            (
                entry.effect_kind.clone(),
                entry.inputs.clone(),
                entry.outputs.clone(),
                entry.ordering_key,
            )
        })
        .collect();

    assert_eq!(
        baseline_obs, replay_obs,
        "arc-backed replay must preserve deterministic observable outputs"
    );
    assert_eq!(
        baseline_effect_semantics, replay_effect_semantics,
        "arc-backed replay must preserve effect semantics (excluding handler identity)"
    );
}

#[test]
fn semantic_object_bundle_roundtrips_through_replay_fragment() {
    let image = simple_send_recv_image("A", "B", "m");
    let handler = PassthroughHandler;

    let mut vm = ProtocolMachine::new(ProtocolMachineConfig::default());
    vm.load_choreography(&image).expect("load vm");
    vm.run(&handler, 64).expect("run vm");

    let fragment = vm.canonical_replay_fragment();
    let encoded = serde_json::to_string(&fragment).expect("serialize replay fragment");
    let decoded: telltale_protocol_machine::CanonicalReplayFragmentV1 =
        serde_json::from_str(&encoded).expect("deserialize replay fragment");

    assert_eq!(
        decoded.semantic_objects.schema_version,
        telltale_protocol_machine::SEMANTIC_OBJECTS_SCHEMA_VERSION
    );
    assert!(
        decoded.semantic_objects == vm.semantic_objects(),
        "semantic object bundle should roundtrip exactly through replay-fragment serialization"
    );
    assert!(
        decoded
            .semantic_objects
            .canonical_handles
            .iter()
            .all(|handle| matches!(
                handle.kind,
                CanonicalHandleKind::Materialization | CanonicalHandleKind::Handoff
            )),
        "semantic object bundle should preserve canonical handle kinds"
    );
}

fn transfer_image() -> telltale_protocol_machine::loader::CodeImage {
    let mut local_types = BTreeMap::new();
    local_types.insert("A".to_string(), LocalTypeR::End);
    local_types.insert("B".to_string(), LocalTypeR::End);

    let mut programs = BTreeMap::new();
    programs.insert(
        "A".to_string(),
        vec![
            telltale_protocol_machine::instr::Instr::Set {
                dst: 1,
                val: telltale_protocol_machine::instr::ImmValue::Nat(1),
            },
            telltale_protocol_machine::instr::Instr::Transfer {
                endpoint: 0,
                target: 1,
                bundle: 2,
            },
            telltale_protocol_machine::instr::Instr::Halt,
        ],
    );
    programs.insert("B".to_string(), vec![telltale_protocol_machine::instr::Instr::Halt]);

    telltale_protocol_machine::loader::CodeImage {
        programs,
        global_type: GlobalType::End,
        local_types,
    }
}

#[test]
fn ownership_transfer_replay_preserves_observable_trace() {
    let image = transfer_image();
    let handler = PassthroughHandler;
    let recording = RecordingEffectHandler::new(&handler);

    let mut baseline = ProtocolMachine::new(ProtocolMachineConfig::default());
    baseline.load_choreography(&image).expect("load baseline");
    baseline.run(&recording, 32).expect("run baseline");
    let baseline_obs = baseline.canonical_replay_fragment().obs_trace;
    let replay_trace: Arc<[EffectTraceEntry]> = Arc::from(recording.effect_trace());

    let mut replay_vm = ProtocolMachine::new(ProtocolMachineConfig::default());
    replay_vm
        .load_choreography(&image)
        .expect("load replay ProtocolMachine");
    replay_vm
        .run_replay_shared(&handler, replay_trace, 32)
        .expect("run replay ProtocolMachine");
    let replay_obs = replay_vm.canonical_replay_fragment().obs_trace;

    assert_eq!(baseline_obs, replay_obs);
    assert!(
        replay_obs
            .iter()
            .any(|event| matches!(event, ObsEvent::Transferred { role, .. } if role == "A")),
        "replayed ownership transfer must retain the transfer observable"
    );
    assert!(
        baseline
            .canonical_replay_fragment()
            .semantic_audit_log
            .iter()
            .any(|record| matches!(
                record,
                SemanticAuditRecord::Delegation { status, .. } if *status == DelegationStatus::Committed
            )),
        "ownership transfer replay should preserve committed delegation audit records"
    );
}

cfg_if! {
    if #[cfg(feature = "multi-thread")] {
        fn obs_signature(trace: &[ObsEvent]) -> Vec<String> {
            trace
                .iter()
                .map(|event| match event {
                    ObsEvent::Opened { session, roles, .. } => {
                        format!("opened:{session}:{}", roles.join(","))
                    }
                    ObsEvent::Sent {
                        session,
                        from,
                        to,
                        label,
                        ..
                    } => format!("sent:{session}:{from}:{to}:{label}"),
                    ObsEvent::Received {
                        session,
                        from,
                        to,
                        label,
                        ..
                    } => format!("received:{session}:{from}:{to}:{label}"),
                    ObsEvent::Invoked { coro_id, role, .. } => format!("invoked:{coro_id}:{role}"),
                    ObsEvent::Halted { coro_id, .. } => format!("halted:{coro_id}"),
                    ObsEvent::OutputConditionChecked {
                        predicate_ref,
                        passed,
                        ..
                    } => format!("output_check:{predicate_ref}:{passed}"),
                    other => format!("{other:?}"),
                })
                .collect()
        }

        #[test]
        fn canonical_replay_fragment_matches_cross_target_for_deterministic_run() {
            let image = simple_send_recv_image("A", "B", "m");
            let handler = PassthroughHandler;

            let mut coop = ProtocolMachine::new(ProtocolMachineConfig::default());
            coop.load_choreography(&image)
                .expect("load cooperative image");
            coop.run(&handler, 64).expect("run cooperative ProtocolMachine");

            let mut threaded = ThreadedProtocolMachine::with_workers(ProtocolMachineConfig::default(), 2);
            threaded
                .load_choreography(&image)
                .expect("load threaded image");
            threaded.run(&handler, 64).expect("run threaded ProtocolMachine");

            assert_eq!(
                obs_signature(&coop.canonical_replay_fragment().obs_trace),
                obs_signature(&threaded.canonical_replay_fragment().obs_trace),
                "normalized observable traces should match across targets"
            );
        }

        #[test]
        fn threaded_run_replay_shared_accepts_arc_backed_trace() {
            let image = simple_send_recv_image("A", "B", "m");
            let handler = PassthroughHandler;
            let recording = RecordingEffectHandler::new(&handler);

            let mut baseline = ThreadedProtocolMachine::with_workers(ProtocolMachineConfig::default(), 2);
            baseline.load_choreography(&image).expect("load baseline");
            baseline.run(&recording, 64).expect("run baseline");
            let baseline_obs = baseline.canonical_replay_fragment().obs_trace;
            let baseline_effect_semantics: Vec<_> = baseline
                .effect_trace()
                .iter()
                .map(|entry| {
                    (
                        entry.effect_kind.clone(),
                        entry.inputs.clone(),
                        entry.outputs.clone(),
                        entry.ordering_key,
                    )
                })
                .collect();
            let replay_trace: Arc<[EffectTraceEntry]> = Arc::from(recording.effect_trace());

            let mut replay_vm = ThreadedProtocolMachine::with_workers(ProtocolMachineConfig::default(), 2);
            replay_vm.load_choreography(&image).expect("load replay ProtocolMachine");
            replay_vm
                .run_replay_shared(&handler, replay_trace, 64)
                .expect("run replay ProtocolMachine");
            let replay_obs = replay_vm.canonical_replay_fragment().obs_trace;
            let replay_effect_semantics: Vec<_> = replay_vm
                .effect_trace()
                .iter()
                .map(|entry| {
                    (
                        entry.effect_kind.clone(),
                        entry.inputs.clone(),
                        entry.outputs.clone(),
                        entry.ordering_key,
                    )
                })
                .collect();

            assert_eq!(
                baseline_obs, replay_obs,
                "threaded arc-backed replay must preserve deterministic observable outputs"
            );
            assert_eq!(
                baseline_effect_semantics, replay_effect_semantics,
                "threaded arc-backed replay must preserve effect semantics (excluding handler identity)"
            );
        }

        #[test]
        fn threaded_ownership_transfer_replay_preserves_observable_trace() {
            let image = transfer_image();
            let handler = PassthroughHandler;
            let recording = RecordingEffectHandler::new(&handler);

            let mut baseline = ThreadedProtocolMachine::with_workers(ProtocolMachineConfig::default(), 2);
            baseline.load_choreography(&image).expect("load baseline");
            baseline.run(&recording, 32).expect("run baseline");
            let baseline_obs = baseline.canonical_replay_fragment().obs_trace;
            let replay_trace: Arc<[EffectTraceEntry]> = Arc::from(recording.effect_trace());

            let mut replay_vm = ThreadedProtocolMachine::with_workers(ProtocolMachineConfig::default(), 2);
            replay_vm.load_choreography(&image).expect("load replay ProtocolMachine");
            replay_vm
                .run_replay_shared(&handler, replay_trace, 32)
                .expect("run replay ProtocolMachine");
            let replay_obs = replay_vm.canonical_replay_fragment().obs_trace;

            assert_eq!(baseline_obs, replay_obs);
            assert!(
                replay_obs
                    .iter()
                    .any(|event| matches!(event, ObsEvent::Transferred { role, .. } if role == "A")),
                "replayed threaded ownership transfer must retain the transfer observable"
            );
        }
    }
}
