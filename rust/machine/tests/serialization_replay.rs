#![allow(missing_docs)]
#![cfg(not(target_arch = "wasm32"))]
//! Serialization round-trip and replay conformance tests.

use cfg_if::cfg_if;

#[allow(dead_code, unreachable_pub)]
#[path = "support/mod.rs"]
mod test_support;

use std::collections::BTreeMap;
use std::sync::Arc;
use std::time::Duration;
use telltale_machine::durable::WalSyncRequest;
use telltale_machine::model::effects::{
    EffectFailure, EffectHandler, EffectResult, EffectTraceEntry, RecordingEffectHandler,
    SendDecision, SendDecisionInput, TopologyPerturbation,
};
use telltale_machine::model::output_condition::OutputConditionHint;
use telltale_machine::trace::normalize_trace_v1;
use telltale_machine::{CanonicalHandleKind, DelegationStatus, SemanticAuditRecord};
use telltale_machine::{ObsEvent, ProtocolMachine, ProtocolMachineConfig};
use telltale_types::{GlobalType, LocalTypeR};
use test_support::{simple_send_recv_image, PassthroughHandler};

cfg_if! {
    if #[cfg(feature = "multi-thread")] {
        use telltale_machine::ThreadedProtocolMachine;
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
        _state: &[telltale_machine::Value],
    ) -> EffectResult<telltale_machine::Value> {
        EffectResult::success(telltale_machine::Value::Str(label.to_string()))
    }

    fn send_decision(&self, input: SendDecisionInput<'_>) -> EffectResult<SendDecision> {
        EffectResult::success(SendDecision::Deliver(
            input.payload.unwrap_or(telltale_machine::Value::Unit),
        ))
    }

    fn handle_recv(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &mut Vec<telltale_machine::Value>,
        _payload: &telltale_machine::Value,
    ) -> EffectResult<()> {
        EffectResult::success(())
    }

    fn handle_choose(
        &self,
        _role: &str,
        _partner: &str,
        labels: &[String],
        _state: &[telltale_machine::Value],
    ) -> EffectResult<String> {
        match labels.first().cloned() {
            Some(label) => EffectResult::success(label),
            None => EffectResult::failure(EffectFailure::invalid_input("no labels")),
        }
    }

    fn step(&self, _role: &str, _state: &mut Vec<telltale_machine::Value>) -> EffectResult<()> {
        EffectResult::success(())
    }

    fn topology_events(&self, tick: u64) -> EffectResult<Vec<TopologyPerturbation>> {
        EffectResult::success(self.events_by_tick.get(&tick).cloned().unwrap_or_default())
    }
}

#[derive(Debug, Clone, Default)]
struct InternalEffectReplayHandler;

impl EffectHandler for InternalEffectReplayHandler {
    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        label: &str,
        _state: &[telltale_machine::Value],
    ) -> EffectResult<telltale_machine::Value> {
        EffectResult::success(telltale_machine::Value::Str(label.to_string()))
    }

    fn send_decision(&self, input: SendDecisionInput<'_>) -> EffectResult<SendDecision> {
        EffectResult::success(SendDecision::Deliver(
            input.payload.unwrap_or(telltale_machine::Value::Unit),
        ))
    }

    fn handle_recv(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &mut Vec<telltale_machine::Value>,
        _payload: &telltale_machine::Value,
    ) -> EffectResult<()> {
        EffectResult::success(())
    }

    fn handle_choose(
        &self,
        _role: &str,
        _partner: &str,
        labels: &[String],
        _state: &[telltale_machine::Value],
    ) -> EffectResult<String> {
        match labels.first().cloned() {
            Some(label) => EffectResult::success(label),
            None => EffectResult::failure(EffectFailure::invalid_input("no labels")),
        }
    }

    fn step(&self, _role: &str, _state: &mut Vec<telltale_machine::Value>) -> EffectResult<()> {
        EffectResult::success(())
    }

    fn topology_events(&self, tick: u64) -> EffectResult<Vec<TopologyPerturbation>> {
        let events = match tick {
            1 => vec![TopologyPerturbation::Partition {
                from: "A".to_string(),
                to: "B".to_string(),
            }],
            2 => vec![TopologyPerturbation::Heal {
                from: "A".to_string(),
                to: "B".to_string(),
            }],
            _ => Vec::new(),
        };
        EffectResult::success(events)
    }

    fn output_condition_hint(
        &self,
        sid: usize,
        role: &str,
        _state: &[telltale_machine::Value],
    ) -> Option<OutputConditionHint> {
        Some(OutputConditionHint {
            predicate_ref: "machine.replay.internal_effects".to_string(),
            witness_ref: Some(format!("sid:{sid}:role:{role}")),
        })
    }

    fn supports_wal_sync(&self) -> bool {
        true
    }

    fn wal_sync(&self, _sync: &WalSyncRequest) -> EffectResult<()> {
        EffectResult::success(())
    }
}

fn assert_internal_effect_replay_exact(baseline: &ProtocolMachine, replay: &ProtocolMachine) {
    assert_eq!(
        baseline.canonical_replay_fragment().obs_trace,
        replay.canonical_replay_fragment().obs_trace,
        "replay must preserve observable outputs exactly when internal effects are replayed"
    );
    assert_eq!(
        baseline.effect_trace(),
        replay.effect_trace(),
        "replay must preserve raw effect trace entries exactly"
    );
    assert_eq!(
        baseline.effect_exchanges(),
        replay.effect_exchanges(),
        "replay must preserve typed effect exchanges exactly"
    );
    assert_eq!(
        baseline.semantic_objects(),
        replay.semantic_objects(),
        "replay must preserve semantic objects exactly"
    );
    assert!(
        baseline.effect_exchanges().iter().any(|exchange| matches!(
            exchange.request.body,
            telltale_machine::model::effects::EffectRequestBody::OutputConditionHint { .. }
        )),
        "baseline exchanges should include output-condition hint effects"
    );
    assert!(
        baseline.effect_exchanges().iter().any(|exchange| matches!(
            exchange.request.body,
            telltale_machine::model::effects::EffectRequestBody::WalSync { .. }
        )),
        "baseline exchanges should include wal_sync effects"
    );
    assert!(
        baseline
            .effect_trace()
            .iter()
            .any(|entry| entry.effect_kind == "topology_event"),
        "baseline trace should include topology ingress effects"
    );
}

#[test]
fn canonical_replay_fragment_is_stable_for_identical_runs() {
    let image = simple_send_recv_image("A", "B", "m");
    let handler = PassthroughHandler;

    let mut machine_a = ProtocolMachine::new(ProtocolMachineConfig::default());
    machine_a.load_choreography(&image).expect("load machine_a");
    machine_a.run(&handler, 64).expect("run machine_a");

    let mut machine_b = ProtocolMachine::new(ProtocolMachineConfig::default());
    machine_b.load_choreography(&image).expect("load machine_b");
    machine_b.run(&handler, 64).expect("run machine_b");

    let lhs = serde_json::to_string(&machine_a.canonical_replay_fragment())
        .expect("serialize canonical replay fragment lhs");
    let rhs = serde_json::to_string(&machine_b.canonical_replay_fragment())
        .expect("serialize canonical replay fragment rhs");
    assert_eq!(lhs, rhs, "canonical replay fragments should match");
    assert!(
        machine_a
            .canonical_replay_fragment()
            .semantic_audit_log
            .iter()
            .any(|record| matches!(record, SemanticAuditRecord::EffectObservation { .. })),
        "canonical replay fragments should retain structured semantic audit records"
    );
    assert!(
        machine_a
            .canonical_replay_fragment()
            .semantic_audit_log
            .iter()
            .any(|record| matches!(record, SemanticAuditRecord::Publication { .. })),
        "canonical replay fragments should retain canonical publication records"
    );
    assert!(
        machine_a
            .canonical_replay_fragment()
            .semantic_objects
            .schema_version
            == telltale_machine::SEMANTIC_OBJECTS_SCHEMA_VERSION,
        "canonical replay fragments should retain canonical semantic-object bundles"
    );
    assert!(
        !machine_a
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

    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    machine.load_choreography(&image).expect("load machine");
    machine
        .step_round(&handler, 1)
        .expect("step with topology events");

    let fragment = machine.canonical_replay_fragment();
    assert_eq!(
        fragment.schema_version,
        telltale_machine::serialization::SERIALIZATION_SCHEMA_VERSION
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
        telltale_machine::SEMANTIC_OBJECTS_SCHEMA_VERSION
    );
}

#[test]
fn protocol_machine_config_schema_versions_remain_compatible() {
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

    let machine = ProtocolMachine::new(decoded_v2);
    assert_eq!(machine.config().config_schema_version, 2);
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
fn replay_preserves_internal_effects_exactly_when_recorded() {
    let image = simple_send_recv_image("A", "B", "m");
    let handler = InternalEffectReplayHandler;
    let recording = RecordingEffectHandler::new(&handler);

    let mut baseline = ProtocolMachine::new(ProtocolMachineConfig::default());
    baseline.load_choreography(&image).expect("load baseline");
    baseline.run(&recording, 64).expect("run baseline");

    let encoded_trace =
        serde_json::to_vec(&recording.effect_trace()).expect("serialize recorded effect trace");
    let decoded_trace: Vec<EffectTraceEntry> =
        serde_json::from_slice(&encoded_trace).expect("deserialize recorded effect trace");

    let mut replay_vm = ProtocolMachine::new(ProtocolMachineConfig::default());
    replay_vm
        .load_choreography(&image)
        .expect("load replay ProtocolMachine");
    replay_vm
        .run_replay_shared(&handler, Arc::from(decoded_trace), 64)
        .expect("run replay ProtocolMachine");

    assert_internal_effect_replay_exact(&baseline, &replay_vm);
}

#[test]
fn semantic_object_bundle_roundtrips_through_replay_fragment() {
    let image = simple_send_recv_image("A", "B", "m");
    let handler = PassthroughHandler;

    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    machine.load_choreography(&image).expect("load machine");
    machine.run(&handler, 64).expect("run machine");

    let fragment = machine.canonical_replay_fragment();
    let encoded = serde_json::to_string(&fragment).expect("serialize replay fragment");
    let decoded: telltale_machine::CanonicalReplayFragmentV1 =
        serde_json::from_str(&encoded).expect("deserialize replay fragment");

    assert_eq!(
        decoded.semantic_objects.schema_version,
        telltale_machine::SEMANTIC_OBJECTS_SCHEMA_VERSION
    );
    assert!(
        decoded.semantic_objects == machine.semantic_objects(),
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

fn transfer_image() -> telltale_machine::runtime::loader::CodeImage {
    let mut local_types = BTreeMap::new();
    local_types.insert("A".to_string(), LocalTypeR::End);
    local_types.insert("B".to_string(), LocalTypeR::End);

    let mut programs = BTreeMap::new();
    programs.insert(
        "A".to_string(),
        vec![
            telltale_machine::instr::Instr::Set {
                dst: 1,
                val: telltale_machine::instr::ImmValue::Nat(1),
            },
            telltale_machine::instr::Instr::Transfer {
                endpoint: 0,
                target: 1,
                bundle: 2,
            },
            telltale_machine::instr::Instr::Halt,
        ],
    );
    programs.insert("B".to_string(), vec![telltale_machine::instr::Instr::Halt]);

    telltale_machine::runtime::loader::CodeImage {
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
        fn threaded_replay_preserves_internal_effects_exactly_when_recorded() {
            let image = simple_send_recv_image("A", "B", "m");
            let handler = InternalEffectReplayHandler;
            let recording = RecordingEffectHandler::new(&handler);

            let mut baseline =
                ThreadedProtocolMachine::with_workers(ProtocolMachineConfig::default(), 2);
            baseline.load_choreography(&image).expect("load baseline");
            baseline.run(&recording, 64).expect("run baseline");

            let encoded_trace = serde_json::to_vec(&recording.effect_trace())
                .expect("serialize recorded effect trace");
            let decoded_trace: Vec<EffectTraceEntry> =
                serde_json::from_slice(&encoded_trace).expect("deserialize recorded effect trace");

            let mut replay_vm =
                ThreadedProtocolMachine::with_workers(ProtocolMachineConfig::default(), 2);
            replay_vm
                .load_choreography(&image)
                .expect("load replay ProtocolMachine");
            replay_vm
                .run_replay_shared(&handler, Arc::from(decoded_trace), 64)
                .expect("run replay ProtocolMachine");

            assert_eq!(
                baseline.canonical_replay_fragment().obs_trace,
                replay_vm.canonical_replay_fragment().obs_trace,
                "threaded replay must preserve observable outputs exactly"
            );
            assert_eq!(
                baseline.effect_trace(),
                replay_vm.effect_trace(),
                "threaded replay must preserve raw effect trace entries exactly"
            );
            assert_eq!(
                baseline.effect_exchanges(),
                replay_vm.effect_exchanges(),
                "threaded replay must preserve typed effect exchanges exactly"
            );
            assert_eq!(
                baseline.semantic_objects(),
                replay_vm.semantic_objects(),
                "threaded replay must preserve semantic objects exactly"
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
