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
use telltale_vm::effect::{
    EffectFailure, EffectHandler, EffectResult, EffectTraceEntry, RecordingEffectHandler,
    SendDecision, SendDecisionInput, TopologyPerturbation,
};
use telltale_vm::trace::normalize_trace_v1;
use telltale_vm::vm::{ObsEvent, VMConfig, VM};
use telltale_vm::{DelegationStatus, SemanticAuditRecord};
use test_support::{simple_send_recv_image, PassthroughHandler};

cfg_if! {
    if #[cfg(feature = "multi-thread")] {
        use telltale_vm::threaded::ThreadedVM;
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
        _state: &[telltale_vm::Value],
    ) -> EffectResult<telltale_vm::Value> {
        EffectResult::success(telltale_vm::Value::Str(label.to_string()))
    }

    fn send_decision(&self, input: SendDecisionInput<'_>) -> EffectResult<SendDecision> {
        EffectResult::success(SendDecision::Deliver(
            input.payload.unwrap_or(telltale_vm::Value::Unit),
        ))
    }

    fn handle_recv(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &mut Vec<telltale_vm::Value>,
        _payload: &telltale_vm::Value,
    ) -> EffectResult<()> {
        EffectResult::success(())
    }

    fn handle_choose(
        &self,
        _role: &str,
        _partner: &str,
        labels: &[String],
        _state: &[telltale_vm::Value],
    ) -> EffectResult<String> {
        match labels.first().cloned() {
            Some(label) => EffectResult::success(label),
            None => EffectResult::failure(EffectFailure::invalid_input("no labels")),
        }
    }

    fn step(&self, _role: &str, _state: &mut Vec<telltale_vm::Value>) -> EffectResult<()> {
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

    let mut vm_a = VM::new(VMConfig::default());
    vm_a.load_choreography(&image).expect("load vm_a");
    vm_a.run(&handler, 64).expect("run vm_a");

    let mut vm_b = VM::new(VMConfig::default());
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

    let mut vm = VM::new(VMConfig::default());
    vm.load_choreography(&image).expect("load vm");
    vm.step_round(&handler, 1)
        .expect("step with topology events");

    let fragment = vm.canonical_replay_fragment();
    assert_eq!(
        fragment.schema_version,
        telltale_vm::serialization::SERIALIZATION_SCHEMA_VERSION
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
}

#[test]
fn vm_config_schema_versions_remain_compatible() {
    let default_cfg =
        serde_json::to_value(VMConfig::default()).expect("serialize default VM config");

    let mut missing_version = default_cfg.clone();
    missing_version
        .as_object_mut()
        .expect("config object")
        .remove("config_schema_version");
    let decoded_missing: VMConfig =
        serde_json::from_value(missing_version).expect("decode config without schema version");
    assert_eq!(decoded_missing.config_schema_version, 1);

    let mut v2_cfg = default_cfg;
    v2_cfg
        .as_object_mut()
        .expect("config object")
        .insert("config_schema_version".to_string(), serde_json::json!(2));
    let decoded_v2: VMConfig = serde_json::from_value(v2_cfg).expect("decode schema version 2");
    assert_eq!(decoded_v2.config_schema_version, 2);

    let vm = VM::new(decoded_v2);
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

    let mut baseline = VM::new(VMConfig::default());
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

    let mut replay_vm = VM::new(VMConfig::default());
    replay_vm.load_choreography(&image).expect("load replay VM");
    replay_vm
        .run_replay_shared(&handler, replay_trace, 64)
        .expect("run replay VM");
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

fn transfer_image() -> telltale_vm::loader::CodeImage {
    let mut local_types = BTreeMap::new();
    local_types.insert("A".to_string(), LocalTypeR::End);
    local_types.insert("B".to_string(), LocalTypeR::End);

    let mut programs = BTreeMap::new();
    programs.insert(
        "A".to_string(),
        vec![
            telltale_vm::instr::Instr::Set {
                dst: 1,
                val: telltale_vm::instr::ImmValue::Nat(1),
            },
            telltale_vm::instr::Instr::Transfer {
                endpoint: 0,
                target: 1,
                bundle: 2,
            },
            telltale_vm::instr::Instr::Halt,
        ],
    );
    programs.insert("B".to_string(), vec![telltale_vm::instr::Instr::Halt]);

    telltale_vm::loader::CodeImage {
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

    let mut baseline = VM::new(VMConfig::default());
    baseline.load_choreography(&image).expect("load baseline");
    baseline.run(&recording, 32).expect("run baseline");
    let baseline_obs = baseline.canonical_replay_fragment().obs_trace;
    let replay_trace: Arc<[EffectTraceEntry]> = Arc::from(recording.effect_trace());

    let mut replay_vm = VM::new(VMConfig::default());
    replay_vm.load_choreography(&image).expect("load replay VM");
    replay_vm
        .run_replay_shared(&handler, replay_trace, 32)
        .expect("run replay VM");
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

            let mut coop = VM::new(VMConfig::default());
            coop.load_choreography(&image)
                .expect("load cooperative image");
            coop.run(&handler, 64).expect("run cooperative VM");

            let mut threaded = ThreadedVM::with_workers(VMConfig::default(), 2);
            threaded
                .load_choreography(&image)
                .expect("load threaded image");
            threaded.run(&handler, 64).expect("run threaded VM");

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

            let mut baseline = ThreadedVM::with_workers(VMConfig::default(), 2);
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

            let mut replay_vm = ThreadedVM::with_workers(VMConfig::default(), 2);
            replay_vm.load_choreography(&image).expect("load replay VM");
            replay_vm
                .run_replay_shared(&handler, replay_trace, 64)
                .expect("run replay VM");
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

            let mut baseline = ThreadedVM::with_workers(VMConfig::default(), 2);
            baseline.load_choreography(&image).expect("load baseline");
            baseline.run(&recording, 32).expect("run baseline");
            let baseline_obs = baseline.canonical_replay_fragment().obs_trace;
            let replay_trace: Arc<[EffectTraceEntry]> = Arc::from(recording.effect_trace());

            let mut replay_vm = ThreadedVM::with_workers(VMConfig::default(), 2);
            replay_vm.load_choreography(&image).expect("load replay VM");
            replay_vm
                .run_replay_shared(&handler, replay_trace, 32)
                .expect("run replay VM");
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
