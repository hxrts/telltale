#![cfg(not(target_arch = "wasm32"))]
#![allow(missing_docs)]

#[allow(dead_code, unreachable_pub)]
mod helpers;

use helpers::{simple_send_recv_image, PassthroughHandler};
use std::collections::BTreeMap;
use std::time::Duration;
use telltale_vm::effect::{EffectHandler, SendDecision, TopologyPerturbation};
#[cfg(feature = "multi-thread")]
use telltale_vm::threaded::ThreadedVM;
use telltale_vm::trace::normalize_trace_v1;
use telltale_vm::vm::{ObsEvent, VMConfig, VM};

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
    ) -> Result<telltale_vm::Value, String> {
        Ok(telltale_vm::Value::Str(label.to_string()))
    }

    fn send_decision(
        &self,
        _sid: usize,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &[telltale_vm::Value],
        payload: Option<telltale_vm::Value>,
    ) -> Result<SendDecision, String> {
        Ok(SendDecision::Deliver(
            payload.unwrap_or(telltale_vm::Value::Unit),
        ))
    }

    fn handle_recv(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &mut Vec<telltale_vm::Value>,
        _payload: &telltale_vm::Value,
    ) -> Result<(), String> {
        Ok(())
    }

    fn handle_choose(
        &self,
        _role: &str,
        _partner: &str,
        labels: &[String],
        _state: &[telltale_vm::Value],
    ) -> Result<String, String> {
        labels
            .first()
            .cloned()
            .ok_or_else(|| "no labels".to_string())
    }

    fn step(&self, _role: &str, _state: &mut Vec<telltale_vm::Value>) -> Result<(), String> {
        Ok(())
    }

    fn topology_events(&self, tick: u64) -> Result<Vec<TopologyPerturbation>, String> {
        Ok(self.events_by_tick.get(&tick).cloned().unwrap_or_default())
    }
}

#[cfg(feature = "multi-thread")]
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
    assert_eq!(fragment.schema_version, 1);
    assert!(fragment.crashed_sites.windows(2).all(|w| w[0] <= w[1]));
    assert!(fragment.partitioned_edges.windows(2).all(|w| w[0] <= w[1]));
}

#[cfg(feature = "multi-thread")]
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
