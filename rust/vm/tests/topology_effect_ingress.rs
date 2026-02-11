#![cfg(not(target_arch = "wasm32"))]
//! Topology perturbations must ingress through effect handlers.

#[allow(dead_code, unreachable_pub)]
mod helpers;

use std::sync::atomic::{AtomicBool, Ordering};
#[cfg(feature = "multi-thread")]
use std::{collections::BTreeMap, time::Duration};

use helpers::simple_send_recv_image;
use telltale_vm::coroutine::Value;
use telltale_vm::effect::{EffectHandler, SendDecision, TopologyPerturbation};
#[cfg(feature = "multi-thread")]
use telltale_vm::threaded::ThreadedVM;
use telltale_vm::vm::{VMConfig, VM};
#[cfg(feature = "multi-thread")]
use telltale_vm::CorruptionType;

#[derive(Debug)]
struct TopologyBurstHandler {
    emitted: AtomicBool,
}

impl TopologyBurstHandler {
    fn new() -> Self {
        Self {
            emitted: AtomicBool::new(false),
        }
    }
}

impl EffectHandler for TopologyBurstHandler {
    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        label: &str,
        _state: &[Value],
    ) -> Result<Value, String> {
        Ok(Value::Str(label.to_string()))
    }

    fn send_decision(
        &self,
        _sid: usize,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &[Value],
        payload: Option<Value>,
    ) -> Result<SendDecision, String> {
        Ok(SendDecision::Deliver(payload.unwrap_or(Value::Unit)))
    }

    fn handle_recv(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &mut Vec<Value>,
        _payload: &Value,
    ) -> Result<(), String> {
        Ok(())
    }

    fn handle_choose(
        &self,
        _role: &str,
        _partner: &str,
        labels: &[String],
        _state: &[Value],
    ) -> Result<String, String> {
        labels
            .first()
            .cloned()
            .ok_or_else(|| "no labels".to_string())
    }

    fn step(&self, _role: &str, _state: &mut Vec<Value>) -> Result<(), String> {
        Ok(())
    }

    fn topology_events(&self, _tick: u64) -> Result<Vec<TopologyPerturbation>, String> {
        if self.emitted.swap(true, Ordering::Relaxed) {
            return Ok(Vec::new());
        }
        Ok(vec![
            TopologyPerturbation::Crash {
                site: "A".to_string(),
            },
            TopologyPerturbation::Partition {
                from: "A".to_string(),
                to: "B".to_string(),
            },
        ])
    }
}

#[cfg(feature = "multi-thread")]
#[derive(Debug, Clone)]
struct ScriptedTopologyHandler {
    events_by_tick: BTreeMap<u64, Vec<TopologyPerturbation>>,
}

#[cfg(feature = "multi-thread")]
impl ScriptedTopologyHandler {
    fn new(events_by_tick: BTreeMap<u64, Vec<TopologyPerturbation>>) -> Self {
        Self { events_by_tick }
    }
}

#[cfg(feature = "multi-thread")]
impl EffectHandler for ScriptedTopologyHandler {
    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        label: &str,
        _state: &[Value],
    ) -> Result<Value, String> {
        Ok(Value::Str(label.to_string()))
    }

    fn send_decision(
        &self,
        _sid: usize,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &[Value],
        payload: Option<Value>,
    ) -> Result<SendDecision, String> {
        Ok(SendDecision::Deliver(payload.unwrap_or(Value::Unit)))
    }

    fn handle_recv(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &mut Vec<Value>,
        _payload: &Value,
    ) -> Result<(), String> {
        Ok(())
    }

    fn handle_choose(
        &self,
        _role: &str,
        _partner: &str,
        labels: &[String],
        _state: &[Value],
    ) -> Result<String, String> {
        labels
            .first()
            .cloned()
            .ok_or_else(|| "no labels".to_string())
    }

    fn step(&self, _role: &str, _state: &mut Vec<Value>) -> Result<(), String> {
        Ok(())
    }

    fn topology_events(&self, tick: u64) -> Result<Vec<TopologyPerturbation>, String> {
        Ok(self.events_by_tick.get(&tick).cloned().unwrap_or_default())
    }
}

#[test]
fn cooperative_vm_ingests_topology_events_before_instruction_effects() {
    let image = simple_send_recv_image("A", "B", "m");
    let handler = TopologyBurstHandler::new();
    let mut vm = VM::new(VMConfig::default());
    vm.load_choreography(&image).expect("load choreography");

    vm.step_round(&handler, 1).expect("step round");

    assert!(vm.crashed_sites().iter().any(|site| site == "A"));
    assert!(vm
        .partitioned_edges()
        .iter()
        .any(|edge| edge.sender == "A" && edge.receiver == "B"));
    let effects = vm.effect_trace();
    assert!(
        effects
            .first()
            .is_some_and(|e| e.effect_kind == "topology_event"),
        "topology events must be ingested before instruction effects"
    );
}

#[cfg(feature = "multi-thread")]
#[test]
fn threaded_vm_ingests_topology_events_before_instruction_effects() {
    let image = simple_send_recv_image("A", "B", "m");
    let handler = TopologyBurstHandler::new();
    let mut vm = ThreadedVM::with_workers(VMConfig::default(), 2);
    vm.load_choreography(&image).expect("load choreography");

    vm.step_round(&handler, 1).expect("step round");

    assert!(vm.crashed_sites().contains("A"));
    assert!(vm
        .partitioned_edges()
        .contains(&("A".to_string(), "B".to_string())));
    let effects = vm.effect_trace();
    assert!(
        effects
            .first()
            .is_some_and(|e| e.effect_kind == "topology_event"),
        "topology events must be ingested before instruction effects"
    );
}

#[cfg(feature = "multi-thread")]
fn topology_trace(entries: &[telltale_vm::effect::EffectTraceEntry]) -> Vec<TopologyPerturbation> {
    entries
        .iter()
        .filter_map(|entry| entry.topology.clone())
        .collect()
}

#[cfg(feature = "multi-thread")]
#[test]
fn crash_partition_heal_corrupt_timeout_traces_have_cross_runtime_parity() {
    let image = simple_send_recv_image("A", "B", "m");
    let mut script = BTreeMap::new();
    script.insert(
        1,
        vec![
            TopologyPerturbation::Crash {
                site: "A".to_string(),
            },
            TopologyPerturbation::Partition {
                from: "A".to_string(),
                to: "B".to_string(),
            },
            TopologyPerturbation::Corrupt {
                from: "A".to_string(),
                to: "B".to_string(),
                corruption: CorruptionType::BitFlip,
            },
            TopologyPerturbation::Timeout {
                site: "B".to_string(),
                duration: Duration::from_millis(5),
            },
        ],
    );
    let handler = ScriptedTopologyHandler::new(script);

    let mut coop = VM::new(VMConfig::default());
    coop.load_choreography(&image)
        .expect("load cooperative image");
    coop.step_round(&handler, 1)
        .expect("cooperative step round");

    let mut threaded = ThreadedVM::with_workers(VMConfig::default(), 2);
    threaded
        .load_choreography(&image)
        .expect("load threaded image");
    threaded
        .step_round(&handler, 1)
        .expect("threaded step round");

    assert_eq!(
        topology_trace(coop.effect_trace()),
        topology_trace(threaded.effect_trace())
    );
    assert!(coop.crashed_sites().contains(&"A".to_string()));
    assert!(threaded.crashed_sites().contains("A"));
    assert!(!coop.corrupted_edges().is_empty());
    assert!(!threaded.corrupted_edges().is_empty());
    assert!(!coop.timed_out_sites().is_empty());
    assert!(!threaded.timed_out_sites().is_empty());
    assert!(coop
        .trace()
        .iter()
        .any(|ev| matches!(ev, telltale_vm::vm::ObsEvent::Faulted { .. })));
    assert!(threaded
        .trace()
        .iter()
        .any(|ev| matches!(ev, telltale_vm::vm::ObsEvent::Faulted { .. })));
}

#[cfg(feature = "multi-thread")]
#[test]
fn partition_then_heal_restores_progress_without_faults() {
    let image = simple_send_recv_image("A", "B", "m");
    let mut script = BTreeMap::new();
    script.insert(
        1,
        vec![TopologyPerturbation::Partition {
            from: "A".to_string(),
            to: "B".to_string(),
        }],
    );
    script.insert(
        2,
        vec![TopologyPerturbation::Heal {
            from: "A".to_string(),
            to: "B".to_string(),
        }],
    );
    let handler = ScriptedTopologyHandler::new(script);

    let mut coop = VM::new(VMConfig::default());
    coop.load_choreography(&image)
        .expect("load cooperative image");
    coop.step_round(&handler, 1).expect("cooperative tick 1");
    coop.step_round(&handler, 1).expect("cooperative tick 2");
    coop.run(&handler, 32).expect("cooperative run after heal");

    let mut threaded = ThreadedVM::with_workers(VMConfig::default(), 2);
    threaded
        .load_choreography(&image)
        .expect("load threaded image");
    threaded.step_round(&handler, 1).expect("threaded tick 1");
    threaded.step_round(&handler, 1).expect("threaded tick 2");
    threaded.run(&handler, 32).expect("threaded run after heal");

    assert!(coop.partitioned_edges().is_empty());
    assert!(threaded.partitioned_edges().is_empty());
    assert!(coop
        .trace()
        .iter()
        .all(|ev| !matches!(ev, telltale_vm::vm::ObsEvent::Faulted { .. })));
    assert!(threaded
        .trace()
        .iter()
        .all(|ev| !matches!(ev, telltale_vm::vm::ObsEvent::Faulted { .. })));
}
