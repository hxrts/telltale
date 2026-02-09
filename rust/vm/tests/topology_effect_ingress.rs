#![cfg(not(target_arch = "wasm32"))]
//! Topology perturbations must ingress through effect handlers.

#[allow(dead_code, unreachable_pub)]
mod helpers;

use std::sync::atomic::{AtomicBool, Ordering};

use helpers::simple_send_recv_image;
use telltale_vm::coroutine::Value;
use telltale_vm::effect::{EffectHandler, SendDecision, TopologyPerturbation};
#[cfg(feature = "multi-thread")]
use telltale_vm::threaded::ThreadedVM;
use telltale_vm::vm::{VMConfig, VM};

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
        Ok(Value::Label(label.to_string()))
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
