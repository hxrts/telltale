#![cfg(not(target_arch = "wasm32"))]
//! Topology perturbations must ingress through effect handlers.

#[allow(dead_code, unreachable_pub)]
#[path = "support/mod.rs"]
mod test_support;

use cfg_if::cfg_if;
use std::sync::atomic::{AtomicBool, Ordering};

use telltale_protocol_machine::coroutine::Value;
use telltale_protocol_machine::effect::{
    EffectFailure, EffectHandler, EffectResult, SendDecision, SendDecisionInput,
    TopologyPerturbation,
};
use telltale_protocol_machine::{ProtocolMachine, ProtocolMachineConfig};
use test_support::simple_send_recv_image;

cfg_if! {
    if #[cfg(feature = "multi-thread")] {
        use std::{collections::BTreeMap, time::Duration};

        use telltale_protocol_machine::ThreadedProtocolMachine;
        use telltale_protocol_machine::CorruptionType;
    }
}

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
            None => EffectResult::failure(EffectFailure::invalid_input("no labels")),
        }
    }

    fn step(&self, _role: &str, _state: &mut Vec<Value>) -> EffectResult<()> {
        EffectResult::success(())
    }

    fn topology_events(&self, _tick: u64) -> EffectResult<Vec<TopologyPerturbation>> {
        if self.emitted.swap(true, Ordering::Relaxed) {
            return EffectResult::success(Vec::new());
        }
        EffectResult::success(vec![
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
    let mut vm = ProtocolMachine::new(ProtocolMachineConfig::default());
    vm.load_choreography(&image).expect("load choreography");

    vm.step_round(&handler, 1).expect("step round");

    assert!(vm.crashed_sites().iter().any(|site| site == "A"));
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

cfg_if! {
    if #[cfg(feature = "multi-thread")] {
        #[derive(Debug, Clone)]
        struct ScriptedTopologyHandler {
            events_by_tick: BTreeMap<u64, Vec<TopologyPerturbation>>,
        }

        impl ScriptedTopologyHandler {
            fn new(events_by_tick: BTreeMap<u64, Vec<TopologyPerturbation>>) -> Self {
                Self { events_by_tick }
            }
        }

        impl EffectHandler for ScriptedTopologyHandler {
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
                    None => EffectResult::failure(EffectFailure::invalid_input("no labels")),
                }
            }

            fn step(&self, _role: &str, _state: &mut Vec<Value>) -> EffectResult<()> {
                EffectResult::success(())
            }

            fn topology_events(&self, tick: u64) -> EffectResult<Vec<TopologyPerturbation>> {
                EffectResult::success(self.events_by_tick.get(&tick).cloned().unwrap_or_default())
            }
        }

        #[test]
        fn threaded_vm_ingests_topology_events_before_instruction_effects() {
            let image = simple_send_recv_image("A", "B", "m");
            let handler = TopologyBurstHandler::new();
            let mut vm = ThreadedProtocolMachine::with_workers(ProtocolMachineConfig::default(), 2);
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

        fn topology_trace(
            entries: &[telltale_protocol_machine::effect::EffectTraceEntry],
        ) -> Vec<TopologyPerturbation> {
            entries
                .iter()
                .filter_map(|entry| entry.topology.clone())
                .collect()
        }

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

            let mut coop = ProtocolMachine::new(ProtocolMachineConfig::default());
            coop.load_choreography(&image)
                .expect("load cooperative image");
            coop.step_round(&handler, 1)
                .expect("cooperative step round");

            let mut threaded = ThreadedProtocolMachine::with_workers(ProtocolMachineConfig::default(), 2);
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
                .any(|ev| matches!(ev, telltale_protocol_machine::ObsEvent::Faulted { .. })));
            assert!(threaded
                .trace()
                .iter()
                .any(|ev| matches!(ev, telltale_protocol_machine::ObsEvent::Faulted { .. })));
        }

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

            let mut coop = ProtocolMachine::new(ProtocolMachineConfig::default());
            coop.load_choreography(&image)
                .expect("load cooperative image");
            coop.step_round(&handler, 1).expect("cooperative tick 1");
            coop.step_round(&handler, 1).expect("cooperative tick 2");
            coop.run(&handler, 32).expect("cooperative run after heal");

            let mut threaded = ThreadedProtocolMachine::with_workers(ProtocolMachineConfig::default(), 2);
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
                .all(|ev| !matches!(ev, telltale_protocol_machine::ObsEvent::Faulted { .. })));
            assert!(threaded
                .trace()
                .iter()
                .all(|ev| !matches!(ev, telltale_protocol_machine::ObsEvent::Faulted { .. })));
        }
    }
}
