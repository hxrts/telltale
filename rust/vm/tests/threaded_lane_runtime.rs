#![doc = "Threaded lane runtime tests: partitioning, handoff, and progress."]
#![cfg(not(target_arch = "wasm32"))]
#![cfg(feature = "multi-thread")]
//! Threaded lane runtime tests: partitioning, handoff, and progress.

#[allow(dead_code, unreachable_pub)]
mod helpers;

use std::collections::BTreeMap;

use helpers::simple_send_recv_image;
use telltale_types::{GlobalType, LocalTypeR};
use telltale_vm::coroutine::Value;
use telltale_vm::effect::EffectHandler;
use telltale_vm::instr::{Endpoint, ImmValue, Instr};
use telltale_vm::loader::CodeImage;
use telltale_vm::threaded::{ContentionMetrics, ThreadedVM};
use telltale_vm::vm::{StepResult, VMConfig};

#[derive(Debug, Clone, Copy)]
struct RuntimeHandler;

impl EffectHandler for RuntimeHandler {
    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &[Value],
    ) -> Result<Value, String> {
        Ok(Value::Unit)
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
            .ok_or_else(|| "no labels available".to_string())
    }

    fn step(&self, role: &str, state: &mut Vec<Value>) -> Result<(), String> {
        if role == "A" {
            state[0] = Value::Endpoint(Endpoint {
                sid: 0,
                role: "A".to_string(),
            });
        }
        Ok(())
    }
}

fn transfer_image() -> CodeImage {
    let mut local_types = BTreeMap::new();
    local_types.insert("A".to_string(), LocalTypeR::End);
    local_types.insert("B".to_string(), LocalTypeR::End);

    let mut programs = BTreeMap::new();
    programs.insert(
        "A".to_string(),
        vec![
            Instr::Invoke { action: 0, dst: 0 },
            Instr::Set {
                dst: 1,
                val: ImmValue::Nat(1),
            },
            Instr::Transfer {
                endpoint: 0,
                target: 1,
                bundle: 2,
            },
            Instr::Halt,
        ],
    );
    programs.insert("B".to_string(), vec![Instr::Halt]);

    CodeImage {
        programs,
        global_type: GlobalType::End,
        local_types,
    }
}

fn run_composed(workers: usize, protocols: usize) -> (usize, ContentionMetrics) {
    let mut vm = ThreadedVM::with_workers(VMConfig::default(), workers);
    for i in 0..protocols {
        let image = simple_send_recv_image("A", "B", &format!("m{i}"));
        vm.load_choreography(&image).expect("load choreography");
    }

    let handler = RuntimeHandler;
    let mut rounds = 0usize;
    for _ in 0..2048 {
        rounds += 1;
        match vm
            .step_round(&handler, workers.max(1))
            .expect("threaded step_round")
        {
            StepResult::AllDone => {
                return (rounds, vm.contention_metrics().clone());
            }
            StepResult::Continue => {}
            StepResult::Stuck => {
                panic!("composed workload got stuck");
            }
        }
    }
    panic!("composed workload did not finish");
}

#[test]
fn lane_assignment_and_single_lane_compatibility() {
    let mut vm = ThreadedVM::with_workers(VMConfig::default(), 4);
    for i in 0..6 {
        let image = simple_send_recv_image("A", "B", &format!("lane{i}"));
        vm.load_choreography(&image).expect("load choreography");
    }
    vm.run(&RuntimeHandler, 512).expect("threaded run");

    let lane_trace = vm.lane_trace();
    assert!(!lane_trace.is_empty(), "lane trace must be populated");
    assert!(
        lane_trace.iter().any(|entry| entry.lane > 0),
        "multi-lane run should select non-zero lanes"
    );

    let mut single_lane = ThreadedVM::with_workers(VMConfig::default(), 1);
    for i in 0..6 {
        let image = simple_send_recv_image("A", "B", &format!("lane{i}"));
        single_lane
            .load_choreography(&image)
            .expect("load choreography");
    }
    single_lane.run(&RuntimeHandler, 512).expect("threaded run");

    assert!(
        single_lane.lane_trace().iter().all(|entry| entry.lane == 0),
        "single-lane runtime must only schedule lane 0"
    );
}

#[test]
fn deterministic_transfer_handoff_uses_delegation_path() {
    let mut vm = ThreadedVM::with_workers(VMConfig::default(), 4);
    vm.load_choreography(&transfer_image())
        .expect("load choreography");

    // Stop as soon as the transfer handoff has been committed; the fixture
    // does not model a post-transfer continuation for the source coroutine.
    for _ in 0..16 {
        vm.step_round(&RuntimeHandler, 2).expect("threaded step");
        if !vm.handoff_trace().is_empty() {
            break;
        }
    }

    let handoffs = vm.handoff_trace();
    assert_eq!(handoffs.len(), 1, "expected one transfer handoff");
    let handoff = &handoffs[0];
    assert_eq!(handoff.from_coro, 0);
    assert_eq!(handoff.to_coro, 1);
    assert_ne!(
        handoff.from_lane, handoff.to_lane,
        "transfer should cross lanes in this test fixture"
    );

    let metrics = vm.contention_metrics();
    assert_eq!(metrics.cross_lane_transfer_count, 1);
    assert_eq!(metrics.handoff_applied_count, 1);
}

#[test]
fn no_deadlock_livelock_and_scaling_proxy_hold() {
    let (single_rounds, single_metrics) = run_composed(1, 48);
    let (multi_rounds, multi_metrics) = run_composed(8, 48);

    assert!(
        multi_rounds <= single_rounds,
        "multi-lane runtime should not require more rounds than single-lane"
    );
    assert!(
        multi_metrics.max_wave_width > single_metrics.max_wave_width,
        "multi-lane runtime should increase parallel wave width"
    );
}

#[test]
fn disjoint_footprints_parallelize_in_same_wave() {
    let mut vm = ThreadedVM::with_workers(VMConfig::default(), 2);
    let sid_a = vm
        .load_choreography(&simple_send_recv_image("A", "B", "m1"))
        .expect("load choreography A");
    let sid_b = vm
        .load_choreography(&simple_send_recv_image("A", "B", "m2"))
        .expect("load choreography B");

    vm.step_round(&RuntimeHandler, 2)
        .expect("threaded step round");
    let tick = vm.clock().tick;
    let wave0: Vec<_> = vm
        .lane_trace()
        .iter()
        .filter(|entry| entry.tick == tick && entry.wave == 0)
        .collect();
    assert!(
        wave0.len() >= 2,
        "expected disjoint sessions to parallelize in wave 0"
    );
    assert!(
        wave0.iter().any(|entry| entry.session == sid_a)
            && wave0.iter().any(|entry| entry.session == sid_b),
        "wave 0 should include both disjoint sessions"
    );
}

#[test]
fn overlapping_footprints_serialize_per_wave() {
    let mut vm = ThreadedVM::with_workers(VMConfig::default(), 2);
    let sid = vm
        .load_choreography(&simple_send_recv_image("A", "B", "m"))
        .expect("load choreography");

    vm.step_round(&RuntimeHandler, 2)
        .expect("threaded step round");
    let tick = vm.clock().tick;
    let mut by_wave: BTreeMap<u64, usize> = BTreeMap::new();
    for entry in vm
        .lane_trace()
        .iter()
        .filter(|entry| entry.tick == tick && entry.session == sid)
    {
        *by_wave.entry(entry.wave).or_insert(0) += 1;
    }
    assert!(!by_wave.is_empty(), "expected at least one scheduled wave");
    assert!(
        by_wave.values().all(|count| *count <= 1),
        "a single session must not schedule multiple coroutines in the same wave"
    );
}

#[test]
fn lane_selection_tie_break_is_repeatable_for_fixed_input() {
    let run_once = || {
        let mut vm = ThreadedVM::with_workers(VMConfig::default(), 4);
        for i in 0..8 {
            let image = simple_send_recv_image("A", "B", &format!("det{i}"));
            vm.load_choreography(&image).expect("load choreography");
        }
        vm.run(&RuntimeHandler, 512).expect("threaded run");
        vm.lane_trace().to_vec()
    };

    let first = run_once();
    let second = run_once();
    assert_eq!(
        first, second,
        "lane trace must be deterministic for fixed input/policy"
    );
}

#[test]
fn lane_scheduler_state_roundtrip_is_stable() {
    let mut vm = ThreadedVM::with_workers(VMConfig::default(), 4);
    for i in 0..4 {
        let image = simple_send_recv_image("A", "B", &format!("state{i}"));
        vm.load_choreography(&image).expect("load choreography");
    }
    vm.step_round(&RuntimeHandler, 4)
        .expect("threaded step round");

    let state = vm.lane_scheduler_state();
    let encoded = serde_json::to_vec(&state).expect("serialize lane scheduler state");
    let decoded: telltale_vm::LaneSchedulerState =
        serde_json::from_slice(&encoded).expect("deserialize lane scheduler state");
    assert_eq!(
        decoded, state,
        "lane scheduler state roundtrip must be stable"
    );
}
