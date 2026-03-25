#![doc = "Threaded lane runtime tests: partitioning, handoff, and progress."]
#![cfg(not(target_arch = "wasm32"))]
#![cfg(feature = "multi-thread")]
//! Threaded lane runtime tests: partitioning, handoff, and progress.

#[allow(dead_code, unreachable_pub)]
#[path = "support/mod.rs"]
mod test_support;

use std::collections::BTreeMap;

use telltale_machine::coroutine::Value;
use telltale_machine::instr::{Endpoint, ImmValue, Instr, InvokeAction};
use telltale_machine::model::effects::{EffectFailure, EffectHandler, EffectResult};
use telltale_machine::runtime::loader::CodeImage;
use telltale_machine::{ContentionMetrics, ThreadedProtocolMachine};
use telltale_machine::{ProtocolMachineConfig, StepResult, ThreadedRoundSemantics};
use telltale_types::{GlobalType, LocalTypeR};
use test_support::ScenarioSpec;

#[derive(Debug, Clone, Copy)]
struct RuntimeHandler;

impl EffectHandler for RuntimeHandler {
    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &[Value],
    ) -> EffectResult<Value> {
        EffectResult::success(Value::Unit)
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

    fn step(&self, role: &str, state: &mut Vec<Value>) -> EffectResult<()> {
        if role == "A" {
            state[0] = Value::Endpoint(Endpoint {
                sid: 0,
                role: "A".to_string(),
            });
        }
        EffectResult::success(())
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
            Instr::Invoke {
                action: InvokeAction::Reg(0),
            },
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

fn threaded_wave_config() -> ProtocolMachineConfig {
    ProtocolMachineConfig {
        threaded_round_semantics: ThreadedRoundSemantics::WaveParallelExtension,
        ..ProtocolMachineConfig::default()
    }
}

fn run_composed(workers: usize, protocols: usize) -> (usize, ContentionMetrics) {
    let mut machine = ThreadedProtocolMachine::with_workers(threaded_wave_config(), workers);
    for i in 0..protocols {
        let image = ScenarioSpec::simple("A", "B", &format!("m{i}")).to_code_image();
        machine
            .load_choreography(&image)
            .expect("load choreography");
    }

    let handler = RuntimeHandler;
    let mut rounds = 0usize;
    for _ in 0..2048 {
        rounds += 1;
        match machine
            .step_round(&handler, workers.max(1))
            .expect("threaded step_round")
        {
            StepResult::AllDone => {
                return (rounds, machine.contention_metrics().clone());
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
    let mut machine = ThreadedProtocolMachine::with_workers(threaded_wave_config(), 4);
    for i in 0..6 {
        let image = ScenarioSpec::simple("A", "B", &format!("lane{i}")).to_code_image();
        machine
            .load_choreography(&image)
            .expect("load choreography");
    }
    machine.run(&RuntimeHandler, 512).expect("threaded run");

    let lane_trace = machine.lane_trace();
    assert!(!lane_trace.is_empty(), "lane trace must be populated");
    assert!(
        lane_trace.iter().any(|entry| entry.lane > 0),
        "multi-lane run should select non-zero lanes"
    );

    let mut single_lane = ThreadedProtocolMachine::with_workers(threaded_wave_config(), 1);
    for i in 0..6 {
        let image = ScenarioSpec::simple("A", "B", &format!("lane{i}")).to_code_image();
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
    let mut machine = ThreadedProtocolMachine::with_workers(threaded_wave_config(), 4);
    machine
        .load_choreography(&transfer_image())
        .expect("load choreography");

    // Stop as soon as the transfer handoff has been committed; the fixture
    // does not model a post-transfer continuation for the source coroutine.
    for _ in 0..16 {
        machine
            .step_round(&RuntimeHandler, 2)
            .expect("threaded step");
        if !machine.handoff_trace().is_empty() {
            break;
        }
    }

    let handoffs = machine.handoff_trace();
    assert_eq!(handoffs.len(), 1, "expected one transfer handoff");
    let handoff = &handoffs[0];
    assert_eq!(handoff.from_coro, 0);
    assert_eq!(handoff.to_coro, 1);
    assert_ne!(
        handoff.from_lane, handoff.to_lane,
        "transfer should cross lanes in this test fixture"
    );

    let metrics = machine.contention_metrics();
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
    let mut machine = ThreadedProtocolMachine::with_workers(threaded_wave_config(), 2);
    let sid_a = machine
        .load_choreography(&ScenarioSpec::simple("A", "B", "m1").to_code_image())
        .expect("load choreography A");
    let sid_b = machine
        .load_choreography(&ScenarioSpec::simple("A", "B", "m2").to_code_image())
        .expect("load choreography B");

    machine
        .step_round(&RuntimeHandler, 2)
        .expect("threaded step round");
    let tick = machine.clock().tick;
    let wave0: Vec<_> = machine
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
    let mut machine = ThreadedProtocolMachine::with_workers(threaded_wave_config(), 2);
    let sid = machine
        .load_choreography(&ScenarioSpec::simple("A", "B", "m").to_code_image())
        .expect("load choreography");

    machine
        .step_round(&RuntimeHandler, 2)
        .expect("threaded step round");
    let tick = machine.clock().tick;
    let mut by_wave: BTreeMap<u64, usize> = BTreeMap::new();
    for entry in machine
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
        let mut machine = ThreadedProtocolMachine::with_workers(threaded_wave_config(), 4);
        for i in 0..8 {
            let image = ScenarioSpec::simple("A", "B", &format!("det{i}")).to_code_image();
            machine
                .load_choreography(&image)
                .expect("load choreography");
        }
        machine.run(&RuntimeHandler, 512).expect("threaded run");
        machine.lane_trace().to_vec()
    };

    let first = run_once();
    let second = run_once();
    assert_eq!(
        first, second,
        "lane trace must be deterministic for fixed input/policy"
    );
}

#[test]
fn planner_trace_is_worker_count_invariant_for_fixed_ready_set() {
    let run_once = |workers: usize| {
        let mut machine = ThreadedProtocolMachine::with_workers(threaded_wave_config(), workers);
        for i in 0..2 {
            let image = ScenarioSpec::simple("A", "B", &format!("wc{i}")).to_code_image();
            machine
                .load_choreography(&image)
                .expect("load choreography");
        }
        machine
            .run_concurrent(&RuntimeHandler, 512, 4)
            .expect("threaded run");
        machine.lane_trace().to_vec()
    };

    let workers4 = run_once(4);
    let workers8 = run_once(8);
    assert_eq!(
        workers4, workers8,
        "planner trace should be invariant across worker counts for the same ready-set footprint"
    );
}

#[test]
fn lane_scheduler_state_roundtrip_is_stable() {
    let mut machine = ThreadedProtocolMachine::with_workers(threaded_wave_config(), 4);
    for i in 0..4 {
        let image = ScenarioSpec::simple("A", "B", &format!("state{i}")).to_code_image();
        machine
            .load_choreography(&image)
            .expect("load choreography");
    }
    machine
        .step_round(&RuntimeHandler, 4)
        .expect("threaded step round");

    let state = machine.lane_scheduler_state();
    let encoded = serde_json::to_vec(&state).expect("serialize lane scheduler state");
    let decoded: telltale_machine::LaneSchedulerState =
        serde_json::from_slice(&encoded).expect("deserialize lane scheduler state");
    assert_eq!(
        decoded, state,
        "lane scheduler state roundtrip must be stable"
    );
}

#[test]
fn invalid_wave_certificate_falls_back_to_single_step() {
    let mut machine = ThreadedProtocolMachine::with_workers(threaded_wave_config(), 2);
    machine
        .load_choreography(&ScenarioSpec::simple("A", "B", "m1").to_code_image())
        .expect("load choreography A");
    machine
        .load_choreography(&ScenarioSpec::simple("A", "B", "m2").to_code_image())
        .expect("load choreography B");

    machine.force_invalid_wave_certificate_once();
    machine
        .step_round(&RuntimeHandler, 2)
        .expect("threaded step round");

    let tick = machine.clock().tick;
    let scheduled_this_tick = machine
        .lane_trace()
        .iter()
        .filter(|entry| entry.tick == tick)
        .count();
    assert_eq!(
        scheduled_this_tick, 1,
        "invalid certificate should degrade to canonical single-step behavior"
    );
}

#[test]
fn footprint_guided_wave_widening_allows_same_session_disjoint_roles() {
    let cfg = ProtocolMachineConfig {
        footprint_guided_wave_widening: true,
        ..threaded_wave_config()
    };
    let mut machine = ThreadedProtocolMachine::with_workers(cfg, 2);
    let sid = machine
        .load_choreography(&ScenarioSpec::simple("A", "B", "m").to_code_image())
        .expect("load choreography");

    machine
        .step_round(&RuntimeHandler, 2)
        .expect("threaded step round");
    let tick = machine.clock().tick;
    let count = machine
        .lane_trace()
        .iter()
        .filter(|entry| entry.tick == tick && entry.session == sid)
        .count();
    assert!(
        count >= 2,
        "widening should allow disjoint same-session roles in one wave"
    );
}
