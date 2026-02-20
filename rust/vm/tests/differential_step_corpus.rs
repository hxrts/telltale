#![cfg(not(target_arch = "wasm32"))]
//! Differential step-by-step conformance corpus.
//!
//! These tests assert transition-level behavior (step results and emitted
//! observable events), not only final traces.

#[allow(dead_code, unreachable_pub)]
mod helpers;

use std::collections::BTreeMap;

use telltale_types::{GlobalType, LocalTypeR};
use telltale_vm::coroutine::Value;
use telltale_vm::effect::{EffectHandler, SendDecision, SendDecisionInput};
use telltale_vm::instr::{Endpoint, ImmValue, Instr, InvokeAction};
use telltale_vm::loader::CodeImage;
#[cfg(feature = "multi-thread")]
use telltale_vm::threaded::ThreadedVM;
use telltale_vm::vm::{ObsEvent, StepResult, VMConfig, VM};

use helpers::PassthroughHandler;

#[derive(Debug, Clone, PartialEq, Eq)]
struct StepSnap {
    result: &'static str,
    new_events: Vec<&'static str>,
}

fn result_name(result: &StepResult) -> &'static str {
    match result {
        StepResult::Continue => "continue",
        StepResult::Stuck => "stuck",
        StepResult::AllDone => "all_done",
    }
}

fn event_name(ev: &ObsEvent) -> &'static str {
    match ev {
        ObsEvent::Sent { .. } => "sent",
        ObsEvent::Received { .. } => "received",
        ObsEvent::Offered { .. } => "offered",
        ObsEvent::Chose { .. } => "chose",
        ObsEvent::Opened { .. } => "opened",
        ObsEvent::Closed { .. } => "closed",
        ObsEvent::EpochAdvanced { .. } => "epoch_advanced",
        ObsEvent::Halted { .. } => "halted",
        ObsEvent::Invoked { .. } => "invoked",
        ObsEvent::Acquired { .. } => "acquired",
        ObsEvent::Released { .. } => "released",
        ObsEvent::Transferred { .. } => "transferred",
        ObsEvent::Forked { .. } => "forked",
        ObsEvent::Joined { .. } => "joined",
        ObsEvent::Aborted { .. } => "aborted",
        ObsEvent::Tagged { .. } => "tagged",
        ObsEvent::Checked { .. } => "checked",
        ObsEvent::Faulted { .. } => "faulted",
        ObsEvent::OutputConditionChecked { .. } => "output_condition_checked",
    }
}

fn run_cooperative_snaps(
    image: &CodeImage,
    handler: &dyn EffectHandler,
    max_steps: usize,
) -> Vec<StepSnap> {
    let mut vm = VM::new(VMConfig::default());
    vm.load_choreography(image).expect("load choreography");
    let mut snaps = Vec::new();
    let mut prev_len = vm.trace().len();
    for _ in 0..max_steps {
        let result = vm.step(handler).expect("step");
        let trace = vm.trace();
        let mut new_events = Vec::new();
        for ev in &trace[prev_len..] {
            if matches!(ev, ObsEvent::OutputConditionChecked { .. }) {
                continue;
            }
            new_events.push(event_name(ev));
        }
        prev_len = trace.len();
        snaps.push(StepSnap {
            result: result_name(&result),
            new_events,
        });
        if matches!(result, StepResult::AllDone | StepResult::Stuck) {
            break;
        }
    }
    snaps
}

fn flatten_events(snaps: &[StepSnap]) -> Vec<&'static str> {
    snaps
        .iter()
        .flat_map(|snap| snap.new_events.iter().copied())
        .collect()
}

fn run_cooperative_snaps_with_config(
    image: &CodeImage,
    handler: &dyn EffectHandler,
    max_steps: usize,
    config: VMConfig,
) -> Vec<StepSnap> {
    let mut vm = VM::new(config);
    vm.load_choreography(image).expect("load choreography");
    let mut snaps = Vec::new();
    let mut prev_len = vm.trace().len();
    for _ in 0..max_steps {
        let result = vm.step(handler).expect("step");
        let trace = vm.trace();
        let mut new_events = Vec::new();
        for ev in &trace[prev_len..] {
            if matches!(ev, ObsEvent::OutputConditionChecked { .. }) {
                continue;
            }
            new_events.push(event_name(ev));
        }
        prev_len = trace.len();
        snaps.push(StepSnap {
            result: result_name(&result),
            new_events,
        });
        if matches!(result, StepResult::AllDone | StepResult::Stuck) {
            break;
        }
    }
    snaps
}

fn single_role_end_image(program: Vec<Instr>) -> CodeImage {
    CodeImage {
        programs: {
            let mut m = BTreeMap::new();
            m.insert("A".to_string(), program);
            m
        },
        global_type: GlobalType::End,
        local_types: {
            let mut m = BTreeMap::new();
            m.insert("A".to_string(), LocalTypeR::End);
            m
        },
    }
}

fn transfer_fixture_image() -> CodeImage {
    let mut local_types = BTreeMap::new();
    local_types.insert("A".to_string(), LocalTypeR::End);
    local_types.insert("B".to_string(), LocalTypeR::End);
    let mut programs = BTreeMap::new();
    programs.insert(
        "A".to_string(),
        vec![
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

fn tag_check_fixture_image() -> CodeImage {
    let mut image = helpers::simple_send_recv_image("A", "B", "msg");
    image.programs.insert(
        "A".to_string(),
        vec![Instr::Send { chan: 0, val: 1 }, Instr::Halt],
    );
    image.programs.insert(
        "B".to_string(),
        vec![
            Instr::Receive { chan: 0, dst: 1 },
            Instr::Tag { fact: 1, dst: 2 },
            Instr::Set {
                dst: 3,
                val: ImmValue::Str("Observer".to_string()),
            },
            Instr::Check {
                knowledge: 1,
                target: 3,
                dst: 4,
            },
            Instr::Halt,
        ],
    );
    image
}

fn guard_effect_fixture_image() -> CodeImage {
    single_role_end_image(vec![
        Instr::Invoke {
            action: InvokeAction::Reg(0),
            dst: Some(1),
        },
        Instr::Acquire {
            layer: "auth".to_string(),
            dst: 2,
        },
        Instr::Release {
            layer: "auth".to_string(),
            evidence: 2,
        },
        Instr::Halt,
    ])
}

fn speculation_fixture_image() -> CodeImage {
    single_role_end_image(vec![
        Instr::Set {
            dst: 1,
            val: ImmValue::Nat(9),
        },
        Instr::Fork { ghost: 1 },
        Instr::Join,
        Instr::Fork { ghost: 1 },
        Instr::Abort,
        Instr::Halt,
    ])
}

fn control_spawn_fixture_image() -> CodeImage {
    single_role_end_image(vec![
        Instr::Set {
            dst: 1,
            val: ImmValue::Nat(42),
        },
        Instr::Spawn {
            target: 6,
            args: vec![1],
        },
        Instr::Jump { target: 4 },
        Instr::Set {
            dst: 2,
            val: ImmValue::Nat(999),
        },
        Instr::Yield,
        Instr::Halt,
        Instr::Move { dst: 2, src: 0 },
        Instr::Halt,
    ])
}

#[derive(Debug, Clone, Copy)]
struct KnowledgePayloadHandler;

impl EffectHandler for KnowledgePayloadHandler {
    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &[Value],
    ) -> Result<Value, String> {
        Ok(Value::Unit)
    }

    fn send_decision(&self, input: SendDecisionInput<'_>) -> Result<SendDecision, String> {
        Ok(SendDecision::Deliver(Value::Prod(
            Box::new(Value::Endpoint(Endpoint {
                sid: input.sid,
                role: input.role.to_string(),
            })),
            Box::new(Value::Str("secret".to_string())),
        )))
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

    fn step(&self, _role: &str, _state: &mut Vec<Value>) -> Result<(), String> {
        Ok(())
    }
}

#[cfg(feature = "multi-thread")]
fn run_threaded_snaps(
    image: &CodeImage,
    handler: &dyn EffectHandler,
    max_steps: usize,
) -> Vec<StepSnap> {
    let mut vm = ThreadedVM::with_workers(VMConfig::default(), 1);
    vm.load_choreography(image).expect("load choreography");
    let mut snaps = Vec::new();
    let mut prev_len = vm.trace().len();
    for _ in 0..max_steps {
        let result = vm.step_round(handler, 1).expect("step round");
        let trace = vm.trace();
        let mut new_events = Vec::new();
        for ev in &trace[prev_len..] {
            if matches!(ev, ObsEvent::OutputConditionChecked { .. }) {
                continue;
            }
            new_events.push(event_name(ev));
        }
        prev_len = trace.len();
        snaps.push(StepSnap {
            result: result_name(&result),
            new_events,
        });
        if matches!(result, StepResult::AllDone | StepResult::Stuck) {
            break;
        }
    }
    snaps
}

#[test]
fn cooperative_step_corpus_send_recv_shape() {
    let image = helpers::simple_send_recv_image("A", "B", "msg");
    let handler = PassthroughHandler;
    let snaps = run_cooperative_snaps(&image, &handler, 16);
    assert!(snaps.len() >= 3, "expected multiple steps, got {snaps:?}");
    assert_eq!(
        snaps.first(),
        Some(&StepSnap {
            result: "continue",
            new_events: vec!["sent"],
        })
    );
    assert_eq!(
        snaps.get(1),
        Some(&StepSnap {
            result: "continue",
            new_events: vec!["received"],
        })
    );
    assert_eq!(
        snaps.last().map(|s| s.result),
        Some("all_done"),
        "expected all_done terminal step, got {snaps:?}"
    );
}

#[test]
fn cooperative_step_corpus_offer_choose_shape() {
    let image = helpers::choice_image("A", "B", &["yes", "no"]);
    let handler = PassthroughHandler;
    let snaps = run_cooperative_snaps(&image, &handler, 16);
    let events = flatten_events(&snaps);
    assert!(
        events.contains(&"offered"),
        "expected offered event in trace, got {events:?}"
    );
    assert!(
        events.contains(&"chose"),
        "expected chose event in trace, got {events:?}"
    );
    assert_eq!(
        snaps.last().map(|s| s.result),
        Some("all_done"),
        "expected all_done terminal step, got {snaps:?}"
    );
}

#[test]
fn cooperative_step_corpus_transfer_shape() {
    let image = transfer_fixture_image();
    let handler = PassthroughHandler;
    let snaps = run_cooperative_snaps(&image, &handler, 16);
    let events = flatten_events(&snaps);
    assert!(
        events.contains(&"transferred"),
        "expected transferred event in trace, got {events:?}"
    );
    assert_eq!(
        snaps.last().map(|s| s.result),
        Some("all_done"),
        "expected all_done terminal step, got {snaps:?}"
    );
}

#[test]
fn cooperative_step_corpus_tag_check_shape() {
    let image = tag_check_fixture_image();
    let snaps = run_cooperative_snaps(&image, &KnowledgePayloadHandler, 32);
    let events = flatten_events(&snaps);
    assert!(
        events.contains(&"tagged"),
        "expected tagged event in trace, got {events:?}"
    );
    assert!(
        events.contains(&"checked"),
        "expected checked event in trace, got {events:?}"
    );
    assert_eq!(
        snaps.last().map(|s| s.result),
        Some("all_done"),
        "expected all_done terminal step, got {snaps:?}"
    );
}

#[test]
fn cooperative_step_corpus_guard_effect_shape() {
    let image = guard_effect_fixture_image();
    let snaps = run_cooperative_snaps(&image, &PassthroughHandler, 16);
    let events = flatten_events(&snaps);
    assert!(
        events.contains(&"invoked"),
        "expected invoked event in trace, got {events:?}"
    );
    assert!(
        events.contains(&"acquired"),
        "expected acquired event in trace, got {events:?}"
    );
    assert!(
        events.contains(&"released"),
        "expected released event in trace, got {events:?}"
    );
    assert_eq!(
        snaps.last().map(|s| s.result),
        Some("all_done"),
        "expected all_done terminal step, got {snaps:?}"
    );
}

#[test]
fn cooperative_step_corpus_control_spawn_shape() {
    let image = control_spawn_fixture_image();
    let snaps = run_cooperative_snaps(&image, &PassthroughHandler, 32);
    assert_eq!(
        snaps.last().map(|s| s.result),
        Some("all_done"),
        "expected all_done terminal step, got {snaps:?}"
    );
}

#[test]
fn cooperative_step_corpus_speculation_shape() {
    let image = speculation_fixture_image();
    let cfg = VMConfig {
        speculation_enabled: true,
        ..VMConfig::default()
    };
    let snaps = run_cooperative_snaps_with_config(&image, &PassthroughHandler, 16, cfg);
    let events = flatten_events(&snaps);
    assert!(
        events.contains(&"forked"),
        "expected forked event in trace, got {events:?}"
    );
    assert!(
        events.contains(&"joined"),
        "expected joined event in trace, got {events:?}"
    );
    assert!(
        events.contains(&"aborted"),
        "expected aborted event in trace, got {events:?}"
    );
    assert_eq!(
        snaps.last().map(|s| s.result),
        Some("all_done"),
        "expected all_done terminal step, got {snaps:?}"
    );
}

#[cfg(feature = "multi-thread")]
#[test]
fn threaded_matches_cooperative_step_corpus_send_recv() {
    let image = helpers::simple_send_recv_image("A", "B", "msg");
    let handler = PassthroughHandler;
    let coop = run_cooperative_snaps(&image, &handler, 16);
    let threaded = run_threaded_snaps(&image, &handler, 16);

    let coop_events = flatten_events(&coop);
    let threaded_events = flatten_events(&threaded);

    assert_eq!(
        coop_events, threaded_events,
        "threaded backend diverged in event sequence"
    );
    assert_eq!(
        coop.first(),
        threaded.first(),
        "first-step transition mismatch"
    );
    assert_eq!(
        coop.last().map(|s| s.result),
        Some("all_done"),
        "coop did not terminate"
    );
    assert_eq!(
        threaded.last().map(|s| s.result),
        Some("all_done"),
        "threaded did not terminate"
    );
}

#[cfg(feature = "multi-thread")]
#[test]
fn threaded_matches_cooperative_step_corpus_choice() {
    let image = helpers::choice_image("A", "B", &["yes", "no"]);
    let handler = PassthroughHandler;
    let coop = run_cooperative_snaps(&image, &handler, 16);
    let threaded = run_threaded_snaps(&image, &handler, 16);

    let coop_events = flatten_events(&coop);
    let threaded_events = flatten_events(&threaded);

    assert_eq!(
        coop_events, threaded_events,
        "threaded backend diverged on choice event sequence"
    );
    assert!(
        coop_events.contains(&"offered"),
        "cooperative trace missing offered"
    );
    assert!(
        coop_events.contains(&"chose"),
        "cooperative trace missing chose"
    );
    assert_eq!(
        coop.last().map(|s| s.result),
        Some("all_done"),
        "coop did not terminate"
    );
    assert_eq!(
        threaded.last().map(|s| s.result),
        Some("all_done"),
        "threaded did not terminate"
    );
}
