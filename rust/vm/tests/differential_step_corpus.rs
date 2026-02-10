#![cfg(not(target_arch = "wasm32"))]
//! Differential step-by-step conformance corpus.
//!
//! These tests assert transition-level behavior (step results and emitted
//! observable events), not only final traces.

#[allow(dead_code, unreachable_pub)]
mod helpers;

use telltale_vm::effect::EffectHandler;
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

#[cfg(feature = "multi-thread")]
#[test]
fn threaded_matches_cooperative_step_corpus_send_recv() {
    let image = helpers::simple_send_recv_image("A", "B", "msg");
    let handler = PassthroughHandler;
    let coop = run_cooperative_snaps(&image, &handler, 16);
    let threaded = run_threaded_snaps(&image, &handler, 16);

    let coop_events: Vec<&'static str> = coop
        .iter()
        .flat_map(|snap| snap.new_events.iter().copied())
        .collect();
    let threaded_events: Vec<&'static str> = threaded
        .iter()
        .flat_map(|snap| snap.new_events.iter().copied())
        .collect();

    assert_eq!(
        coop_events, threaded_events,
        "threaded backend diverged in event sequence"
    );
    assert_eq!(coop.first(), threaded.first(), "first-step transition mismatch");
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
