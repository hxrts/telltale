#![cfg(not(target_arch = "wasm32"))]
//! Threaded vs cooperative VM equivalence tests.

#![cfg(feature = "multi-thread")]

#[allow(dead_code, unreachable_pub)]
mod helpers;

use std::collections::BTreeMap;
use std::sync::atomic::{AtomicUsize, Ordering};

use helpers::{
    choice_image, recursive_send_recv_image, simple_send_recv_image, PassthroughHandler,
};
use telltale_vm::coroutine::Value;
use telltale_vm::determinism::{replay_consistent, DeterminismMode};
use telltale_vm::effect::{EffectHandler, RecordingEffectHandler, SendDecision};
use telltale_vm::threaded::ThreadedVM;
use telltale_vm::vm::{ObsEvent, VMConfig, VM};
use telltale_vm::OutputConditionPolicy;

type Normalized = (String, String, String, String);

fn normalize_event(ev: &ObsEvent) -> Option<(usize, Normalized)> {
    match ev {
        ObsEvent::Sent {
            session,
            from,
            to,
            label,
            ..
        } => Some((
            *session,
            ("sent".into(), from.clone(), to.clone(), label.clone()),
        )),
        ObsEvent::Received {
            session,
            from,
            to,
            label,
            ..
        } => Some((
            *session,
            ("recv".into(), from.clone(), to.clone(), label.clone()),
        )),
        _ => None,
    }
}

fn per_session(trace: &[ObsEvent]) -> BTreeMap<usize, Vec<Normalized>> {
    let mut map: BTreeMap<usize, Vec<Normalized>> = BTreeMap::new();
    for ev in trace {
        if let Some((sid, norm)) = normalize_event(ev) {
            map.entry(sid).or_default().push(norm);
        }
    }
    map
}

fn run_cooperative(
    images: &[telltale_vm::loader::CodeImage],
    concurrency: usize,
) -> BTreeMap<usize, Vec<Normalized>> {
    let handler = PassthroughHandler;
    let mut vm = VM::new(VMConfig::default());
    for image in images {
        vm.load_choreography(image).expect("load image");
    }
    vm.run_concurrent(&handler, 200, concurrency)
        .expect("cooperative run");
    per_session(vm.trace())
}

fn run_threaded(
    images: &[telltale_vm::loader::CodeImage],
    workers: usize,
) -> BTreeMap<usize, Vec<Normalized>> {
    let handler = PassthroughHandler;
    let mut vm = ThreadedVM::with_workers(VMConfig::default(), workers);
    for image in images {
        vm.load_choreography(image).expect("load image");
    }
    vm.run(&handler, 200).expect("threaded run");
    per_session(vm.trace())
}

#[derive(Debug, Default)]
struct FlakySendHandler {
    counter: AtomicUsize,
}

impl EffectHandler for FlakySendHandler {
    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &[Value],
    ) -> Result<Value, String> {
        Ok(Value::Int(1))
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
        let idx = self.counter.fetch_add(1, Ordering::Relaxed);
        if idx % 2 == 0 {
            Ok(SendDecision::Deliver(payload.unwrap_or(Value::Int(1))))
        } else {
            Ok(SendDecision::Drop)
        }
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

#[test]
fn test_threaded_matches_cooperative() {
    let images = vec![
        simple_send_recv_image("A", "B", "msg"),
        choice_image("A", "B", &["yes", "no"]),
        recursive_send_recv_image("A", "B", "tick"),
    ];

    let total_coros: usize = images.iter().map(|img| img.roles().len()).sum();
    let workers = total_coros.max(1);

    let coop = run_cooperative(&images, workers);
    let threaded = run_threaded(&images, workers);

    assert_eq!(coop, threaded, "per-session traces should match");
}

#[test]
fn test_output_condition_gate_applies_to_all_drivers() {
    let image = simple_send_recv_image("A", "B", "msg");
    let handler = PassthroughHandler;

    let deny_cfg = VMConfig {
        output_condition_policy: OutputConditionPolicy::DenyAll,
        ..VMConfig::default()
    };

    let mut coop = VM::new(deny_cfg.clone());
    coop.load_choreography(&image).expect("load image");
    assert!(coop.run(&handler, 50).is_err());

    let mut threaded = ThreadedVM::with_workers(deny_cfg, 2);
    threaded.load_choreography(&image).expect("load image");
    assert!(threaded.run(&handler, 50).is_err());
}

#[test]
fn test_output_condition_outcomes_match_across_drivers() {
    let image = simple_send_recv_image("A", "B", "msg");
    let handler = PassthroughHandler;

    let allow_cfg = VMConfig {
        output_condition_policy: OutputConditionPolicy::PredicateAllowList(vec![
            "vm.observable_output".to_string(),
        ]),
        ..VMConfig::default()
    };

    let mut coop = VM::new(allow_cfg.clone());
    coop.load_choreography(&image).expect("load image");
    coop.run(&handler, 50).expect("cooperative run");
    let coop_checks: Vec<(String, bool)> = coop
        .output_condition_checks()
        .iter()
        .map(|c| (c.meta.predicate_ref.clone(), c.passed))
        .collect();

    let mut threaded = ThreadedVM::with_workers(allow_cfg, 2);
    threaded.load_choreography(&image).expect("load image");
    threaded.run(&handler, 50).expect("threaded run");
    let threaded_checks: Vec<(String, bool)> = threaded
        .output_condition_checks()
        .iter()
        .map(|c| (c.meta.predicate_ref.clone(), c.passed))
        .collect();

    assert_eq!(coop_checks, threaded_checks);
}

#[test]
fn test_effect_trace_records_for_coop_and_threaded() {
    let image = simple_send_recv_image("A", "B", "msg");
    let handler = PassthroughHandler;

    let mut coop = VM::new(VMConfig::default());
    coop.load_choreography(&image).expect("load image");
    coop.run(&handler, 50).expect("cooperative run");
    assert!(!coop.effect_trace().is_empty());

    let mut threaded = ThreadedVM::with_workers(VMConfig::default(), 2);
    threaded.load_choreography(&image).expect("load image");
    threaded.run(&handler, 50).expect("threaded run");
    assert!(!threaded.effect_trace().is_empty());
}

#[test]
fn test_replay_mode_reproduces_cooperative_trace() {
    let image = simple_send_recv_image("A", "B", "msg");

    let base = FlakySendHandler::default();
    let recording = RecordingEffectHandler::new(&base);

    let mut baseline = VM::new(VMConfig::default());
    baseline.load_choreography(&image).expect("load image");
    baseline.run(&recording, 50).expect("baseline run");

    let recorded_effects = recording.effect_trace();
    let baseline_trace = baseline.trace().to_vec();

    let mut replay_vm = VM::new(VMConfig::default());
    replay_vm.load_choreography(&image).expect("load image");
    let fallback = FlakySendHandler::default();
    replay_vm
        .run_replay(&fallback, &recorded_effects, 50)
        .expect("replay run");

    assert!(replay_consistent(
        DeterminismMode::ModuloEffects,
        &baseline_trace,
        replay_vm.trace(),
        &recorded_effects,
        &[]
    ));
}

#[test]
fn test_replay_mode_cross_target_differential() {
    let image = simple_send_recv_image("A", "B", "msg");

    let base = FlakySendHandler::default();
    let recording = RecordingEffectHandler::new(&base);

    let mut baseline = VM::new(VMConfig::default());
    baseline.load_choreography(&image).expect("load image");
    baseline.run(&recording, 50).expect("baseline run");
    let recorded_effects = recording.effect_trace();

    let mut replay_threaded = ThreadedVM::with_workers(VMConfig::default(), 2);
    replay_threaded
        .load_choreography(&image)
        .expect("load image");
    let fallback = FlakySendHandler::default();
    replay_threaded
        .run_replay(&fallback, &recorded_effects, 50)
        .expect("threaded replay run");

    assert_eq!(
        per_session(baseline.trace()),
        per_session(replay_threaded.trace()),
        "cross-target replay traces diverged"
    );
}
