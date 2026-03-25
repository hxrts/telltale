#![cfg(not(target_arch = "wasm32"))]
//! Threaded vs cooperative ProtocolMachine equivalence tests.

#![cfg(feature = "multi-thread")]

#[allow(dead_code, unreachable_pub)]
#[path = "support/mod.rs"]
mod test_support;

use std::collections::BTreeMap;
use std::sync::atomic::{AtomicUsize, Ordering};

use telltale_machine::coroutine::Fault;
use telltale_machine::coroutine::Value;
use telltale_machine::determinism::{replay_consistent, DeterminismMode};
use telltale_machine::model::effects::{
    EffectFailure, EffectHandler, EffectResult, RecordingEffectHandler, SendDecision,
    SendDecisionInput,
};
use telltale_machine::OutputConditionPolicy;
use telltale_machine::ProgressState;
use telltale_machine::ThreadedProtocolMachine;
use telltale_machine::{ObsEvent, ProtocolMachine, ProtocolMachineConfig, ProtocolMachineError};
use test_support::{
    choice_image, recursive_send_recv_image, simple_send_recv_image, PassthroughHandler,
};

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
    images: &[telltale_machine::runtime::loader::CodeImage],
    concurrency: usize,
) -> BTreeMap<usize, Vec<Normalized>> {
    let handler = PassthroughHandler;
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    for image in images {
        machine.load_choreography(image).expect("load image");
    }
    machine.run_concurrent(&handler, 200, concurrency)
        .expect("cooperative run");
    per_session(machine.trace())
}

fn run_threaded(
    images: &[telltale_machine::runtime::loader::CodeImage],
    workers: usize,
) -> BTreeMap<usize, Vec<Normalized>> {
    let handler = PassthroughHandler;
    let mut machine = ThreadedProtocolMachine::with_workers(ProtocolMachineConfig::default(), workers);
    for image in images {
        machine.load_choreography(image).expect("load image");
    }
    machine.run_concurrent(&handler, 200, 1)
        .expect("threaded run at canonical concurrency=1");
    per_session(machine.trace())
}

#[allow(clippy::type_complexity)]
fn run_progress_states(
    image: &telltale_machine::runtime::loader::CodeImage,
) -> (
    Vec<(String, ProgressState, Option<String>)>,
    Vec<(String, ProgressState, Option<String>)>,
) {
    let handler = PassthroughHandler;

    let mut coop = ProtocolMachine::new(ProtocolMachineConfig::default());
    coop.load_choreography(image).expect("load image");
    coop.run(&handler, 64).expect("cooperative run");
    let coop_progress = coop
        .semantic_objects()
        .progress_contracts
        .into_iter()
        .map(|contract| (contract.operation_id, contract.state, contract.reason))
        .collect();

    let mut threaded = ThreadedProtocolMachine::with_workers(ProtocolMachineConfig::default(), 2);
    threaded.load_choreography(image).expect("load image");
    threaded.run(&handler, 64).expect("threaded run");
    let threaded_progress = threaded
        .semantic_objects()
        .progress_contracts
        .into_iter()
        .map(|contract| (contract.operation_id, contract.state, contract.reason))
        .collect();

    (coop_progress, threaded_progress)
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
    ) -> EffectResult<Value> {
        EffectResult::success(Value::Nat(1))
    }

    fn send_decision(&self, input: SendDecisionInput<'_>) -> EffectResult<SendDecision> {
        let idx = self.counter.fetch_add(1, Ordering::Relaxed);
        if idx % 2 == 0 {
            EffectResult::success(SendDecision::Deliver(
                input.payload.unwrap_or(Value::Nat(1)),
            ))
        } else {
            EffectResult::success(SendDecision::Drop)
        }
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

    fn step(&self, _role: &str, _state: &mut Vec<Value>) -> EffectResult<()> {
        EffectResult::success(())
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
fn test_progress_contract_exports_match_across_drivers() {
    let image = simple_send_recv_image("A", "B", "msg");
    let (coop_progress, threaded_progress) = run_progress_states(&image);
    assert_eq!(coop_progress, threaded_progress);
}

#[test]
fn test_output_condition_gate_applies_to_all_drivers() {
    let image = simple_send_recv_image("A", "B", "msg");
    let handler = PassthroughHandler;

    let deny_cfg = ProtocolMachineConfig {
        output_condition_policy: OutputConditionPolicy::DenyAll,
        ..ProtocolMachineConfig::default()
    };

    let mut coop = ProtocolMachine::new(deny_cfg.clone());
    coop.load_choreography(&image).expect("load image");
    assert!(coop.run(&handler, 50).is_err());

    let mut threaded = ThreadedProtocolMachine::with_workers(deny_cfg, 2);
    threaded.load_choreography(&image).expect("load image");
    assert!(threaded.run(&handler, 50).is_err());
}

#[test]
fn test_output_condition_outcomes_match_across_drivers() {
    let image = simple_send_recv_image("A", "B", "msg");
    let handler = PassthroughHandler;

    let allow_cfg = ProtocolMachineConfig {
        output_condition_policy: OutputConditionPolicy::PredicateAllowList(vec![
            "machine.observable_output".to_string(),
        ]),
        ..ProtocolMachineConfig::default()
    };

    let mut coop = ProtocolMachine::new(allow_cfg.clone());
    coop.load_choreography(&image).expect("load image");
    coop.run(&handler, 50).expect("cooperative run");
    let coop_checks: Vec<(String, bool)> = coop
        .output_condition_checks()
        .iter()
        .map(|c| (c.meta.predicate_ref.clone(), c.passed))
        .collect();

    let mut threaded = ThreadedProtocolMachine::with_workers(allow_cfg, 2);
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
fn test_output_condition_commit_fail_artifacts_match_across_drivers() {
    let image = simple_send_recv_image("A", "B", "msg");
    let handler = PassthroughHandler;

    let deny_cfg = ProtocolMachineConfig {
        output_condition_policy: OutputConditionPolicy::DenyAll,
        ..ProtocolMachineConfig::default()
    };

    let mut coop = ProtocolMachine::new(deny_cfg.clone());
    coop.load_choreography(&image).expect("load image");
    let coop_err = coop
        .run(&handler, 50)
        .expect_err("cooperative run should fault");

    let mut threaded = ThreadedProtocolMachine::with_workers(deny_cfg, 2);
    threaded.load_choreography(&image).expect("load image");
    let threaded_err = threaded
        .run(&handler, 50)
        .expect_err("threaded run should fault");

    let extract_output_condition_fault = |err: ProtocolMachineError| match err {
        ProtocolMachineError::Fault {
            fault: Fault::OutputCondition { predicate_ref },
            ..
        } => predicate_ref,
        other => panic!("expected output-condition fault, got {other:?}"),
    };

    let coop_predicate = extract_output_condition_fault(coop_err);
    let threaded_predicate = extract_output_condition_fault(threaded_err);
    assert_eq!(coop_predicate, threaded_predicate);
    assert_eq!(coop_predicate, "machine.observable_output");

    let coop_checks: Vec<(String, bool)> = coop
        .output_condition_checks()
        .iter()
        .map(|c| (c.meta.predicate_ref.clone(), c.passed))
        .collect();
    let threaded_checks: Vec<(String, bool)> = threaded
        .output_condition_checks()
        .iter()
        .map(|c| (c.meta.predicate_ref.clone(), c.passed))
        .collect();
    assert_eq!(coop_checks, threaded_checks);
    assert!(coop_checks.iter().all(|(_, passed)| !passed));

    let coop_trace_checks: Vec<(String, bool)> = coop
        .trace()
        .iter()
        .filter_map(|ev| match ev {
            ObsEvent::OutputConditionChecked {
                predicate_ref,
                passed,
                ..
            } => Some((predicate_ref.clone(), *passed)),
            _ => None,
        })
        .collect();
    let threaded_trace_checks: Vec<(String, bool)> = threaded
        .trace()
        .iter()
        .filter_map(|ev| match ev {
            ObsEvent::OutputConditionChecked {
                predicate_ref,
                passed,
                ..
            } => Some((predicate_ref.clone(), *passed)),
            _ => None,
        })
        .collect();
    assert_eq!(coop_trace_checks, threaded_trace_checks);
    assert!(coop_trace_checks.iter().all(|(_, passed)| !passed));
}

#[test]
fn test_output_condition_commit_pass_artifacts_match_across_drivers() {
    let image = simple_send_recv_image("A", "B", "msg");
    let handler = PassthroughHandler;

    let allow_cfg = ProtocolMachineConfig {
        output_condition_policy: OutputConditionPolicy::PredicateAllowList(vec![
            "machine.observable_output".to_string(),
        ]),
        ..ProtocolMachineConfig::default()
    };

    let mut coop = ProtocolMachine::new(allow_cfg.clone());
    coop.load_choreography(&image).expect("load image");
    coop.run(&handler, 50).expect("cooperative run");

    let mut threaded = ThreadedProtocolMachine::with_workers(allow_cfg, 2);
    threaded.load_choreography(&image).expect("load image");
    threaded.run(&handler, 50).expect("threaded run");

    let coop_trace_checks: Vec<(String, bool)> = coop
        .trace()
        .iter()
        .filter_map(|ev| match ev {
            ObsEvent::OutputConditionChecked {
                predicate_ref,
                passed,
                ..
            } => Some((predicate_ref.clone(), *passed)),
            _ => None,
        })
        .collect();
    let threaded_trace_checks: Vec<(String, bool)> = threaded
        .trace()
        .iter()
        .filter_map(|ev| match ev {
            ObsEvent::OutputConditionChecked {
                predicate_ref,
                passed,
                ..
            } => Some((predicate_ref.clone(), *passed)),
            _ => None,
        })
        .collect();

    assert_eq!(coop_trace_checks, threaded_trace_checks);
    assert!(coop_trace_checks.iter().all(|(_, passed)| *passed));
}

#[test]
fn test_effect_trace_records_for_coop_and_threaded() {
    let image = simple_send_recv_image("A", "B", "msg");
    let handler = PassthroughHandler;

    let mut coop = ProtocolMachine::new(ProtocolMachineConfig::default());
    coop.load_choreography(&image).expect("load image");
    coop.run(&handler, 50).expect("cooperative run");
    assert!(!coop.effect_trace().is_empty());

    let mut threaded = ThreadedProtocolMachine::with_workers(ProtocolMachineConfig::default(), 2);
    threaded.load_choreography(&image).expect("load image");
    threaded.run(&handler, 50).expect("threaded run");
    assert!(!threaded.effect_trace().is_empty());
}

#[test]
fn test_replay_mode_reproduces_cooperative_trace() {
    let image = simple_send_recv_image("A", "B", "msg");

    let base = FlakySendHandler::default();
    let recording = RecordingEffectHandler::new(&base);

    let mut baseline = ProtocolMachine::new(ProtocolMachineConfig::default());
    baseline.load_choreography(&image).expect("load image");
    baseline.run(&recording, 50).expect("baseline run");

    let recorded_effects = recording.effect_trace();
    let baseline_trace = baseline.trace().to_vec();

    let mut replay_vm = ProtocolMachine::new(ProtocolMachineConfig::default());
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

    let mut baseline = ProtocolMachine::new(ProtocolMachineConfig::default());
    baseline.load_choreography(&image).expect("load image");
    baseline.run(&recording, 50).expect("baseline run");
    let recorded_effects = recording.effect_trace();

    let mut replay_threaded =
        ThreadedProtocolMachine::with_workers(ProtocolMachineConfig::default(), 2);
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
