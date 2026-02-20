#![cfg(feature = "runner")]
#![allow(clippy::expect_used)]

use std::collections::{BTreeMap, BTreeSet};
use std::sync::atomic::{AtomicUsize, Ordering};

use serde::Serialize;
use serde_json::json;
use telltale_types::{GlobalType, Label, LocalTypeR};
use telltale_vm::coroutine::Value;
use telltale_vm::effect::{EffectHandler, RecordingEffectHandler, SendDecision, SendDecisionInput};
use telltale_vm::loader::CodeImage;
use telltale_vm::threaded::ThreadedVM;
use telltale_vm::vm::{ObsEvent, VMConfig, VM};

type NormalizedEvent = (String, String, String, String);
type PerSessionTrace = BTreeMap<usize, Vec<NormalizedEvent>>;
type LaneSelectionView = (u64, u64, usize, usize);

#[derive(Debug, Clone, Copy)]
struct DeterministicHandler;

impl EffectHandler for DeterministicHandler {
    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        label: &str,
        _state: &[Value],
    ) -> Result<Value, String> {
        Ok(Value::Str(label.to_string()))
    }

    fn send_decision(&self, input: SendDecisionInput<'_>) -> Result<SendDecision, String> {
        Ok(SendDecision::Deliver(input.payload.unwrap_or(Value::Unit)))
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
        Ok(Value::Nat(1))
    }

    fn send_decision(&self, input: SendDecisionInput<'_>) -> Result<SendDecision, String> {
        let idx = self.counter.fetch_add(1, Ordering::Relaxed);
        if idx % 2 == 0 {
            Ok(SendDecision::Deliver(
                input.payload.unwrap_or(Value::Nat(1)),
            ))
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

fn normalize_event(ev: &ObsEvent) -> Option<(usize, NormalizedEvent)> {
    match ev {
        ObsEvent::Sent {
            session,
            from,
            to,
            label,
            ..
        } => Some((
            *session,
            ("sent".to_string(), from.clone(), to.clone(), label.clone()),
        )),
        ObsEvent::Received {
            session,
            from,
            to,
            label,
            ..
        } => Some((
            *session,
            (
                "received".to_string(),
                from.clone(),
                to.clone(),
                label.clone(),
            ),
        )),
        _ => None,
    }
}

fn per_session(trace: &[ObsEvent]) -> PerSessionTrace {
    let mut map = BTreeMap::new();
    for ev in trace {
        if let Some((sid, norm)) = normalize_event(ev) {
            map.entry(sid).or_insert_with(Vec::new).push(norm);
        }
    }
    map
}

fn scheduler_signature(trace: &[ObsEvent]) -> Vec<(usize, String)> {
    trace
        .iter()
        .filter_map(|ev| normalize_event(ev).map(|(sid, (kind, _, _, _))| (sid, kind)))
        .collect()
}

fn effect_signature(effect_trace: &[telltale_vm::effect::EffectTraceEntry]) -> Vec<String> {
    effect_trace
        .iter()
        .map(|entry| entry.effect_kind.clone())
        .collect()
}

fn lane_selection_view(trace: &[telltale_vm::LaneSelection]) -> Vec<LaneSelectionView> {
    trace
        .iter()
        .map(|entry| (entry.tick, entry.wave, entry.session, entry.lane))
        .collect()
}

fn normalize_lane_selection(trace: &[LaneSelectionView]) -> Vec<usize> {
    let mut out: Vec<usize> = trace
        .iter()
        .map(|(_, _, sid, _)| *sid)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    out.sort_unstable();
    out
}

fn assert_eq_structured<T>(dimension: &str, left: &T, right: &T)
where
    T: PartialEq + Serialize,
{
    if left == right {
        return;
    }

    let payload = json!({
        "dimension": dimension,
        "left": left,
        "right": right,
    });
    let pretty = serde_json::to_string_pretty(&payload).expect("serialize diff payload");
    panic!("cross-target mismatch:\n{pretty}");
}

fn classify_mismatch(
    dimension: &str,
    left_effect_signature: &[String],
    right_effect_signature: &[String],
) -> &'static str {
    if left_effect_signature != right_effect_signature {
        "effect_policy_difference"
    } else {
        // Both effect_trace and other dimensions default to kernel logic difference
        // when effect signatures match.
        let _ = dimension; // Mark as intentionally unused after signature check
        "kernel_logic_difference"
    }
}

fn assert_eq_structured_attributed<T>(
    dimension: &str,
    left: &T,
    right: &T,
    left_effect_signature: &[String],
    right_effect_signature: &[String],
) where
    T: PartialEq + Serialize,
{
    if left == right {
        return;
    }

    let payload = json!({
        "dimension": dimension,
        "attribution": classify_mismatch(dimension, left_effect_signature, right_effect_signature),
        "left": left,
        "right": right,
        "left_effect_signature": left_effect_signature,
        "right_effect_signature": right_effect_signature,
    });
    let pretty = serde_json::to_string_pretty(&payload).expect("serialize diff payload");
    panic!("cross-target mismatch:\n{pretty}");
}

fn ping_pong_image() -> CodeImage {
    let mut local_types = BTreeMap::new();
    local_types.insert(
        "A".to_string(),
        LocalTypeR::send(
            "B",
            Label::new("ping"),
            LocalTypeR::recv("B", Label::new("pong"), LocalTypeR::End),
        ),
    );
    local_types.insert(
        "B".to_string(),
        LocalTypeR::recv(
            "A",
            Label::new("ping"),
            LocalTypeR::send("A", Label::new("pong"), LocalTypeR::End),
        ),
    );
    let global = GlobalType::send(
        "A",
        "B",
        Label::new("ping"),
        GlobalType::send("B", "A", Label::new("pong"), GlobalType::End),
    );
    CodeImage::from_local_types(&local_types, &global)
}

fn chain_image() -> CodeImage {
    let mut local_types = BTreeMap::new();
    local_types.insert(
        "A".to_string(),
        LocalTypeR::send(
            "B",
            Label::new("ab"),
            LocalTypeR::recv("C", Label::new("ca"), LocalTypeR::End),
        ),
    );
    local_types.insert(
        "B".to_string(),
        LocalTypeR::recv(
            "A",
            Label::new("ab"),
            LocalTypeR::send("C", Label::new("bc"), LocalTypeR::End),
        ),
    );
    local_types.insert(
        "C".to_string(),
        LocalTypeR::recv(
            "B",
            Label::new("bc"),
            LocalTypeR::send("A", Label::new("ca"), LocalTypeR::End),
        ),
    );
    let global = GlobalType::send(
        "A",
        "B",
        Label::new("ab"),
        GlobalType::send(
            "B",
            "C",
            Label::new("bc"),
            GlobalType::send("C", "A", Label::new("ca"), GlobalType::End),
        ),
    );
    CodeImage::from_local_types(&local_types, &global)
}

fn run_single_thread(
    image: &CodeImage,
) -> (Vec<ObsEvent>, Vec<telltale_vm::effect::EffectTraceEntry>) {
    let mut vm = VM::new(VMConfig::default());
    vm.load_choreography(image).expect("load choreography");
    vm.run(&DeterministicHandler, 256)
        .expect("single-thread run");
    (vm.trace().to_vec(), vm.effect_trace().to_vec())
}

fn run_threaded(
    image: &CodeImage,
) -> (
    Vec<ObsEvent>,
    Vec<telltale_vm::effect::EffectTraceEntry>,
    Vec<telltale_vm::LaneSelection>,
) {
    run_threaded_with_concurrency(image, 1, 4)
}

fn run_threaded_with_concurrency(
    image: &CodeImage,
    sessions: usize,
    concurrency: usize,
) -> (
    Vec<ObsEvent>,
    Vec<telltale_vm::effect::EffectTraceEntry>,
    Vec<telltale_vm::LaneSelection>,
) {
    let mut vm = ThreadedVM::with_workers(VMConfig::default(), concurrency.max(1));
    for _ in 0..sessions {
        vm.load_choreography(image).expect("load choreography");
    }
    vm.run_concurrent(&DeterministicHandler, 256, concurrency)
        .expect("threaded run");
    (
        vm.trace().to_vec(),
        vm.effect_trace().to_vec(),
        vm.lane_trace().to_vec(),
    )
}

#[test]
fn cross_target_matrix_native_single_vs_threaded_traces() {
    let images = [ping_pong_image(), chain_image()];
    for image in images {
        let (single_trace, single_effects) = run_single_thread(&image);
        let (threaded_trace, threaded_effects, _) = run_threaded(&image);
        let single_effect_sig = effect_signature(&single_effects);
        let threaded_effect_sig = effect_signature(&threaded_effects);

        let single_per_session = per_session(&single_trace);
        let threaded_per_session = per_session(&threaded_trace);
        assert_eq_structured_attributed(
            "vm_trace.per_session",
            &single_per_session,
            &threaded_per_session,
            &single_effect_sig,
            &threaded_effect_sig,
        );

        let single_sched = scheduler_signature(&single_trace);
        let threaded_sched = scheduler_signature(&threaded_trace);
        assert_eq_structured_attributed(
            "scheduler_trace.normalized",
            &single_sched,
            &threaded_sched,
            &single_effect_sig,
            &threaded_effect_sig,
        );

        assert_eq_structured_attributed(
            "effect_trace.signature",
            &single_effect_sig,
            &threaded_effect_sig,
            &single_effect_sig,
            &threaded_effect_sig,
        );
    }
}

#[test]
fn cross_target_matrix_replay_effect_trace_comparison() {
    let image = ping_pong_image();

    let flaky = FlakySendHandler::default();
    let recording = RecordingEffectHandler::new(&flaky);
    let mut single = VM::new(VMConfig::default());
    single.load_choreography(&image).expect("load choreography");
    single.run(&recording, 256).expect("single baseline run");

    let replay_trace = recording.effect_trace();
    let single_trace = single.trace().to_vec();

    let mut threaded = ThreadedVM::with_workers(VMConfig::default(), 4);
    threaded
        .load_choreography(&image)
        .expect("load choreography");
    let fallback = FlakySendHandler::default();
    threaded
        .run_replay(&fallback, &replay_trace, 256)
        .expect("threaded replay run");

    let single_per_session = per_session(&single_trace);
    let threaded_per_session = per_session(threaded.trace());
    assert_eq_structured(
        "replay.vm_trace.per_session",
        &single_per_session,
        &threaded_per_session,
    );

    let replay_effect_kinds: BTreeSet<_> = replay_trace
        .iter()
        .map(|entry| entry.effect_kind.as_str())
        .collect();
    let threaded_effect_kinds: BTreeSet<_> = threaded
        .effect_trace()
        .iter()
        .map(|entry| entry.effect_kind.as_str())
        .collect();

    assert!(
        threaded_effect_kinds.is_subset(&replay_effect_kinds)
            || replay_effect_kinds.is_subset(&threaded_effect_kinds),
        "unexpected effect-policy delta across replay targets"
    );
}

#[test]
fn cross_target_matrix_lane_selection_normalization_single_vs_multi_lane() {
    let image = ping_pong_image();

    // Single-lane baseline in threaded backend.
    let (_, _, single_lane_trace) = run_threaded_with_concurrency(&image, 3, 1);
    let single_lane = lane_selection_view(&single_lane_trace);
    assert!(
        single_lane.iter().all(|(_, _, _, lane)| *lane == 0),
        "single-lane run must only use lane slot 0"
    );

    // Multi-lane run over same workload.
    let (_, _, multi_lane_trace) = run_threaded_with_concurrency(&image, 3, 4);
    let multi_lane = lane_selection_view(&multi_lane_trace);
    assert!(
        multi_lane.iter().any(|(_, _, _, lane)| *lane > 0),
        "multi-lane run must use non-zero lane slots for concurrent picks"
    );

    let single_norm = normalize_lane_selection(&single_lane);
    let multi_norm = normalize_lane_selection(&multi_lane);
    assert_eq_structured(
        "scheduler_trace.lane_selection.normalized",
        &single_norm,
        &multi_norm,
    );
}
