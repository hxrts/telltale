#![cfg(feature = "runner")]
#![allow(clippy::expect_used)]

use std::collections::{BTreeMap, BTreeSet};
use std::sync::atomic::{AtomicUsize, Ordering};

use serde::Serialize;
use serde_json::json;
use telltale_machine::coroutine::Value;
use telltale_machine::model::effects::{
    EffectHandler, EffectResult, RecordingEffectHandler, SendDecision, SendDecisionInput,
};
use telltale_machine::runtime::loader::CodeImage;
use telltale_machine::ProtocolMachineSemanticObjects;
use telltale_machine::ThreadedProtocolMachine;
use telltale_machine::{ObsEvent, ProtocolMachine, ProtocolMachineConfig};
use telltale_types::{GlobalType, Label, LocalTypeR};

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
        EffectResult::success(
            labels
                .first()
                .cloned()
                .expect("labels should contain at least one branch"),
        )
    }

    fn step(&self, _role: &str, _state: &mut Vec<Value>) -> EffectResult<()> {
        EffectResult::success(())
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
        EffectResult::success(
            labels
                .first()
                .cloned()
                .expect("labels should contain at least one branch"),
        )
    }

    fn step(&self, _role: &str, _state: &mut Vec<Value>) -> EffectResult<()> {
        EffectResult::success(())
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

fn effect_signature(
    effect_trace: &[telltale_machine::model::effects::EffectTraceEntry],
) -> Vec<String> {
    effect_trace
        .iter()
        .map(|entry| entry.effect_kind.clone())
        .collect()
}

fn lane_selection_view(trace: &[telltale_machine::LaneSelection]) -> Vec<LaneSelectionView> {
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

fn normalize_semantic_objects(
    mut objects: ProtocolMachineSemanticObjects,
) -> ProtocolMachineSemanticObjects {
    let normalize_owner_id = |owner_id: &mut Option<String>| {
        if owner_id.as_deref() == Some("wasm/host") {
            *owner_id = None;
        }
    };

    for operation in &mut objects.operation_instances {
        if operation.handler_identity.is_some() {
            operation.handler_identity = Some("<normalized-handler>".to_string());
        }
        normalize_owner_id(&mut operation.owner_id);
    }
    for effect in &mut objects.outstanding_effects {
        effect.handler_identity = "<normalized-handler>".to_string();
        normalize_owner_id(&mut effect.owner_id);
    }
    for read in &mut objects.observed_reads {
        read.handler_identity = "<normalized-handler>".to_string();
    }
    for read in &mut objects.authoritative_reads {
        normalize_owner_id(&mut read.owner_id);
    }
    for handle in &mut objects.canonical_handles {
        normalize_owner_id(&mut handle.owner_id);
    }
    for publication in &mut objects.publication_events {
        normalize_owner_id(&mut publication.owner_id);
    }
    for binding in &mut objects.prestate_bindings {
        normalize_owner_id(&mut binding.participant_digest);
    }
    for contract in &mut objects.agreement_contracts {
        normalize_owner_id(&mut contract.owner_id);
    }
    for evidence in &mut objects.agreement_evidence {
        normalize_owner_id(&mut evidence.owner_id);
    }
    for state in &mut objects.agreement_states {
        normalize_owner_id(&mut state.owner_id);
    }
    for region in &mut objects.regions {
        normalize_owner_id(&mut region.owner_id);
    }

    objects
        .operation_instances
        .sort_by_key(|value| serde_json::to_string(value).expect("serialize operation"));
    objects.operation_instances.dedup();

    objects
        .outstanding_effects
        .sort_by_key(|value| serde_json::to_string(value).expect("serialize effect"));
    objects.outstanding_effects.dedup_by(|lhs, rhs| lhs == rhs);

    objects
        .semantic_handoffs
        .sort_by_key(|value| serde_json::to_string(value).expect("serialize handoff"));
    objects.semantic_handoffs.dedup();
    objects
        .transformation_obligations
        .sort_by_key(|value| serde_json::to_string(value).expect("serialize obligation"));
    objects.transformation_obligations.dedup();
    objects
        .authoritative_reads
        .sort_by_key(|value| serde_json::to_string(value).expect("serialize authoritative read"));
    objects.authoritative_reads.dedup();
    objects
        .observed_reads
        .sort_by_key(|value| serde_json::to_string(value).expect("serialize observed read"));
    objects.observed_reads.dedup();
    objects
        .materialization_proofs
        .sort_by_key(|value| serde_json::to_string(value).expect("serialize proof"));
    objects.materialization_proofs.dedup();
    objects
        .canonical_handles
        .sort_by_key(|value| serde_json::to_string(value).expect("serialize handle"));
    objects.canonical_handles.dedup();
    objects
        .publication_events
        .sort_by_key(|value| serde_json::to_string(value).expect("serialize publication"));
    objects.publication_events.dedup();
    objects
        .prestate_bindings
        .sort_by_key(|value| serde_json::to_string(value).expect("serialize prestate binding"));
    objects.prestate_bindings.dedup();
    objects
        .agreement_profiles
        .sort_by_key(|value| serde_json::to_string(value).expect("serialize agreement profile"));
    objects.agreement_profiles.dedup();
    objects
        .agreement_contracts
        .sort_by_key(|value| serde_json::to_string(value).expect("serialize agreement contract"));
    objects.agreement_contracts.dedup();
    objects
        .agreement_evidence
        .sort_by_key(|value| serde_json::to_string(value).expect("serialize agreement evidence"));
    objects.agreement_evidence.dedup();
    objects
        .agreement_states
        .sort_by_key(|value| serde_json::to_string(value).expect("serialize agreement state"));
    objects.agreement_states.dedup();
    objects
        .regions
        .sort_by_key(|value| serde_json::to_string(value).expect("serialize region"));
    objects.regions.dedup();
    objects
        .progress_contracts
        .sort_by_key(|value| serde_json::to_string(value).expect("serialize progress contract"));
    objects.progress_contracts.dedup();
    objects
        .progress_transitions
        .sort_by_key(|value| serde_json::to_string(value).expect("serialize progress transition"));
    objects.progress_transitions.dedup();
    objects
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
) -> (
    Vec<ObsEvent>,
    Vec<telltale_machine::model::effects::EffectTraceEntry>,
    ProtocolMachineSemanticObjects,
) {
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    machine.load_choreography(image).expect("load choreography");
    machine
        .run(&DeterministicHandler, 256)
        .expect("single-thread run");
    (
        machine.trace().to_vec(),
        machine.effect_trace().to_vec(),
        machine.semantic_objects(),
    )
}

fn run_threaded(
    image: &CodeImage,
) -> (
    Vec<ObsEvent>,
    Vec<telltale_machine::model::effects::EffectTraceEntry>,
    Vec<telltale_machine::LaneSelection>,
    ProtocolMachineSemanticObjects,
) {
    run_threaded_with_concurrency(image, 1, 4)
}

fn run_threaded_with_concurrency(
    image: &CodeImage,
    sessions: usize,
    concurrency: usize,
) -> (
    Vec<ObsEvent>,
    Vec<telltale_machine::model::effects::EffectTraceEntry>,
    Vec<telltale_machine::LaneSelection>,
    ProtocolMachineSemanticObjects,
) {
    let mut machine =
        ThreadedProtocolMachine::with_workers(ProtocolMachineConfig::default(), concurrency.max(1));
    for _ in 0..sessions {
        machine.load_choreography(image).expect("load choreography");
    }
    machine
        .run_concurrent(&DeterministicHandler, 256, concurrency)
        .expect("threaded run");
    (
        machine.trace().to_vec(),
        machine.effect_trace().to_vec(),
        machine.lane_trace().to_vec(),
        machine.semantic_objects(),
    )
}

#[test]
fn cross_target_matrix_native_single_vs_threaded_traces() {
    let images = [ping_pong_image(), chain_image()];
    for image in images {
        let (single_trace, single_effects, single_semantic_objects) = run_single_thread(&image);
        let (threaded_trace, threaded_effects, _, threaded_semantic_objects) = run_threaded(&image);
        let single_effect_sig = effect_signature(&single_effects);
        let threaded_effect_sig = effect_signature(&threaded_effects);

        let single_per_session = per_session(&single_trace);
        let threaded_per_session = per_session(&threaded_trace);
        assert_eq_structured_attributed(
            "semantic_audit.per_session",
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
        assert_eq_structured_attributed(
            "semantic_objects.bundle",
            &normalize_semantic_objects(single_semantic_objects),
            &normalize_semantic_objects(threaded_semantic_objects),
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
    let mut single = ProtocolMachine::new(ProtocolMachineConfig::default());
    single.load_choreography(&image).expect("load choreography");
    single.run(&recording, 256).expect("single baseline run");

    let replay_trace = recording.effect_trace();
    let single_trace = single.trace().to_vec();
    let single_semantic_objects = single.semantic_objects();

    let mut threaded = ThreadedProtocolMachine::with_workers(ProtocolMachineConfig::default(), 4);
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
        "replay.semantic_audit.per_session",
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
    assert_eq_structured(
        "replay.semantic_objects.bundle",
        &normalize_semantic_objects(single_semantic_objects),
        &normalize_semantic_objects(threaded.semantic_objects()),
    );
}

#[test]
fn cross_target_matrix_lane_selection_normalization_single_vs_multi_lane() {
    let image = ping_pong_image();

    // Single-lane baseline in threaded backend.
    let (_, _, single_lane_trace, _) = run_threaded_with_concurrency(&image, 3, 1);
    let single_lane = lane_selection_view(&single_lane_trace);
    assert!(
        single_lane.iter().all(|(_, _, _, lane)| *lane == 0),
        "single-lane run must only use lane slot 0"
    );

    // Multi-lane run over same workload.
    let (_, _, multi_lane_trace, _) = run_threaded_with_concurrency(&image, 3, 4);
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
