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
use telltale_machine::durable::WalSyncRequest;
use telltale_machine::instr::{ImmValue, Instr, InvokeAction};
use telltale_machine::model::effects::{
    EffectFailure, EffectHandler, EffectResult, RecordingEffectHandler, SendDecision,
    SendDecisionInput,
};
use telltale_machine::model::output_condition::OutputConditionHint;
use telltale_machine::runtime::loader::CodeImage;
use telltale_machine::OutputConditionPolicy;
use telltale_machine::ProgressState;
use telltale_machine::ThreadedProtocolMachine;
use telltale_machine::{
    ObsEvent, ProtocolMachine, ProtocolMachineConfig, ProtocolMachineError,
    ProtocolMachineRefinementSlice, ProtocolMachineSemanticObjects,
};
use test_support::{
    choice_image, recursive_send_recv_image, simple_send_recv_image, PassthroughHandler,
};

type Normalized = (String, String, String, String);

#[derive(Debug)]
struct SemanticParityHandler;

impl EffectHandler for SemanticParityHandler {
    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &[Value],
    ) -> EffectResult<Value> {
        EffectResult::success(Value::Nat(7))
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
        EffectResult::success(labels.first().cloned().expect("choice label"))
    }

    fn step(&self, _role: &str, _state: &mut Vec<Value>) -> EffectResult<()> {
        EffectResult::success(())
    }

    fn handle_acquire(
        &self,
        _sid: usize,
        _role: &str,
        layer: &str,
        _state: &[Value],
    ) -> EffectResult<Value> {
        EffectResult::success(Value::Str(format!("evidence:{layer}")))
    }

    fn handle_release(
        &self,
        _sid: usize,
        _role: &str,
        _layer: &str,
        _evidence: &Value,
        _state: &[Value],
    ) -> EffectResult<()> {
        EffectResult::success(())
    }

    fn output_condition_hint(
        &self,
        sid: usize,
        role: &str,
        _state: &[Value],
    ) -> Option<OutputConditionHint> {
        Some(OutputConditionHint {
            predicate_ref: "machine.semantic.matrix".to_string(),
            witness_ref: Some(format!("sid:{sid}:role:{role}")),
        })
    }

    fn supports_wal_sync(&self) -> bool {
        true
    }

    fn wal_sync(&self, _sync: &WalSyncRequest) -> EffectResult<()> {
        EffectResult::success(())
    }
}

fn single_role_end_image(program: Vec<Instr>) -> CodeImage {
    CodeImage {
        programs: {
            let mut programs = BTreeMap::new();
            programs.insert("A".to_string(), program);
            programs
        },
        global_type: telltale_types::GlobalType::End,
        local_types: {
            let mut local_types = BTreeMap::new();
            local_types.insert("A".to_string(), telltale_types::LocalTypeR::End);
            local_types
        },
    }
}

#[derive(Debug)]
struct SemanticParitySnapshot {
    effect_exchanges: Vec<telltale_machine::model::effects::EffectExchangeRecord>,
    outstanding_effects: Vec<telltale_machine::semantic_objects::OutstandingEffect>,
    operation_instances: Vec<telltale_machine::semantic_objects::OperationInstance>,
    semantic_objects: ProtocolMachineSemanticObjects,
}

#[derive(Debug)]
struct SemanticParityFixture {
    name: &'static str,
    image: CodeImage,
    config: ProtocolMachineConfig,
    max_steps: usize,
}

fn run_semantic_parity_fixture_cooperative(
    fixture: &SemanticParityFixture,
    handler: &dyn EffectHandler,
) -> SemanticParitySnapshot {
    let mut machine = ProtocolMachine::new(fixture.config.clone());
    machine
        .load_choreography(&fixture.image)
        .expect("load cooperative fixture");
    machine
        .run(handler, fixture.max_steps)
        .expect("run cooperative fixture");
    SemanticParitySnapshot {
        effect_exchanges: machine.effect_exchanges().to_vec(),
        outstanding_effects: machine.outstanding_effects().to_vec(),
        operation_instances: machine.operation_instances().to_vec(),
        semantic_objects: machine.semantic_objects(),
    }
}

fn run_semantic_parity_fixture_threaded(
    fixture: &SemanticParityFixture,
    handler: &dyn EffectHandler,
) -> SemanticParitySnapshot {
    let mut machine = ThreadedProtocolMachine::with_workers(fixture.config.clone(), 2);
    machine
        .load_choreography(&fixture.image)
        .expect("load threaded fixture");
    machine
        .run(handler, fixture.max_steps)
        .expect("run threaded fixture");
    SemanticParitySnapshot {
        effect_exchanges: machine.effect_exchanges().to_vec(),
        outstanding_effects: machine.outstanding_effects().to_vec(),
        operation_instances: machine.operation_instances().to_vec(),
        semantic_objects: machine.semantic_objects(),
    }
}

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
    machine
        .run_concurrent(&handler, 200, concurrency)
        .expect("cooperative run");
    per_session(machine.trace())
}

fn run_threaded(
    images: &[telltale_machine::runtime::loader::CodeImage],
    workers: usize,
) -> BTreeMap<usize, Vec<Normalized>> {
    let handler = PassthroughHandler;
    let mut machine =
        ThreadedProtocolMachine::with_workers(ProtocolMachineConfig::default(), workers);
    for image in images {
        machine.load_choreography(image).expect("load image");
    }
    machine
        .run_concurrent(&handler, 200, 1)
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

fn run_semantic_objects(
    image: &telltale_machine::runtime::loader::CodeImage,
) -> (
    ProtocolMachineSemanticObjects,
    ProtocolMachineSemanticObjects,
) {
    let handler = PassthroughHandler;

    let mut coop = ProtocolMachine::new(ProtocolMachineConfig::default());
    coop.load_choreography(image).expect("load image");
    coop.run(&handler, 64).expect("cooperative run");

    let mut threaded = ThreadedProtocolMachine::with_workers(ProtocolMachineConfig::default(), 2);
    threaded.load_choreography(image).expect("load image");
    threaded.run(&handler, 64).expect("threaded run");

    (coop.semantic_objects(), threaded.semantic_objects())
}

fn run_refinement_slices(
    image: &telltale_machine::runtime::loader::CodeImage,
) -> (
    ProtocolMachineRefinementSlice,
    ProtocolMachineRefinementSlice,
) {
    let handler = PassthroughHandler;

    let mut coop = ProtocolMachine::new(ProtocolMachineConfig::default());
    coop.load_choreography(image).expect("load image");
    coop.run(&handler, 64).expect("cooperative run");

    let mut threaded = ThreadedProtocolMachine::with_workers(ProtocolMachineConfig::default(), 2);
    threaded.load_choreography(image).expect("load image");
    threaded
        .run_concurrent(&handler, 64, 1)
        .expect("threaded run at canonical concurrency=1");

    (
        coop.refinement_slice()
            .expect("export cooperative refinement slice"),
        threaded
            .refinement_slice()
            .expect("export threaded refinement slice"),
    )
}

#[allow(clippy::too_many_lines)]
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

fn normalize_refinement_slice(
    mut slice: ProtocolMachineRefinementSlice,
) -> ProtocolMachineRefinementSlice {
    slice.coroutines.sort_by_key(|coro| coro.coro_id);
    slice.sessions.sort_by_key(|session| session.sid);
    slice
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
fn test_semantic_object_exports_match_across_drivers() {
    let image = simple_send_recv_image("A", "B", "msg");
    let (coop_semantic_objects, threaded_semantic_objects) = run_semantic_objects(&image);
    assert_eq!(coop_semantic_objects, threaded_semantic_objects);
}

#[test]
fn test_instruction_owned_effect_semantics_match_across_drivers() {
    let allow_output = ProtocolMachineConfig {
        output_condition_policy: OutputConditionPolicy::PredicateAllowList(vec![
            "machine.semantic.matrix".to_string(),
        ]),
        ..ProtocolMachineConfig::default()
    };
    let fixtures = vec![
        SemanticParityFixture {
            name: "send_recv",
            image: simple_send_recv_image("A", "B", "msg"),
            config: ProtocolMachineConfig::default(),
            max_steps: 32,
        },
        SemanticParityFixture {
            name: "invoke_output_condition_and_wal",
            image: single_role_end_image(vec![
                Instr::Set {
                    dst: 1,
                    val: ImmValue::Nat(1),
                },
                Instr::Invoke {
                    action: InvokeAction::Reg(1),
                },
                Instr::Halt,
            ]),
            config: allow_output,
            max_steps: 32,
        },
        SemanticParityFixture {
            name: "acquire_release",
            image: single_role_end_image(vec![
                Instr::Acquire {
                    layer: "auth".to_string(),
                    dst: 2,
                },
                Instr::Release {
                    layer: "auth".to_string(),
                    evidence: 2,
                },
                Instr::Halt,
            ]),
            config: ProtocolMachineConfig::default(),
            max_steps: 32,
        },
    ];
    let handler = SemanticParityHandler;

    for fixture in &fixtures {
        let cooperative = run_semantic_parity_fixture_cooperative(fixture, &handler);
        let threaded = run_semantic_parity_fixture_threaded(fixture, &handler);
        assert_eq!(
            cooperative.effect_exchanges, threaded.effect_exchanges,
            "effect exchanges diverged for fixture {}",
            fixture.name
        );
        assert_eq!(
            cooperative.outstanding_effects, threaded.outstanding_effects,
            "outstanding effects diverged for fixture {}",
            fixture.name
        );
        assert_eq!(
            cooperative.operation_instances, threaded.operation_instances,
            "operation instances diverged for fixture {}",
            fixture.name
        );
        assert_eq!(
            cooperative.semantic_objects, threaded.semantic_objects,
            "semantic objects diverged for fixture {}",
            fixture.name
        );
    }
}

#[test]
fn test_refinement_slices_match_across_drivers_at_canonical_concurrency() {
    let image = simple_send_recv_image("A", "B", "msg");
    let (coop_slice, threaded_slice) = run_refinement_slices(&image);
    assert_eq!(
        normalize_refinement_slice(coop_slice),
        normalize_refinement_slice(threaded_slice)
    );
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
            "protocol_machine.observable_output".to_string(),
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
fn test_agreement_semantic_objects_match_across_drivers_for_output_condition_execution() {
    let image = simple_send_recv_image("A", "B", "msg");
    let handler = PassthroughHandler;

    let allow_cfg = ProtocolMachineConfig {
        output_condition_policy: OutputConditionPolicy::PredicateAllowList(vec![
            "protocol_machine.observable_output".to_string(),
        ]),
        ..ProtocolMachineConfig::default()
    };

    let mut coop = ProtocolMachine::new(allow_cfg.clone());
    coop.load_choreography(&image).expect("load image");
    coop.run(&handler, 50).expect("cooperative run");

    let mut threaded = ThreadedProtocolMachine::with_workers(allow_cfg, 2);
    threaded.load_choreography(&image).expect("load image");
    threaded.run(&handler, 50).expect("threaded run");

    let coop_semantics = normalize_semantic_objects(coop.semantic_objects());
    let threaded_semantics = normalize_semantic_objects(threaded.semantic_objects());

    assert_eq!(
        coop_semantics.agreement_profiles,
        threaded_semantics.agreement_profiles
    );
    assert_eq!(
        coop_semantics.agreement_contracts,
        threaded_semantics.agreement_contracts
    );
    assert_eq!(
        coop_semantics.agreement_evidence,
        threaded_semantics.agreement_evidence
    );
    assert_eq!(
        coop_semantics.agreement_states,
        threaded_semantics.agreement_states
    );
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
    assert_eq!(coop_predicate, "protocol_machine.observable_output");

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
            "protocol_machine.observable_output".to_string(),
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
    assert_eq!(
        normalize_semantic_objects(baseline.semantic_objects()),
        normalize_semantic_objects(replay_threaded.semantic_objects()),
        "cross-target replay semantic objects diverged"
    );
}
