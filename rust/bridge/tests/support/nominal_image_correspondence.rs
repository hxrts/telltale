//! Actual DSL artifact -> Rust owned execution and executable Lean image.
#![allow(clippy::expect_used)]

use std::collections::{BTreeMap, VecDeque};
use std::num::NonZeroU64;
use std::sync::Mutex;

use serde_json::{json, Value};
use telltale_bridge::nominal_image::{
    capture_nominal_execution, nominal_executions_equivalent, NominalExecutableImage,
    NominalHostOutcome, NominalImageRunInput, NOMINAL_IMAGE_SCHEMA,
};
use telltale_bridge::{ProtocolMachineRunner, ProtocolMachineRunnerError};
use telltale_machine::model::effects::{
    EffectFailure, EffectHandler, EffectOutcome, EffectRequest, EffectRequestBody, EffectResult,
};
use telltale_machine::nominal_command::NominalCommandRequest;
use telltale_machine::runtime::loader::CodeImage;
use telltale_machine::{
    ProtocolMachine, ProtocolMachineConfig, ThreadedProtocolMachine, ThreadedRoundSemantics,
};

const SOURCE: &str = r#"
effect Host
  command ready : Unit -> Result String Bool
  {
    class : best_effort
    progress : may_block
    region : session
    agreement_use : forbidden
    reentrancy : allow
  }
agreement_profile SelectedLocal
  visibility immediate
  rule no_agreement
  usable_at none
  finalized_at none
  evidence witness
operation Check at A progress CheckProgress within bounded agreement SelectedLocal =
  let result at A = check Host.ready()
  case result of
    | Ok(value) => A -> B : Ready
    | Err(reason) => A -> B : Denied
protocol Commands uses Host =
  roles A, B
  A -> B : Start
"#;

struct Provider {
    outcomes: Mutex<VecDeque<NominalHostOutcome>>,
    requests: Mutex<Vec<NominalCommandRequest>>,
    readiness: Mutex<Option<telltale_types::ReadinessWitness>>,
}
impl Provider {
    fn new(outcomes: &[NominalHostOutcome]) -> Self {
        Self {
            outcomes: Mutex::new(outcomes.iter().cloned().collect()),
            requests: Mutex::new(Vec::new()),
            readiness: Mutex::new(None),
        }
    }
}
impl EffectHandler for Provider {
    fn handle_send(
        &self,
        _: &str,
        _: &str,
        _: &str,
        _: &[telltale_machine::Value],
    ) -> EffectResult<telltale_machine::Value> {
        EffectResult::failure(EffectFailure::unavailable(
            "nominal provider cannot dispatch legacy send",
        ))
    }
    fn handle_recv(
        &self,
        _: &str,
        _: &str,
        _: &str,
        _: &mut Vec<telltale_machine::Value>,
        _: &telltale_machine::Value,
    ) -> EffectResult<()> {
        EffectResult::failure(EffectFailure::unavailable(
            "nominal provider cannot dispatch legacy receive",
        ))
    }
    fn handle_choose(
        &self,
        _: &str,
        _: &str,
        _: &[String],
        _: &[telltale_machine::Value],
    ) -> EffectResult<String> {
        EffectResult::failure(EffectFailure::unavailable(
            "nominal provider cannot dispatch legacy choose",
        ))
    }
    fn handler_identity(&self) -> String {
        "nominal.bridge".into()
    }
    fn step(&self, _: &str, _: &mut Vec<telltale_machine::coroutine::Value>) -> EffectResult<()> {
        panic!("nominal executable image must never dispatch generic step")
    }
    fn handle_effect(&self, request: EffectRequest) -> EffectOutcome {
        if let EffectRequestBody::NominalCommand { request: actual } = &request.body {
            self.requests
                .lock()
                .expect("actual requests")
                .push(actual.clone());
            let outcome = self.outcomes.lock().expect("script").pop_front();
            match outcome {
                Some(outcome) => outcome.for_request_with_readiness(
                    actual,
                    self.readiness
                        .lock()
                        .expect("actual between-round result")
                        .as_ref(),
                ),
                None => EffectOutcome::failure(EffectFailure::unavailable(
                    "nominal provider script exhausted",
                )),
            }
        } else {
            super::PassthroughHandler.handle_effect(request)
        }
    }
}

fn image() -> CodeImage {
    telltale::compile_command_operation(
        SOURCE,
        "Check",
        &BTreeMap::from([(
            "bounded".into(),
            NonZeroU64::new(64).expect("selected nonzero window"),
        )]),
    )
    .expect("actual source compiler artifact")
}
fn input(image: &CodeImage, outcomes: &[NominalHostOutcome]) -> NominalImageRunInput {
    NominalImageRunInput {
        schema_version: NOMINAL_IMAGE_SCHEMA.into(),
        image: NominalExecutableImage::from_code_image(image).expect("preserve actual opcodes"),
        outcomes: vec![("A".into(), outcomes.to_vec())],
        handler_identity: "nominal.bridge".into(),
        num_registers: 16,
        max_steps: 64,
        deny_outputs: false,
        readiness_admission: None,
    }
}
fn cooperative(image: &CodeImage, outcomes: &[NominalHostOutcome]) -> Value {
    cooperative_configured(image, outcomes, 64, false)
}
fn cooperative_configured(
    image: &CodeImage,
    outcomes: &[NominalHostOutcome],
    rounds: usize,
    deny: bool,
) -> Value {
    let mut machine = ProtocolMachine::new(configured(deny));
    let owner = machine
        .load_choreography_owned(image, "original")
        .expect("genuine owned loader");
    let provider = Provider::new(outcomes);
    let actual_terminal = machine.run(&provider, rounds);
    let requests = provider.requests.lock().expect("actual requests");
    assert!(
        !requests.is_empty(),
        "source opcode must invoke the typed provider"
    );
    assert!(requests
        .iter()
        .all(|request| request.invocation == requests[0].invocation));
    assert!(requests
        .iter()
        .all(|request| request.session == owner.session_id()));
    let observed = capture_nominal_execution(
        image,
        machine.coroutines(),
        machine.effect_exchanges(),
        &machine.semantic_objects(),
        machine.trace(),
    )
    .expect("actual cooperative view");
    assert_terminal(&observed, actual_terminal.is_err());
    observed
}
fn configured(deny: bool) -> ProtocolMachineConfig {
    ProtocolMachineConfig {
        threaded_round_semantics: ThreadedRoundSemantics::CanonicalOneStep,
        output_condition_policy: if deny {
            telltale_machine::output_condition::OutputConditionPolicy::DenyAll
        } else {
            telltale_machine::output_condition::OutputConditionPolicy::AllowAll
        },
        ..ProtocolMachineConfig::default()
    }
}
fn threaded(image: &CodeImage, outcomes: &[NominalHostOutcome]) -> Value {
    threaded_configured(image, outcomes, 64, false)
}
fn threaded_configured(
    image: &CodeImage,
    outcomes: &[NominalHostOutcome],
    rounds: usize,
    deny: bool,
) -> Value {
    let config = configured(deny);
    let mut machine = ThreadedProtocolMachine::with_workers(config, 2);
    let admitted = machine.load_choreography_owned(image, "original");
    if let Err(error) = admitted {
        let joined = machine.shutdown_worker_pool();
        assert!(
            joined.is_ok(),
            "join actual workers before reporting admission failure"
        );
        panic!("actual owned admission failed: {error}");
    }
    let provider = Provider::new(outcomes);
    let actual_terminal = machine.run(&provider, rounds);
    let observed = capture_nominal_execution(
        image,
        &machine.coroutines(),
        machine.effect_exchanges(),
        &machine.semantic_objects(),
        machine.trace(),
    );
    let requests = provider.requests.lock().expect("actual requests").clone();
    let joined = machine.shutdown_worker_pool();
    assert!(
        joined.is_ok(),
        "join actual original workers before final assertions"
    );
    assert!(
        !requests.is_empty(),
        "actual worker must invoke the typed provider"
    );
    assert!(requests
        .iter()
        .all(|request| request.invocation == requests[0].invocation));
    let observed = observed.expect("actual threaded view");
    assert_terminal(&observed, actual_terminal.is_err());
    observed
}

fn assert_terminal(observed: &Value, failed: bool) {
    let faulted = observed["coroutines"]
        .as_array()
        .expect("actual coroutines")
        .iter()
        .any(|coro| coro["status"] == "faulted");
    assert_eq!(
        failed, faulted,
        "actual run result and typed terminal cause must agree"
    );
}

#[test]
fn actual_source_nominal_opcodes_and_typed_outcomes_match_executable_lean() {
    let runner = ProtocolMachineRunner::new()
        .expect("required actual Lean runner; never skip nominal correspondence");
    let image = image();
    let cases = vec![
        vec![NominalHostOutcome::Success {
            result: Ok(true),
            reply_offset: 0,
        }],
        vec![NominalHostOutcome::Success {
            result: Err("application refusal".into()),
            reply_offset: 0,
        }],
        vec![
            NominalHostOutcome::Blocked,
            NominalHostOutcome::Success {
                result: Ok(false),
                reply_offset: 0,
            },
        ],
        vec![NominalHostOutcome::Failure {
            failure: EffectFailure::denied("original semantic refusal"),
        }],
        vec![NominalHostOutcome::WrongResponse],
        vec![NominalHostOutcome::Success {
            result: Ok(true),
            reply_offset: 1,
        }],
    ];
    for outcomes in cases {
        let lean = runner
            .run_nominal_image(&input(&image, &outcomes))
            .expect("execute actual nominal image in Lean");
        let cooperative = cooperative(&image, &outcomes);
        let threaded = threaded(&image, &outcomes);
        assert!(
            nominal_executions_equivalent(&cooperative, &lean).expect("strict typed comparison"),
            "cooperative/model mismatch: Rust={cooperative} Lean={lean}"
        );
        assert!(
            nominal_executions_equivalent(&threaded, &lean).expect("strict typed comparison"),
            "threaded/model mismatch: Rust={threaded} Lean={lean}"
        );
        if matches!(
            outcomes.last(),
            Some(NominalHostOutcome::Success {
                reply_offset: 0,
                ..
            })
        ) {
            assert!(
                lean["coroutines"]
                    .as_array()
                    .expect("actual coroutines")
                    .iter()
                    .all(|coro| coro["status"] == json!("done")),
                "both original peers complete"
            );
        }
    }
}

#[test]
fn nominal_correspondence_refuses_erased_payload_outcomes_and_continuations() {
    let runner = ProtocolMachineRunner::new().expect("required actual Lean runner");
    let image = image();
    let configured = input(
        &image,
        &[NominalHostOutcome::Success {
            result: Ok(true),
            reply_offset: 0,
        }],
    );
    let original = runner
        .run_nominal_image(&configured)
        .expect("genuine positive executable control");
    for field in ["image", "outcomes"] {
        let mut erased = serde_json::to_value(&configured).expect("actual input");
        erased.as_object_mut().expect("input object").remove(field);
        assert!(
            runner
                .run_validation_operation("runNominalImage", &erased)
                .is_err(),
            "missing {field} must not use communication reconstruction"
        );
    }
    let mut missing_code = serde_json::to_value(&configured).expect("actual input");
    missing_code["image"]["programs"] = json!([]);
    assert!(runner
        .run_validation_operation("runNominalImage", &missing_code)
        .is_err());
    for field in [
        "exchanges",
        "effects",
        "operations",
        "coroutines",
        "invoked",
    ] {
        let mut erased = original.clone();
        erased.as_object_mut().expect("output object").remove(field);
        assert!(
            nominal_executions_equivalent(&erased, &erased).is_err(),
            "missing {field} must refuse"
        );
    }
    let mut absent = original.clone();
    absent["exchanges"] = json!([]);
    assert!(nominal_executions_equivalent(&absent, &absent).is_err());
    let mut changed_result = original.clone();
    changed_result["exchanges"][0]["response"]["result"] = json!({"Ok":{"Bool":false}});
    assert!(!nominal_executions_equivalent(&original, &changed_result)
        .expect("valid changed typed result"));
    let mut changed_pc = original.clone();
    changed_pc["coroutines"][0]["pc"] = json!(999);
    assert!(!nominal_executions_equivalent(&original, &changed_pc).expect("changed continuation"));
    let mut wrong_reference = original.clone();
    wrong_reference["operations"][0]["effect_ids"] = json!([999]);
    assert!(nominal_executions_equivalent(&wrong_reference, &wrong_reference).is_err());
}

#[test]
fn actual_pending_and_output_refusal_retain_original_typed_continuation() {
    let runner = ProtocolMachineRunner::new().expect("required executable Lean runner");
    let image = image();
    for (outcomes, rounds, deny) in [
        (vec![NominalHostOutcome::Blocked], 3_usize, false),
        (
            vec![NominalHostOutcome::Success {
                result: Ok(true),
                reply_offset: 0,
            }],
            64,
            true,
        ),
    ] {
        let mut configured = input(&image, &outcomes);
        configured.max_steps = rounds as u64;
        configured.deny_outputs = deny;
        let lean = runner
            .run_nominal_image(&configured)
            .expect("actual retained model holder");
        let cooperative = cooperative_configured(&image, &outcomes, rounds, deny);
        let threaded = threaded_configured(&image, &outcomes, rounds, deny);
        for actual in [&cooperative, &threaded, &lean] {
            let owner = actual["coroutines"]
                .as_array()
                .expect("actual coroutines")
                .iter()
                .find(|coro| coro["role"] == "A")
                .expect("original execution role");
            assert!(
                !owner["continuation"].is_null(),
                "same original holder must remain resident"
            );
            assert_eq!(owner["continuation"]["returned"].is_null(), !deny);
            let exchange = &actual["exchanges"][0];
            let effect = &actual["effects"][0];
            assert_eq!(owner["continuation"]["invocation"], effect["effect_id"]);
            assert_eq!(owner["continuation"]["issued_at"], exchange["issued_at"]);
            assert_eq!(effect["budget_ticks"], json!(64));
            if !deny {
                assert_eq!(exchange["issued_at"], json!(3));
                assert_eq!(effect["status"], json!("blocked"));
                assert_eq!(owner["pc"], json!(1));
            }

            let mut erased = actual.clone();
            let index = erased["coroutines"]
                .as_array()
                .expect("actual coroutines")
                .iter()
                .position(|coro| coro["role"] == "A")
                .expect("original owner");
            erased["coroutines"][index]["continuation"] = Value::Null;
            assert!(!nominal_executions_equivalent(actual, &erased)
                .expect("holder omission comparison"));
            if deny {
                let mut changed = actual.clone();
                changed["coroutines"][index]["continuation"]["returned"] =
                    json!({"Ok":{"Bool":false}});
                assert!(!nominal_executions_equivalent(actual, &changed)
                    .expect("retained result comparison"));
                let mut fault = actual.clone();
                fault["coroutines"][index]["fault"]["predicate_ref"] = json!("foreign.predicate");
                assert!(!nominal_executions_equivalent(actual, &fault)
                    .expect("terminal cause comparison"));
            }
        }
        assert!(
            nominal_executions_equivalent(&cooperative, &lean)
                .expect("pending/refusal co-op correspondence"),
            "actual Rust={cooperative} Lean={lean}"
        );
        assert!(nominal_executions_equivalent(&threaded, &lean)
            .expect("pending/refusal threaded correspondence"));
    }
}

#[test]
fn nominal_foreign_reply_relation_does_not_equate_distinct_foreign_ids() {
    let runner = ProtocolMachineRunner::new().expect("required executable Lean runner");
    let image = image();
    let actual = runner
        .run_nominal_image(&input(
            &image,
            &[NominalHostOutcome::Success {
                result: Ok(true),
                reply_offset: 1,
            }],
        ))
        .expect("actual foreign reply refusal control");
    assert!(nominal_executions_equivalent(&actual, &actual).expect("genuine foreign control"));
    let mut changed = actual.clone();
    let id = actual["effects"][0]["effect_id"]
        .as_u64()
        .expect("actual original occurrence");
    changed["exchanges"][0]["response"]["invocation"] =
        json!(id.checked_add(99).expect("foreign fixture ID"));
    assert!(nominal_executions_equivalent(&actual, &changed).is_err());
}

fn readiness_image() -> CodeImage {
    let source = SOURCE
        .replace(
            "command ready : Unit -> Result String Bool",
            "authoritative ready : Unit -> Result String ReadinessWitness",
        )
        .replace("class : best_effort", "class : authoritative")
        .replace("let result at A", "authoritative let result at A");
    telltale::compile_command_operation(
        &source,
        "Check",
        &BTreeMap::from([("bounded".into(), NonZeroU64::new(64).expect("window"))]),
    )
    .expect("actual authoritative source compiler")
}

macro_rules! readiness_executable_backend {
    ($name:ident, $make:expr, $registry:expr, $dispose:expr) => {
        fn $name(image: &CodeImage, deny: bool) -> Value {
            let outcomes = [NominalHostOutcome::Blocked, NominalHostOutcome::Readiness { reply_offset: 0 }];
            let mut machine = ($make)(configured(deny));
            let owner = machine.load_choreography_owned(image, "original").expect("actual original owner admission");
            let provider = Provider::new(&outcomes);
            let mut elapsed = 0_usize;
            let mut blocked = false;
            for _ in 0..64 {
                elapsed += 1;
                if machine.step_round(&provider, 1).is_err() { break; }
                let requests = provider.requests.lock().expect("actual requests");
                if let [request] = requests.as_slice() {
                    blocked = machine.semantic_objects().outstanding_effects.iter().any(|effect|
                        effect.effect_id == request.invocation && effect.session == Some(owner.session_id()) &&
                        effect.status == telltale_machine::semantic_objects::OutstandingEffectStatus::Blocked);
                }
                if blocked { break; }
            }
            if !blocked {
                ($dispose)(machine);
                panic!("actual original Blocked occurrence was not established");
            }
            let witness = owner.issue_readiness_witness(&mut machine, "Host.ready").expect("actual original issuer between rounds");
            *provider.readiness.lock().expect("same provider result slot") = Some(witness);
            let terminal = machine.run(&provider, 64_usize.saturating_sub(elapsed));
            let registry = ($registry)(&machine, owner.session_id());
            let captured = telltale_bridge::nominal_image::capture_nominal_execution_with_readiness(
                image, &machine.coroutines(), machine.effect_exchanges(), &machine.semantic_objects(),
                machine.trace(), Some(&registry));
            let requests = provider.requests.lock().expect("actual requests").clone();
            ($dispose)(machine);
            let captured = captured.expect("actual canonical registry and original continuation view");
            assert_eq!(requests.len(), 2, "real Blocked then retained original readiness result");
            assert_eq!(requests[0].invocation, requests[1].invocation);
            assert_eq!(requests[0].session, requests[1].session);
            assert_eq!(terminal.is_err(), deny);
            captured
        }
    };
}
readiness_executable_backend!(
    cooperative_readiness,
    ProtocolMachine::new,
    |machine: &ProtocolMachine, sid| machine
        .sessions()
        .get(sid)
        .expect("same actual session")
        .readiness_registry_view(),
    |_: ProtocolMachine| {}
);
readiness_executable_backend!(
    threaded_readiness,
    |config| ThreadedProtocolMachine::with_workers(config, 1),
    |machine: &ThreadedProtocolMachine, sid| machine
        .session_snapshots()
        .get(&sid)
        .expect("same actual resident session")
        .readiness_registry_view(),
    |machine: ThreadedProtocolMachine| {
        assert_eq!(
            machine
                .shutdown_worker_pool()
                .expect("same actual pool joined")
                .joined_workers(),
            1
        );
    }
);

#[test]
fn actual_readiness_source_registry_and_retained_commit_match_existing_lean_runner() {
    let runner = ProtocolMachineRunner::new().expect("required existing executable runner");
    let image = readiness_image();
    for deny in [false, true] {
        let outcomes = [
            NominalHostOutcome::Blocked,
            NominalHostOutcome::Readiness { reply_offset: 0 },
        ];
        let mut configured = input(&image, &outcomes);
        configured.deny_outputs = deny;
        configured.readiness_admission =
            Some(telltale_bridge::nominal_image::NominalReadinessAdmission {
                owner_id: "original".into(),
                issue_after_blocked: true,
            });
        let cooperative = cooperative_readiness(&image, deny);
        let threaded = threaded_readiness(&image, deny);
        let lean = runner
            .run_nominal_image(&configured)
            .expect("actual compiled opcode plus canonical model admission/issuer");
        assert!(nominal_executions_equivalent(&cooperative, &threaded)
            .expect("actual backend registry correspondence"));
        assert!(
            nominal_executions_equivalent(&cooperative, &lean)
                .expect("actual model registry/continuation correspondence"),
            "actual Rust={cooperative} Lean={lean}"
        );
        let registry = &cooperative["readiness"];
        assert_eq!(registry["audit"][0]["event"], json!("Issued"));
        assert!(registry["audit"][0]["tick"].as_u64().is_some());
        if deny {
            assert_eq!(
                registry["issued"]
                    .as_array()
                    .expect("resident original witness")
                    .len(),
                1
            );
            assert!(registry["consumed"]
                .as_array()
                .expect("consumed IDs")
                .is_empty());
        } else {
            assert!(registry["issued"].as_array().expect("issued").is_empty());
            assert_eq!(registry["consumed"], json!([1]));
            assert_eq!(registry["audit"][1]["event"], json!("Consumed"));
            assert!(registry["audit"][1]["tick"].as_u64().is_some());
        }
    }
}

#[test]
fn readiness_bridge_refuses_erased_original_issuer_and_semantic_field_mutations() {
    let image = readiness_image();
    let original = cooperative_readiness(&image, true);
    assert!(nominal_executions_equivalent(&original, &original)
        .expect("genuine refused-commit control"));
    let mut erased = original.clone();
    erased
        .as_object_mut()
        .expect("actual output")
        .remove("readiness");
    assert!(nominal_executions_equivalent(&erased, &erased).is_err());
    for field in [
        "owner_id",
        "generation",
        "session_id",
        "predicate_ref",
        "witness_id",
    ] {
        let mut changed = original.clone();
        changed["readiness"]["issued"][0][field] = if matches!(field, "owner_id" | "predicate_ref")
        {
            json!("foreign")
        } else {
            json!(999)
        };
        assert!(
            nominal_executions_equivalent(&changed, &changed).is_err(),
            "actual registry mismatch: {field}"
        );
    }
    let mut erased_holder = original.clone();
    let holder = erased_holder["coroutines"]
        .as_array_mut()
        .expect("actual coroutine observations")
        .iter_mut()
        .find(|coro| coro["role"] == json!("A"))
        .expect("actual original role");
    holder["continuation"]["returned"] = Value::Null;
    assert!(!nominal_executions_equivalent(&original, &erased_holder)
        .expect("genuine retained result cannot be erased"));
    let mut consumed_without_gate = original.clone();
    consumed_without_gate["readiness"]["consumed"] = json!([1]);
    assert!(nominal_executions_equivalent(&consumed_without_gate, &consumed_without_gate).is_err());
    let runner = ProtocolMachineRunner::new().expect("existing runner");
    let outcomes = [
        NominalHostOutcome::Blocked,
        NominalHostOutcome::Readiness { reply_offset: 0 },
    ];
    let mut absent_original = input(&image, &outcomes);
    absent_original.deny_outputs = true;
    let mut admitted_original = absent_original.clone();
    admitted_original.readiness_admission =
        Some(telltale_bridge::nominal_image::NominalReadinessAdmission {
            owner_id: "original".into(),
            issue_after_blocked: true,
        });
    let admitted = runner
        .run_nominal_image(&admitted_original)
        .expect("same actual runner admits original owner, Blocked issuer and retained result");
    assert!(nominal_executions_equivalent(&original, &admitted)
        .expect("same actual denied-output registry and continuation control"));
    let refusal = runner
        .run_nominal_image(&absent_original)
        .expect_err("removing only original admission must refuse the actual source declaration");
    match refusal {
        ProtocolMachineRunnerError::ProcessFailed { code, stderr } => {
            assert_eq!(code, 1, "canonical uncaught Lean IO.userError exit");
            assert!(
                stderr.contains(
                    "nominal executable image refused: readiness setup does not match the actual source declaration"
                ),
                "actual canonical absent-admission refusal required: {stderr}"
            );
        }
        other => panic!("absent admission must reach the canonical Lean refusal: {other}"),
    }
}

fn parent_image(authoritative: bool) -> CodeImage {
    let mut source = SOURCE
        .replace("  let result at A", "  begin Check\n  let result at A")
        .replace(
            "| Ok(value) => A -> B : Ready",
            "| Ok(value) =>\n        A -> B : Ready\n        await Check\n        resolve Check as Success",
        )
        .replace(
            "| Err(reason) => A -> B : Denied",
            "| Err(reason) =>\n        A -> B : Denied\n        await Check\n        resolve Check as Failure",
        );
    if authoritative {
        source = source
            .replace(
                "command ready : Unit -> Result String Bool",
                "authoritative ready : Unit -> Result String ReadinessWitness",
            )
            .replace("class : best_effort", "class : authoritative")
            .replace("let result at A", "authoritative let result at A");
    }
    telltale::compile_operation_image(
        &source,
        "Check",
        &BTreeMap::from([(
            "bounded".into(),
            NonZeroU64::new(64).expect("original window"),
        )]),
    )
    .expect("actual source parent and exact typed child compiler")
}

#[test]
fn compiled_original_parent_and_child_match_both_backends_and_executable_model() {
    let runner = ProtocolMachineRunner::new().expect("required actual executable model runner");
    let image = parent_image(false);
    for outcomes in [
        vec![NominalHostOutcome::Success {
            result: Ok(true),
            reply_offset: 0,
        }],
        vec![NominalHostOutcome::Success {
            result: Err("application refusal".into()),
            reply_offset: 0,
        }],
        vec![
            NominalHostOutcome::Blocked,
            NominalHostOutcome::Success {
                result: Ok(false),
                reply_offset: 0,
            },
        ],
        vec![NominalHostOutcome::Failure {
            failure: EffectFailure::denied("original child failure"),
        }],
    ] {
        let cooperative = cooperative(&image, &outcomes);
        let threaded = threaded(&image, &outcomes);
        let lean = runner
            .run_nominal_image(&input(&image, &outcomes))
            .expect("execute actual source-operation opcodes and original typed outcomes");
        assert!(nominal_executions_equivalent(&cooperative, &threaded)
            .expect("same parent/backend transaction"));
        assert!(
            nominal_executions_equivalent(&cooperative, &lean)
                .expect("actual enclosing operation correspondence"),
            "actual Rust={cooperative} Lean={lean}"
        );
        assert_eq!(
            cooperative["source_operations"]
                .as_array()
                .expect("actual original parent")
                .len(),
            1
        );
        assert_ne!(
            cooperative["source_operations"][0]["operation_id"],
            json!("effect:0")
        );
        assert_eq!(
            cooperative["source_operations"][0]["record"]["requires_proof"],
            json!(true)
        );
    }
}

#[test]
fn compiled_parent_readiness_retains_original_result_and_revocation_at_output_gate() {
    let runner = ProtocolMachineRunner::new().expect("required actual model runner");
    let image = parent_image(true);
    let outcomes = [
        NominalHostOutcome::Blocked,
        NominalHostOutcome::Readiness { reply_offset: 0 },
    ];
    for deny in [false, true] {
        let mut configured = input(&image, &outcomes);
        configured.deny_outputs = deny;
        configured.readiness_admission =
            Some(telltale_bridge::nominal_image::NominalReadinessAdmission {
                owner_id: "original".into(),
                issue_after_blocked: true,
            });
        let cooperative = cooperative_readiness(&image, deny);
        let threaded = threaded_readiness(&image, deny);
        let lean = runner
            .run_nominal_image(&configured)
            .expect("actual parent plus canonical readiness issuer");
        assert!(nominal_executions_equivalent(&cooperative, &threaded)
            .expect("actual same-owner backend result"));
        assert!(
            nominal_executions_equivalent(&cooperative, &lean)
                .expect("actual model owner/result/parent relation"),
            "actual Rust={cooperative} Lean={lean}"
        );
        let parent = &cooperative["source_operations"][0];
        assert_eq!(parent["resolved"], json!(!deny));
        assert_eq!(parent["invalidated"], json!(deny));
        assert_eq!(
            parent["completed_children"]
                .as_array()
                .expect("original returned result")
                .len(),
            1
        );
        if deny {
            assert!(!parent["execution_failure"].is_null());
            assert_eq!(cooperative["readiness"]["consumed"], json!([]));
        }
    }
}

#[test]
fn source_operation_comparison_refuses_erased_parent_and_rewritten_child_or_window() {
    let image = parent_image(false);
    let outcomes = [
        NominalHostOutcome::Blocked,
        NominalHostOutcome::Success {
            result: Ok(true),
            reply_offset: 0,
        },
    ];
    let original = cooperative(&image, &outcomes);
    assert!(nominal_executions_equivalent(&original, &original)
        .expect("actual parent positive control"));
    let mut missing = original.clone();
    missing
        .as_object_mut()
        .expect("actual execution view")
        .remove("source_operations");
    assert!(nominal_executions_equivalent(&missing, &missing).is_err());
    for field in ["children", "admitted_slots", "completed_children"] {
        let mut changed = original.clone();
        changed["source_operations"][0][field] = json!([]);
        assert!(
            nominal_executions_equivalent(&changed, &changed).is_err(),
            "erased original {field}"
        );
    }
    for field in ["issued_at", "runtime_original_pc"] {
        let mut changed = original.clone();
        changed["source_operations"][0][field] = json!(999);
        assert!(
            nominal_executions_equivalent(&changed, &changed).is_err(),
            "rewritten original {field}"
        );
    }
    let mut changed = original.clone();
    changed["source_operations"][0]["outcome"] = json!({"kind":"failure","value":null});
    assert!(nominal_executions_equivalent(&changed, &changed).is_err());
    let mut changed = original.clone();
    changed["source_operations"][0]["owner"]["generation"] = json!(999);
    assert!(!nominal_executions_equivalent(&original, &changed)
        .expect("original generation observation is retained"));
}
