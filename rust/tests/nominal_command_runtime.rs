//! Actual source/owned-loader/typed-callback/continuation fixtures.
//! These test synchronous semantic callbacks, not physical host teardown.

use std::collections::BTreeMap;
use std::num::NonZeroU64;
use std::sync::Mutex;

use telltale::compile_command_operation;
use telltale_machine::coroutine::Value;
use telltale_machine::model::effects::{EffectHandler, EffectResult};
use telltale_machine::nominal_command::{NominalCommandReply, NominalCommandRequest};
use telltale_machine::{ProtocolMachine, ProtocolMachineConfig};

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
agreement_profile ImmediateLocal
  visibility immediate
  rule no_agreement
  usable_at none
  finalized_at none
  evidence witness
operation Check at A progress CheckProgress within bounded agreement ImmediateLocal =
  let result at A = check Host.ready()
  case result of
    | Ok(value) => A -> B : Ready
    | Err(reason) => A -> B : Denied
protocol Commands uses Host =
  roles A, B
  A -> B : Start
"#;

fn windows() -> BTreeMap<String, NonZeroU64> {
    BTreeMap::from([("bounded".into(), NonZeroU64::new(64).expect("nonzero"))])
}

struct Reply {
    identity: &'static str,
    wrong_occurrence: bool,
    calls: Mutex<Vec<u64>>,
    result: Result<bool, String>,
    block_for: usize,
}
impl EffectHandler for Reply {
    fn handler_identity(&self) -> String {
        self.identity.to_string()
    }
    fn handle_send(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        state: &[Value],
    ) -> EffectResult<Value> {
        super::NoopHandler.handle_send(role, partner, label, state)
    }
    fn handle_recv(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        state: &mut Vec<Value>,
        payload: &Value,
    ) -> EffectResult<()> {
        super::NoopHandler.handle_recv(role, partner, label, state, payload)
    }
    fn handle_choose(
        &self,
        role: &str,
        partner: &str,
        labels: &[String],
        state: &[Value],
    ) -> EffectResult<String> {
        super::NoopHandler.handle_choose(role, partner, labels, state)
    }
    fn step(&self, _: &str, _: &mut Vec<Value>) -> EffectResult<()> {
        panic!("nominal command must never dispatch generic step")
    }
    fn handle_nominal_command(
        &self,
        request: &NominalCommandRequest,
    ) -> EffectResult<NominalCommandReply> {
        assert_eq!(request.declaration.interface, "Host");
        assert_eq!(request.declaration.operation, "ready");
        assert_eq!(request.role, "A");
        let mut calls = self.calls.lock().expect("calls");
        calls.push(request.invocation);
        if calls.len() <= self.block_for {
            return EffectResult::Blocked;
        }
        EffectResult::success(NominalCommandReply {
            invocation: request.invocation + u64::from(self.wrong_occurrence),
            result: self
                .result
                .clone()
                .map(telltale_machine::nominal_command::NominalCommandValue::Bool),
        })
    }
}

#[test]
fn source_owned_command_selects_original_typed_result_continuation() {
    for result in [Ok(true), Err("application refusal".to_string())] {
        let image = compile_command_operation(SOURCE, "Check", &windows())
            .expect("compile original operation");
        let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
        let owner = machine
            .load_choreography_owned(&image, "command-owner")
            .expect("issued original owner");
        let handler = Reply {
            identity: "H1",
            wrong_occurrence: false,
            calls: Mutex::new(Vec::new()),
            result: result.clone(),
            block_for: 0,
        };
        assert_eq!(
            machine
                .run(&handler, 64)
                .expect("execute command and selected terminal branch"),
            telltale_machine::RunStatus::AllDone
        );
        let coroutines = machine.session_coroutines(owner.session_id());
        assert_eq!(coroutines.len(), 2);
        assert!(coroutines
            .iter()
            .all(|coroutine| coroutine.status == telltale_machine::coroutine::CoroStatus::Done));
        let coroutine = machine
            .session_coroutines(owner.session_id())
            .into_iter()
            .find(|coroutine| coroutine.role == "A")
            .expect("actual owner coroutine");
        assert_eq!(
            coroutine.regs[2],
            match result {
                Ok(value) => Value::Bool(value),
                Err(reason) => Value::Str(reason),
            }
        );
        assert_eq!(handler.calls.lock().expect("calls").len(), 1);
        let view = machine.semantic_objects();
        let invocation = handler.calls.lock().expect("actual original invocation")[0];
        let operation = assert_original_nominal_publication(
            &view,
            invocation,
            owner.session_id(),
            &owner.capability().owner_id,
        );
        assert_output_check_materializations(&view, machine.output_condition_checks());
        assert!(operation.requires_proof);
        let profile = operation
            .agreement_profile
            .as_ref()
            .expect("source-selected profile retained");
        assert_eq!(profile.profile_name, "ImmediateLocal");
        assert_eq!(
            profile.rule,
            telltale_machine::semantic_objects::AgreementRule::NoAgreement
        );
        assert!(!view.authoritative_reads.iter().any(|read| read.kind
            == telltale_machine::semantic_objects::AuthoritativeReadKind::Readiness));
        let publication = view
            .publication_events
            .iter()
            .find(|event| event.operation_id == operation.operation_id)
            .expect("derived nominal publication observation");
        assert_eq!(
            publication.status,
            telltale_machine::semantic_objects::PublicationStatus::Rejected
        );
        assert_eq!(
            publication.reason.as_deref(),
            Some("proof-bearing success required")
        );
    }
}

fn assert_original_nominal_publication<'a>(
    view: &'a telltale_machine::semantic_objects::ProtocolMachineSemanticObjects,
    invocation: u64,
    session: telltale_machine::SessionId,
    owner: &str,
) -> &'a telltale_machine::semantic_objects::OperationInstance {
    use telltale_machine::semantic_objects::{OperationPhase, PublicationStatus};
    let effects: Vec<_> = view
        .outstanding_effects
        .iter()
        .filter(|effect| effect.effect_id == invocation)
        .collect();
    assert_eq!(effects.len(), 1);
    let effect = effects[0];
    assert_eq!(effect.effect_kind, "nominal_command");
    assert_eq!(effect.session, Some(session));
    assert_eq!(effect.owner_id.as_deref(), Some(owner));
    let operations: Vec<_> = view
        .operation_instances
        .iter()
        .filter(|operation| operation.operation_id == effect.operation_id)
        .collect();
    assert_eq!(operations.len(), 1);
    let operation = operations[0];
    assert_eq!(operation.effect_ids, vec![invocation]);
    assert_eq!(operation.session, effect.session);
    assert_eq!(operation.owner_id, effect.owner_id);
    assert_eq!(
        operation
            .agreement_profile
            .as_ref()
            .map(|profile| profile.profile_name.as_str()),
        Some("ImmediateLocal")
    );
    assert_eq!(operation.kind, "Check");
    assert_eq!(operation.phase, OperationPhase::Succeeded);
    assert!(operation.requires_proof);
    let publications: Vec<_> = view
        .publication_events
        .iter()
        .filter(|event| event.operation_id == operation.operation_id)
        .collect();
    assert_eq!(publications.len(), 1);
    assert_eq!(publications[0].status, PublicationStatus::Rejected);
    assert_eq!(
        publications[0].reason.as_deref(),
        Some("proof-bearing success required")
    );
    assert!(publications[0].proof_ref.is_none() && publications[0].handle_ref.is_none());
    operation
}

fn assert_output_check_materializations(
    view: &telltale_machine::semantic_objects::ProtocolMachineSemanticObjects,
    checks: &[telltale_machine::OutputConditionCheck],
) {
    use telltale_machine::semantic_objects::OperationPhase;
    assert!(
        !checks.is_empty(),
        "actual nominal/communication output gates ran"
    );
    assert_eq!(view.materialization_proofs.len(), checks.len());
    let operations: Vec<_> = view
        .operation_instances
        .iter()
        .filter(|operation| operation.kind == "materialization")
        .collect();
    assert_eq!(operations.len(), checks.len());
    // The semantic export canonically sorts proofs and materialization records.
    let mut checks: Vec<_> = checks.iter().collect();
    checks
        .sort_by_key(|check| format!("{}:{}", check.meta.predicate_ref, check.meta.output_digest));
    for ((check, proof), operation) in checks
        .iter()
        .zip(&view.materialization_proofs)
        .zip(operations)
    {
        assert_eq!(
            proof.proof_id,
            format!("{}:{}", check.meta.predicate_ref, check.meta.output_digest)
        );
        assert_eq!(proof.predicate_ref, check.meta.predicate_ref);
        assert_eq!(proof.witness_ref, check.meta.witness_ref);
        assert_eq!(proof.output_digest, check.meta.output_digest);
        assert_eq!(proof.passed, check.passed);
        assert_eq!(
            proof.session, None,
            "actual output-check projection has no session authority"
        );
        assert_eq!(
            operation.operation_id,
            format!("materialization:{}", proof.proof_id)
        );
        assert_eq!(operation.session, proof.session);
        assert!(
            operation.owner_id.is_none()
                && operation.effect_ids.is_empty()
                && operation.requires_proof
        );
        assert_eq!(
            operation.phase,
            if proof.passed {
                OperationPhase::Succeeded
            } else {
                OperationPhase::Failed
            }
        );
    }
    assert_materialization_handle_bijection(view);
}

fn assert_materialization_handle_bijection(
    view: &telltale_machine::semantic_objects::ProtocolMachineSemanticObjects,
) {
    use telltale_machine::semantic_objects::CanonicalHandleKind;
    let mut expected: Vec<_> = view
        .materialization_proofs
        .iter()
        .filter(|proof| proof.passed)
        .map(|proof| {
            (
                format!("materialization:{}", proof.output_digest),
                proof.session,
                None::<String>,
                Some(proof.proof_id.clone()),
            )
        })
        .collect();
    let mut actual: Vec<_> = view
        .canonical_handles
        .iter()
        .map(|handle| {
            assert_eq!(handle.kind, CanonicalHandleKind::Materialization);
            (
                handle.handle_id.clone(),
                handle.session,
                handle.owner_id.clone(),
                handle.proof_ref.clone(),
            )
        })
        .collect();
    expected.sort();
    actual.sort();
    assert_eq!(
        actual, expected,
        "full passed-proof/handle multiset, including multiplicity"
    );
}

#[test]
fn blocked_command_reuses_original_issued_occurrence() {
    let image = compile_command_operation(SOURCE, "Check", &windows()).expect("compile");
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    let _owner = machine
        .load_choreography_owned(&image, "command-owner")
        .expect("issued owner");
    let handler = Reply {
        identity: "H1",
        wrong_occurrence: false,
        calls: Mutex::new(Vec::new()),
        result: Ok(false),
        block_for: 1,
    };
    for _ in 0..16 {
        machine
            .step(&handler)
            .expect("step until actual Blocked callback");
        if !handler.calls.lock().expect("calls").is_empty() {
            break;
        }
    }
    let before = machine.semantic_objects();
    let original = before
        .outstanding_effects
        .iter()
        .find(|effect| effect.effect_kind == "nominal_command")
        .expect("actual issued nominal effect");
    assert_eq!(
        original.status,
        telltale_machine::semantic_objects::OutstandingEffectStatus::Blocked
    );
    assert_eq!(original.budget_ticks, Some(64));
    let progress = before
        .progress_contracts
        .iter()
        .find(|progress| progress.operation_id == original.operation_id)
        .expect("same original progress owner");
    assert_eq!(progress.budget_ticks, Some(64));
    machine
        .run(&handler, 64)
        .expect("same original pending occurrence resumes");
    let after = machine.semantic_objects();
    let completed = after
        .outstanding_effects
        .iter()
        .find(|effect| effect.effect_id == original.effect_id)
        .expect("same retained occurrence");
    assert_eq!(completed.budget_ticks, original.budget_ticks);
    assert_eq!(
        completed.status,
        telltale_machine::semantic_objects::OutstandingEffectStatus::Succeeded
    );
    let calls = handler.calls.lock().expect("calls");
    assert_eq!(calls.len(), 2);
    assert_eq!(calls[0], calls[1]);
}

#[test]
fn ordinary_loader_never_invokes_nominal_callback_without_issued_owner() {
    let image = compile_command_operation(SOURCE, "Check", &windows()).expect("compile");
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    machine
        .load_choreography(&image)
        .expect("static image load");
    let handler = Reply {
        identity: "H1",
        wrong_occurrence: false,
        calls: Mutex::new(Vec::new()),
        result: Ok(true),
        block_for: 0,
    };
    assert!(machine.run(&handler, 64).is_err());
    assert!(handler.calls.lock().expect("calls").is_empty());
}

#[test]
fn source_profile_window_and_unknown_operation_refuse_before_execution() {
    assert!(compile_command_operation(SOURCE, "Check", &BTreeMap::new()).is_err());
    assert!(compile_command_operation(SOURCE, "Foreign", &windows()).is_err());
    assert!(compile_command_operation(
        &SOURCE.replace("rule no_agreement", "rule consensus"),
        "Check",
        &windows()
    )
    .is_err());
    assert!(compile_command_operation(
        &SOURCE.replace("at A = check", "at B = check"),
        "Check",
        &windows()
    )
    .is_err());
}

#[test]
fn original_progress_invalidation_prevents_late_nominal_callback_and_commit() {
    use telltale_machine::semantic_objects::OutstandingEffectStatus;
    let windows = BTreeMap::from([("bounded".into(), NonZeroU64::new(1).expect("nonzero"))]);
    let image = compile_command_operation(SOURCE, "Check", &windows)
        .expect("compile selected original window");
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    let owner = machine
        .load_choreography_owned(&image, "command-owner")
        .expect("issued owner");
    let handler = Reply {
        identity: "H1",
        wrong_occurrence: false,
        calls: Mutex::new(Vec::new()),
        result: Ok(true),
        block_for: usize::MAX,
    };
    for _ in 0..32 {
        let _ = machine.step(&handler);
        if machine
            .semantic_objects()
            .outstanding_effects
            .iter()
            .any(|effect| {
                effect.effect_kind == "nominal_command"
                    && effect.status == OutstandingEffectStatus::Invalidated
            })
        {
            break;
        }
    }
    let view = machine.semantic_objects();
    let original = view
        .outstanding_effects
        .iter()
        .find(|effect| effect.effect_kind == "nominal_command")
        .expect("actual callback occurrence admitted");
    assert_eq!(original.status, OutstandingEffectStatus::Invalidated);
    assert_eq!(original.budget_ticks, Some(1));
    let calls = handler.calls.lock().expect("calls").len();
    assert!(
        calls > 0,
        "must exercise actual Blocked callback before invalidation"
    );
    for _ in 0..4 {
        let _ = machine.step(&handler);
    }
    assert_eq!(handler.calls.lock().expect("calls").len(), calls);
    let coroutine = machine
        .session_coroutines(owner.session_id())
        .into_iter()
        .find(|coroutine| coroutine.role == "A")
        .expect("owner coroutine");
    assert_eq!(coroutine.regs[2], Value::Unit);
    assert!(!machine
        .semantic_objects()
        .outstanding_effects
        .iter()
        .any(|effect| effect.effect_id == original.effect_id
            && effect.status == OutstandingEffectStatus::Succeeded));
}

#[test]
fn checkpoint_cannot_recreate_original_live_nominal_continuation() {
    let image = compile_command_operation(SOURCE, "Check", &windows()).expect("compile");
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    let owner = machine
        .load_choreography_owned(&image, "command-owner")
        .expect("issued owner");
    let handler = Reply {
        identity: "H1",
        wrong_occurrence: false,
        calls: Mutex::new(Vec::new()),
        result: Ok(true),
        block_for: usize::MAX,
    };
    for _ in 0..16 {
        machine
            .step(&handler)
            .expect("reach actual Blocked callback");
        if !handler.calls.lock().expect("calls").is_empty() {
            break;
        }
    }
    let calls = handler.calls.lock().expect("calls").clone();
    assert_eq!(calls.len(), 1);
    let before = machine.semantic_objects();
    let original: Vec<_> = before
        .outstanding_effects
        .into_iter()
        .filter(|effect| effect.effect_id == calls[0])
        .collect();
    assert_eq!(original.len(), 1);
    assert_eq!(
        original[0].status,
        telltale_machine::semantic_objects::OutstandingEffectStatus::Blocked
    );
    assert_eq!(original[0].session, Some(owner.session_id()));
    assert_eq!(
        original[0].owner_id.as_deref(),
        Some(owner.capability().owner_id.as_str())
    );
    assert_eq!(original[0].budget_ticks, Some(64));
    let pending = machine
        .session_coroutines(owner.session_id())
        .into_iter()
        .find(|coroutine| coroutine.role == "A")
        .expect("actual original coroutine")
        .nominal_continuation_view()
        .expect("actual retained opaque continuation");
    assert_eq!(pending.invocation, calls[0]);
    assert_eq!(&pending.original_owner, owner.capability());
    assert_eq!(pending.issued_at, original[0].ordering_key);
    let original_tick = machine.clock().tick;
    // Existing simulator persisted checkpoints and machine restoration tests use
    // this self-describing CBOR codec. JSON does not support live endpoint-map keys.
    let mut encoded = Vec::new();
    ciborium::ser::into_writer(&machine, &mut encoded).expect("canonical checkpoint CBOR");
    let mut restored: ProtocolMachine = ciborium::de::from_reader(encoded.as_slice())
        .expect("restore full actual state without opaque owner");
    restored
        .validate_post_decode()
        .expect("canonical checkpoint structural validation");
    assert_eq!(restored.clock().tick, original_tick);
    let decoded: Vec<_> = restored
        .semantic_objects()
        .outstanding_effects
        .into_iter()
        .filter(|effect| effect.effect_id == calls[0])
        .collect();
    assert_eq!(
        decoded, original,
        "same full semantic occurrence, not reconstructed authority"
    );
    let coroutines = restored.session_coroutines(owner.session_id());
    let actual: Vec<_> = coroutines
        .iter()
        .filter(|coroutine| coroutine.role == "A")
        .collect();
    assert_eq!(actual.len(), 1);
    assert!(actual[0].nominal_continuation_view().is_none());
    assert!(restored.run(&handler, 64).is_err());
    assert_eq!(*handler.calls.lock().expect("calls"), calls);
    assert!(restored
        .semantic_objects()
        .outstanding_effects
        .iter()
        .any(|effect| effect.effect_id == calls[0]));
}

#[test]
fn transferred_generation_cannot_resume_old_nominal_continuation() {
    let image = compile_command_operation(SOURCE, "Check", &windows()).expect("compile");
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    let owner = machine
        .load_choreography_owned(&image, "command-owner")
        .expect("issued owner");
    let handler = Reply {
        identity: "H1",
        wrong_occurrence: false,
        calls: Mutex::new(Vec::new()),
        result: Ok(true),
        block_for: 1,
    };
    for _ in 0..16 {
        machine
            .step(&handler)
            .expect("reach actual Blocked callback");
        if !handler.calls.lock().expect("calls").is_empty() {
            break;
        }
    }
    let calls = handler.calls.lock().expect("calls").clone();
    assert_eq!(calls.len(), 1);
    let receipt = owner
        .begin_transfer(
            &mut machine,
            "new-owner",
            telltale_machine::OwnershipScope::Session,
        )
        .expect("actual original transfer");
    let _new_owner = owner
        .commit_transfer(&mut machine, &receipt)
        .expect("new issued generation");
    assert!(machine.run(&handler, 64).is_err());
    assert_eq!(*handler.calls.lock().expect("calls"), calls);
}

#[test]
fn blocked_original_command_refuses_changed_semantic_handler_before_callback() {
    let image = compile_command_operation(SOURCE, "Check", &windows()).expect("compile");
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    let _owner = machine
        .load_choreography_owned(&image, "command-owner")
        .expect("issued owner");
    let original = Reply {
        identity: "H1",
        wrong_occurrence: false,
        calls: Mutex::new(Vec::new()),
        result: Ok(true),
        block_for: 1,
    };
    for _ in 0..16 {
        machine
            .step(&original)
            .expect("reach original Blocked callback");
        if !original.calls.lock().expect("calls").is_empty() {
            break;
        }
    }
    assert_eq!(original.calls.lock().expect("calls").len(), 1);
    let before = machine.semantic_objects();
    let occurrence = before
        .outstanding_effects
        .iter()
        .find(|effect| effect.effect_kind == "nominal_command")
        .expect("original occurrence");
    assert_eq!(occurrence.handler_identity, "H1");
    assert_eq!(
        occurrence.status,
        telltale_machine::semantic_objects::OutstandingEffectStatus::Blocked
    );
    let foreign = Reply {
        identity: "H2",
        wrong_occurrence: false,
        calls: Mutex::new(Vec::new()),
        result: Ok(true),
        block_for: 0,
    };
    assert!(machine.run(&foreign, 64).is_err());
    assert!(foreign.calls.lock().expect("foreign calls").is_empty());
    let after = machine.semantic_objects();
    let retained = after
        .outstanding_effects
        .iter()
        .find(|effect| effect.effect_id == occurrence.effect_id)
        .expect("original occurrence retained");
    assert_eq!(retained.handler_identity, occurrence.handler_identity);
    assert_eq!(retained.budget_ticks, occurrence.budget_ticks);
    assert_ne!(
        retained.status,
        telltale_machine::semantic_objects::OutstandingEffectStatus::Succeeded
    );
}

#[test]
fn expired_original_window_refuses_while_effect_is_still_blocked() {
    use telltale_machine::semantic_objects::OutstandingEffectStatus;
    let windows = BTreeMap::from([("bounded".into(), NonZeroU64::new(1).expect("nonzero"))]);
    let image = compile_command_operation(SOURCE, "Check", &windows).expect("compile");
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    let _owner = machine
        .load_choreography_owned(&image, "command-owner")
        .expect("original owner");
    let handler = Reply {
        identity: "H1",
        wrong_occurrence: false,
        calls: Mutex::new(Vec::new()),
        result: Ok(true),
        block_for: usize::MAX,
    };
    let mut refused = false;
    for _ in 0..16 {
        if machine.step(&handler).is_err() {
            refused = true;
            break;
        }
    }
    assert!(
        refused,
        "original window must refuse before multi-window escalation finishes"
    );
    let view = machine.semantic_objects();
    let original = view
        .outstanding_effects
        .iter()
        .find(|effect| effect.effect_kind == "nominal_command")
        .expect("original actual Blocked callback");
    assert_eq!(original.status, OutstandingEffectStatus::Blocked);
    assert_eq!(original.budget_ticks, Some(1));
    assert!(
        machine.clock().tick
            > original
                .ordering_key
                .checked_add(1)
                .expect("original endpoint")
    );
    let calls = handler.calls.lock().expect("calls").len();
    assert!(calls > 0);
    for _ in 0..2 {
        let _ = machine.step(&handler);
    }
    assert_eq!(handler.calls.lock().expect("calls").len(), calls);
}

#[test]
fn foreign_nominal_reply_occurrence_cannot_mutate_result_or_publish_success() {
    use telltale_machine::semantic_objects::OutstandingEffectStatus;
    let image = compile_command_operation(SOURCE, "Check", &windows()).expect("compile");
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    let owner = machine
        .load_choreography_owned(&image, "command-owner")
        .expect("issued owner");
    let handler = Reply {
        identity: "H1",
        wrong_occurrence: true,
        calls: Mutex::new(Vec::new()),
        result: Ok(true),
        block_for: 0,
    };
    assert!(machine.run(&handler, 64).is_err());
    let calls = handler.calls.lock().expect("calls");
    assert_eq!(calls.len(), 1);
    let view = machine.semantic_objects();
    let original = view
        .outstanding_effects
        .iter()
        .find(|effect| effect.effect_id == calls[0])
        .expect("actual original occurrence");
    assert_eq!(original.status, OutstandingEffectStatus::Failed);
    let coroutine = machine
        .session_coroutines(owner.session_id())
        .into_iter()
        .find(|coroutine| coroutine.role == "A")
        .expect("owner coroutine");
    assert_eq!(coroutine.regs[2], Value::Unit);
    assert!(!view
        .publication_events
        .iter()
        .any(|event| event.operation_id == original.operation_id
            && event.status == telltale_machine::semantic_objects::PublicationStatus::Published));
}

#[test]
fn original_endpoint_overflow_refuses_before_nominal_issuance_or_callback() {
    let windows = BTreeMap::from([(
        "bounded".into(),
        NonZeroU64::new(u64::MAX).expect("nonzero"),
    )]);
    let image = compile_command_operation(SOURCE, "Check", &windows)
        .expect("compile selected budget without inventing an endpoint");
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    let _owner = machine
        .load_choreography_owned(&image, "command-owner")
        .expect("actual issued owner");
    let handler = Reply {
        identity: "H1",
        wrong_occurrence: false,
        calls: Mutex::new(Vec::new()),
        result: Ok(true),
        block_for: 0,
    };
    assert!(machine.run(&handler, 64).is_err());
    assert!(
        machine.clock().tick > 0,
        "actual admission tick must make the selected addition overflow"
    );
    assert!(handler.calls.lock().expect("calls").is_empty());
    assert!(!machine
        .semantic_objects()
        .outstanding_effects
        .iter()
        .any(|effect| effect.effect_kind == "nominal_command"));
}

telltale::tell! {
    effect Host
      command ready : Unit -> Result String Bool
      {
        class : best_effort
        progress : may_block
        region : session
        agreement_use : forbidden
        reentrancy : allow
      }
    agreement_profile LocalCommandProfile
      visibility immediate
      rule no_agreement
      usable_at none
      finalized_at none
      evidence witness
    operation Check at A progress CheckProgress within bounded agreement LocalCommandProfile =
      let result at A = check Host.ready()
      case result of
        | Ok(value) => A -> B : Ready
        | Err(reason) => A -> B : Denied
    protocol MacroNominalCommand uses Host =
      roles A, B
      A -> B : Start
}

#[test]
fn macro_original_source_compiles_and_executes_selected_nominal_operation() {
    let image = MacroNominalCommand::operation_image("Check", &windows())
        .expect("actual macro-preserved original source");
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    let owner = machine
        .load_choreography_owned(&image, "command-owner")
        .expect("issued owner");
    let handler = Reply {
        identity: "H1",
        wrong_occurrence: false,
        calls: Mutex::new(Vec::new()),
        result: Ok(true),
        block_for: 0,
    };
    assert_eq!(
        machine
            .run(&handler, 64)
            .expect("actual macro command execution"),
        telltale_machine::RunStatus::AllDone
    );
    assert_eq!(handler.calls.lock().expect("calls").len(), 1);
    let view = machine.semantic_objects();
    let operation = view
        .operation_instances
        .iter()
        .find(|operation| {
            operation.session == Some(owner.session_id()) && operation.kind == "Check"
        })
        .expect("same source-selected operation");
    assert_eq!(
        operation
            .agreement_profile
            .as_ref()
            .expect("actual source profile")
            .profile_name,
        "LocalCommandProfile"
    );
}

#[cfg(all(feature = "multi-thread", not(target_arch = "wasm32")))]
mod threaded_nominal {
    use super::*;
    use telltale_machine::semantic_objects::OutstandingEffectStatus;
    use telltale_machine::{ThreadedProtocolMachine, ThreadedRoundSemantics};

    fn config() -> ProtocolMachineConfig {
        ProtocolMachineConfig {
            threaded_round_semantics: ThreadedRoundSemantics::CanonicalOneStep,
            ..ProtocolMachineConfig::default()
        }
    }

    #[test]
    fn source_command_typed_branches_match_canonical_threaded_execution() {
        for result in [Ok(true), Err("application refusal".to_string())] {
            let image = compile_command_operation(SOURCE, "Check", &windows())
                .expect("compile actual source");
            let mut machine = ThreadedProtocolMachine::with_workers(config(), 2);
            let owner = machine
                .load_choreography_owned(&image, "command-owner")
                .expect("issued original threaded owner");
            let handler = Reply {
                identity: "H1",
                wrong_occurrence: false,
                calls: Mutex::new(Vec::new()),
                result: result.clone(),
                block_for: 0,
            };
            let execution = machine.run(&handler, 64);
            let coroutines = machine.session_coroutines(owner.session_id());
            let view = machine.semantic_objects();
            let checks = machine.output_condition_checks().to_vec();
            let shutdown = machine.shutdown_worker_pool();
            assert!(
                shutdown.is_ok(),
                "join the actual workers before result assertions"
            );
            assert_eq!(
                execution.expect("typed execution"),
                telltale_machine::RunStatus::AllDone
            );
            assert_eq!(handler.calls.lock().expect("calls").len(), 1);
            assert!(coroutines
                .iter()
                .all(|coro| coro.status == telltale_machine::coroutine::CoroStatus::Done));
            let original = view
                .outstanding_effects
                .iter()
                .find(|effect| effect.effect_kind == "nominal_command")
                .expect("actual pre-dispatch occurrence");
            assert_eq!(original.status, OutstandingEffectStatus::Succeeded);
            let coroutine = coroutines
                .iter()
                .find(|coro| coro.role == "A")
                .expect("original role");
            assert_eq!(
                coroutine.regs[2],
                match result {
                    Ok(value) => Value::Bool(value),
                    Err(error) => Value::Str(error),
                }
            );
            let operation = assert_original_nominal_publication(
                &view,
                original.effect_id,
                owner.session_id(),
                &owner.capability().owner_id,
            );
            assert_output_check_materializations(&view, &checks);
            assert!(operation.requires_proof);
            assert_eq!(
                view.publication_events
                    .iter()
                    .find(|event| event.operation_id == operation.operation_id)
                    .expect("publication observation")
                    .status,
                telltale_machine::semantic_objects::PublicationStatus::Rejected
            );
        }
    }

    #[test]
    fn threaded_blocked_command_keeps_original_occurrence_and_tick_window() {
        let image = compile_command_operation(SOURCE, "Check", &windows()).expect("compile");
        let mut machine = ThreadedProtocolMachine::with_workers(config(), 2);
        let _owner = machine
            .load_choreography_owned(&image, "command-owner")
            .expect("actual owner");
        let handler = Reply {
            identity: "H1",
            wrong_occurrence: false,
            calls: Mutex::new(Vec::new()),
            result: Ok(false),
            block_for: 1,
        };
        for _ in 0..16 {
            machine
                .step_round(&handler, 1)
                .expect("reach original Blocked callback");
            if !handler.calls.lock().expect("calls").is_empty() {
                break;
            }
        }
        let before = machine.semantic_objects();
        let execution = machine.run(&handler, 64);
        let after = machine.semantic_objects();
        let shutdown = machine.shutdown_worker_pool();
        assert!(shutdown.is_ok());
        let original = before
            .outstanding_effects
            .iter()
            .find(|effect| effect.effect_kind == "nominal_command")
            .expect("actual original occurrence");
        assert_eq!(original.status, OutstandingEffectStatus::Blocked);
        assert_eq!(original.budget_ticks, Some(64));
        assert_eq!(
            before
                .progress_contracts
                .iter()
                .find(|progress| progress.operation_id == original.operation_id)
                .expect("original progress owner")
                .budget_ticks,
            original.budget_ticks
        );
        assert_eq!(
            execution.expect("resume same original occurrence"),
            telltale_machine::RunStatus::AllDone
        );
        let calls = handler.calls.lock().expect("calls");
        assert_eq!(calls.len(), 2);
        assert_eq!(calls[0], calls[1]);
        assert_eq!(
            after
                .outstanding_effects
                .iter()
                .find(|effect| effect.effect_id == original.effect_id)
                .expect("same occurrence")
                .status,
            OutstandingEffectStatus::Succeeded
        );
    }

    #[test]
    fn threaded_unowned_and_foreign_reply_refuse_without_nominal_success() {
        for unowned in [true, false] {
            let image = compile_command_operation(SOURCE, "Check", &windows()).expect("compile");
            let mut machine = ThreadedProtocolMachine::with_workers(config(), 2);
            if unowned {
                machine.load_choreography(&image).expect("static image");
            } else {
                let _owner = machine
                    .load_choreography_owned(&image, "command-owner")
                    .expect("actual owner");
            }
            let handler = Reply {
                identity: "H1",
                wrong_occurrence: true,
                calls: Mutex::new(Vec::new()),
                result: Ok(true),
                block_for: 0,
            };
            let execution = machine.run(&handler, 64);
            let view = machine.semantic_objects();
            let shutdown = machine.shutdown_worker_pool();
            assert!(shutdown.is_ok());
            assert!(execution.is_err());
            assert_eq!(
                handler.calls.lock().expect("calls").len(),
                usize::from(!unowned)
            );
            assert!(!view
                .outstanding_effects
                .iter()
                .any(|effect| effect.effect_kind == "nominal_command"
                    && effect.status == OutstandingEffectStatus::Succeeded));
        }
    }

    #[test]
    fn threaded_original_window_refuses_before_multistage_progress_timeout() {
        let windows = BTreeMap::from([("bounded".into(), NonZeroU64::new(1).expect("nonzero"))]);
        let image = compile_command_operation(SOURCE, "Check", &windows).expect("compile");
        let mut machine = ThreadedProtocolMachine::with_workers(config(), 2);
        let _owner = machine
            .load_choreography_owned(&image, "command-owner")
            .expect("actual owner");
        let handler = Reply {
            identity: "H1",
            wrong_occurrence: false,
            calls: Mutex::new(Vec::new()),
            result: Ok(true),
            block_for: usize::MAX,
        };
        let mut refusal = false;
        for _ in 0..16 {
            if machine.step_round(&handler, 1).is_err() {
                refusal = true;
                break;
            }
        }
        let tick = machine.clock().tick;
        let view = machine.semantic_objects();
        let shutdown = machine.shutdown_worker_pool();
        assert!(shutdown.is_ok());
        assert!(refusal);
        let original = view
            .outstanding_effects
            .iter()
            .find(|effect| effect.effect_kind == "nominal_command")
            .expect("actual pending callback");
        assert_eq!(original.status, OutstandingEffectStatus::Blocked);
        assert!(
            tick > original
                .ordering_key
                .checked_add(1)
                .expect("original endpoint")
        );
        assert!(!handler.calls.lock().expect("calls").is_empty());
    }
}

struct ChangingIdentity {
    reply: Reply,
    changed: std::sync::atomic::AtomicBool,
    change_in_gate: bool,
    #[cfg(not(target_arch = "wasm32"))]
    callback_threads: Mutex<Vec<std::thread::ThreadId>>,
}
impl ChangingIdentity {
    fn new(change_in_gate: bool) -> Self {
        Self {
            reply: Reply {
                identity: "H1",
                wrong_occurrence: false,
                calls: Mutex::new(Vec::new()),
                result: Ok(true),
                block_for: 0,
            },
            changed: std::sync::atomic::AtomicBool::new(false),
            change_in_gate,
            #[cfg(not(target_arch = "wasm32"))]
            callback_threads: Mutex::new(Vec::new()),
        }
    }
}
impl EffectHandler for ChangingIdentity {
    fn handler_identity(&self) -> String {
        if self.changed.load(std::sync::atomic::Ordering::SeqCst) {
            "H2"
        } else {
            "H1"
        }
        .into()
    }
    fn handle_nominal_command(
        &self,
        request: &NominalCommandRequest,
    ) -> EffectResult<NominalCommandReply> {
        #[cfg(not(target_arch = "wasm32"))]
        self.callback_threads
            .lock()
            .expect("actual callback threads")
            .push(std::thread::current().id());
        let result = self.reply.handle_nominal_command(request);
        if !self.change_in_gate {
            self.changed
                .store(true, std::sync::atomic::Ordering::SeqCst);
        }
        result
    }
    fn output_condition_hint(
        &self,
        _: telltale_machine::SessionId,
        _: &str,
        _: &[Value],
    ) -> Option<telltale_machine::model::output_condition::OutputConditionHint> {
        if self.change_in_gate
            && !self
                .reply
                .calls
                .lock()
                .expect("actual nominal calls")
                .is_empty()
        {
            self.changed
                .store(true, std::sync::atomic::Ordering::SeqCst);
        }
        None
    }
    fn handle_send(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        state: &[Value],
    ) -> EffectResult<Value> {
        self.reply.handle_send(role, partner, label, state)
    }
    fn handle_recv(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        state: &mut Vec<Value>,
        payload: &Value,
    ) -> EffectResult<()> {
        self.reply.handle_recv(role, partner, label, state, payload)
    }
    fn handle_choose(
        &self,
        role: &str,
        partner: &str,
        labels: &[String],
        state: &[Value],
    ) -> EffectResult<String> {
        self.reply.handle_choose(role, partner, labels, state)
    }
    fn step(&self, _: &str, _: &mut Vec<Value>) -> EffectResult<()> {
        panic!("nominal command cannot use generic step")
    }
}

#[test]
fn changed_identity_after_callback_or_gate_cannot_publish_nominal_success() {
    for gate in [false, true] {
        let image = compile_command_operation(SOURCE, "Check", &windows()).expect("compile");
        let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
        let _owner = machine
            .load_choreography_owned(&image, "command-owner")
            .expect("issued owner");
        let handler = ChangingIdentity::new(gate);
        assert!(machine.run(&handler, 64).is_err());
        assert_eq!(handler.reply.calls.lock().expect("actual calls").len(), 1);
        assert!(!machine
            .trace()
            .iter()
            .any(|event| matches!(event, telltale_machine::ObsEvent::Invoked { .. })));
        let original = machine.semantic_objects();
        assert!(!original
            .outstanding_effects
            .iter()
            .any(|effect| effect.effect_kind == "nominal_command"
                && effect.status
                    == telltale_machine::semantic_objects::OutstandingEffectStatus::Succeeded));
        assert!(machine.effect_exchanges().iter().any(|exchange| matches!(&exchange.outcome.response, Some(telltale_machine::model::effects::EffectResponse::NominalCommand { reply }) if reply.result == Ok(telltale_machine::nominal_command::NominalCommandValue::Bool(true)))));
    }
}

#[cfg(all(feature = "multi-thread", not(target_arch = "wasm32")))]
#[test]
fn actual_worker_identity_refusal_precedes_main_success_publication() {
    for gate in [false, true] {
        run_identity_dispatch_case(gate, false);
        run_identity_dispatch_case(gate, true);
    }
}

#[cfg(all(feature = "multi-thread", not(target_arch = "wasm32")))]
fn run_identity_dispatch_case(gate: bool, parallel: bool) {
    let image = compile_command_operation(SOURCE, "Check", &windows()).expect("compile");
    let mut machine = telltale_machine::ThreadedProtocolMachine::with_workers(
        ProtocolMachineConfig {
            threaded_round_semantics: if parallel {
                telltale_machine::ThreadedRoundSemantics::WaveParallelExtension
            } else {
                telltale_machine::ThreadedRoundSemantics::CanonicalOneStep
            },
            ..ProtocolMachineConfig::default()
        },
        2,
    );
    let background = if parallel {
        Some(
            machine
                .load_choreography_owned(&identity_background_image(), "identity/background")
                .expect("real independent ready session, admitted before nominal role"),
        )
    } else {
        None
    };
    let owner = machine
        .load_choreography_owned(&image, "command-owner")
        .expect("issued owner");
    let original_coro = machine
        .session_coroutines(owner.session_id())
        .iter()
        .find(|coroutine| coroutine.role == "A")
        .expect("original nominal role")
        .id;
    let caller = std::thread::current().id();
    let handler = ChangingIdentity::new(gate);
    let execution = machine.run(&handler, 64);
    let trace = machine.trace().to_vec();
    let view = machine.semantic_objects();
    let exchanges = machine.effect_exchanges().to_vec();
    let selections = machine.lane_trace().to_vec();
    let shutdown = machine.shutdown_worker_pool();
    assert!(shutdown.is_ok());
    assert!(execution.is_err());
    assert_eq!(handler.reply.calls.lock().expect("calls").len(), 1);
    let threads = handler
        .callback_threads
        .lock()
        .expect("actual worker callbacks");
    assert_eq!(threads.len(), 1);
    assert_identity_dispatch(
        &selections,
        &exchanges,
        original_coro,
        background.as_ref().map(|owner| owner.session_id()),
        threads[0],
        caller,
    );
    assert!(!trace
        .iter()
        .any(|event| matches!(event, telltale_machine::ObsEvent::Invoked { .. })));
    assert!(!view
        .outstanding_effects
        .iter()
        .any(|effect| effect.effect_kind == "nominal_command"
            && effect.status
                == telltale_machine::semantic_objects::OutstandingEffectStatus::Succeeded));
    assert!(exchanges.iter().any(|exchange| matches!(&exchange.outcome.response, Some(telltale_machine::model::effects::EffectResponse::NominalCommand { reply }) if reply.result == Ok(telltale_machine::nominal_command::NominalCommandValue::Bool(true)))));
}

#[cfg(all(feature = "multi-thread", not(target_arch = "wasm32")))]
fn identity_background_image() -> telltale_machine::runtime::loader::CodeImage {
    use telltale_machine::instr::Instr;
    use telltale_types::{GlobalType, LocalTypeR};
    let mut image = telltale_machine::runtime::loader::CodeImage::from_local_types(
        &BTreeMap::from([("Background".into(), LocalTypeR::End)]),
        &GlobalType::End,
    );
    image
        .programs
        .insert("Background".into(), vec![Instr::Jump { target: 0 }]);
    image
        .validate_runtime_shape()
        .expect("pure original scheduler loop");
    image
}

#[cfg(all(feature = "multi-thread", not(target_arch = "wasm32")))]
fn assert_identity_dispatch(
    selections: &[telltale_machine::LaneSelection],
    exchanges: &[telltale_machine::model::effects::EffectExchangeRecord],
    original_coro: usize,
    background: Option<telltale_machine::SessionId>,
    callback: std::thread::ThreadId,
    caller: std::thread::ThreadId,
) {
    let nominal: Vec<_> = exchanges
        .iter()
        .filter(|exchange| {
            matches!(&exchange.request.body,
            telltale_machine::model::effects::EffectRequestBody::NominalCommand { request }
            if request.coroutine == original_coro)
        })
        .collect();
    assert_eq!(nominal.len(), 1);
    let actual: Vec<_> = selections
        .iter()
        .filter(|selection| {
            selection.coro_id == original_coro && selection.tick == nominal[0].request.tick
        })
        .collect();
    assert_eq!(actual.len(), 1);
    let selected = actual[0];
    let same_wave: Vec<_> = selections
        .iter()
        .filter(|selection| selection.tick == selected.tick && selection.wave == selected.wave)
        .collect();
    if let Some(background) = background {
        assert_eq!(
            same_wave.len(),
            2,
            "actual two-pick nativepool dispatch precondition"
        );
        assert!(same_wave.iter().any(|other| other.session == background
            && other.session != selected.session
            && other.lane != selected.lane));
        assert_ne!(
            callback, caller,
            "actual provider callback ran on owned native worker"
        );
    } else {
        assert_eq!(same_wave.len(), 1);
        assert_eq!(
            callback, caller,
            "canonical one-pick caller fastpath is intentional"
        );
    }
}

// Real source compiler → owned loader → callback → gated capability consumption.
struct ReadinessReply {
    result: Result<telltale_machine::nominal_command::NominalCommandValue, String>,
    calls: Mutex<Vec<u64>>,
}
impl EffectHandler for ReadinessReply {
    fn handle_send(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        state: &[Value],
    ) -> EffectResult<Value> {
        super::NoopHandler.handle_send(role, partner, label, state)
    }
    fn handle_recv(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        state: &mut Vec<Value>,
        payload: &Value,
    ) -> EffectResult<()> {
        super::NoopHandler.handle_recv(role, partner, label, state, payload)
    }
    fn handle_choose(
        &self,
        role: &str,
        partner: &str,
        labels: &[String],
        state: &[Value],
    ) -> EffectResult<String> {
        super::NoopHandler.handle_choose(role, partner, labels, state)
    }
    fn step(&self, _: &str, _: &mut Vec<Value>) -> EffectResult<()> {
        panic!("readiness cannot dispatch generic step")
    }
    fn handle_nominal_command(
        &self,
        request: &NominalCommandRequest,
    ) -> EffectResult<NominalCommandReply> {
        self.calls
            .lock()
            .expect("actual calls")
            .push(request.invocation);
        EffectResult::success(NominalCommandReply {
            invocation: request.invocation,
            result: self.result.clone(),
        })
    }
}

// Actual registry issuance happens between rounds, without callback reentrancy.
struct PendingReadinessReply {
    original: ReadinessReply,
    witness: Mutex<Vec<telltale_types::ReadinessWitness>>,
}
impl EffectHandler for PendingReadinessReply {
    fn handle_send(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        state: &[Value],
    ) -> EffectResult<Value> {
        self.original.handle_send(role, partner, label, state)
    }
    fn handle_recv(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        state: &mut Vec<Value>,
        payload: &Value,
    ) -> EffectResult<()> {
        self.original
            .handle_recv(role, partner, label, state, payload)
    }
    fn handle_choose(
        &self,
        role: &str,
        partner: &str,
        labels: &[String],
        state: &[Value],
    ) -> EffectResult<String> {
        self.original.handle_choose(role, partner, labels, state)
    }
    fn step(&self, _: &str, _: &mut Vec<Value>) -> EffectResult<()> {
        panic!("readiness cannot dispatch generic step")
    }
    fn handle_nominal_command(
        &self,
        request: &NominalCommandRequest,
    ) -> EffectResult<NominalCommandReply> {
        self.original
            .calls
            .lock()
            .expect("actual callback")
            .push(request.invocation);
        match self
            .witness
            .lock()
            .expect("between-round admission")
            .iter()
            .find(|witness| witness.session_id == request.session)
        {
            None => EffectResult::Blocked,
            Some(witness) => EffectResult::success(NominalCommandReply {
                invocation: request.invocation,
                result: Ok(
                    telltale_machine::nominal_command::NominalCommandValue::Readiness(
                        witness.clone(),
                    ),
                ),
            }),
        }
    }
}

fn readiness_source() -> String {
    SOURCE
        .replace(
            "command ready : Unit -> Result String Bool",
            "authoritative ready : Unit -> Result String ReadinessWitness",
        )
        .replace("class : best_effort", "class : authoritative")
        .replace("let result at A", "authoritative let result at A")
}

macro_rules! readiness_backend_cases {
    ($module:ident, $make:expr, $dispose:expr) => {
        mod $module {
            use super::*;
            use telltale_machine::nominal_command::NominalCommandValue;

            #[test]
            fn actual_blocked_occurrence_resumes_after_between_round_registry_issuance() {
                let image = compile_command_operation(&readiness_source(), "Check", &windows()).expect("source");
                let mut machine = ($make)(ProtocolMachineConfig::default());
                let owner = machine.load_choreography_owned(&image, "original-owner").expect("owner");
                let handler = PendingReadinessReply {
                    original: ReadinessReply { result: Err("unused fallback".into()), calls: Mutex::new(Vec::new()) },
                    witness: Mutex::new(Vec::new()),
                };
                for _ in 0..8 {
                    machine.step_round(&handler, 1).expect("real deterministic round");
                    if !handler.original.calls.lock().expect("calls").is_empty() { break; }
                }
                let calls = handler.original.calls.lock().expect("calls").clone();
                assert_eq!(calls.len(), 1, "actual original callback entered and returned Blocked");
                let occurrence = calls[0];
                assert!(machine.semantic_objects().outstanding_effects.iter().any(|effect|
                    effect.effect_id == occurrence && effect.session == Some(owner.session_id()) &&
                    effect.status == telltale_machine::semantic_objects::OutstandingEffectStatus::Blocked));
                let blocked = machine.semantic_objects().outstanding_effects.into_iter()
                    .find(|effect| effect.effect_id == occurrence).expect("actual blocked original");
                assert_eq!(blocked.completed_at_tick, None, "Blocked is not terminal completion");
                let original_tick = blocked.ordering_key;
                let witness = owner.issue_readiness_witness(&mut machine, "Host.ready").expect("same owner between actual rounds");
                handler.witness.lock().expect("same resident callback result").push(witness.clone());
                let outcome = machine.run(&handler, 64);
                let calls = handler.original.calls.lock().expect("calls").clone();
                let consumed = owner.consume_readiness_witness(&mut machine, &witness);
                let request_ticks: Vec<_> = machine.effect_exchanges().iter().filter_map(|exchange| {
                    if matches!(&exchange.request.body, telltale_machine::model::effects::EffectRequestBody::NominalCommand { request } if request.invocation == occurrence) {
                        Some(exchange.request.tick)
                    } else { None }
                }).collect();
                let settled = machine.semantic_objects().outstanding_effects.into_iter()
                    .find(|effect| effect.effect_id == occurrence).expect("same settled original");
                let completion = settled.completed_at_tick;
                let ordering = settled.ordering_key;
                ($dispose)(machine);
                assert_eq!(outcome.expect("same original continuation"), telltale_machine::RunStatus::AllDone);
                assert_eq!(calls, vec![occurrence, occurrence]);
                assert_eq!(request_ticks.len(), 2);
                assert_eq!(request_ticks[0], request_ticks[1], "retry retains original admitted tick");
                assert_eq!(ordering, original_tick);
                assert_eq!(request_ticks[0], original_tick);
                assert!(completion.is_some_and(|tick| tick > original_tick), "actual later completion remains distinct from original admission");
                assert!(matches!(consumed, Err(telltale_machine::OwnershipError::WitnessConsumed { .. })));
            }

            #[test]
            fn original_registry_witness_commits_once_after_rollback() {
                let image = compile_command_operation(&readiness_source(), "Check", &windows())
                    .expect("actual authoritative source");
                let mut machine = ($make)(ProtocolMachineConfig::default());
                let owner = machine
                    .load_choreography_owned(&image, "readiness-owner")
                    .expect("issued owner");
                let witness = owner
                    .issue_readiness_witness(&mut machine, "Host.ready")
                    .expect("actual registry issuance");
                let transfer = owner
                    .begin_transfer(
                        &mut machine,
                        "next-owner",
                        telltale_machine::OwnershipScope::Session,
                    )
                    .expect("staged actual transfer");
                owner
                    .rollback_transfer(&mut machine, &transfer)
                    .expect("same original rollback");
                let handler = ReadinessReply {
                    result: Ok(NominalCommandValue::Readiness(witness.clone())),
                    calls: Mutex::new(Vec::new()),
                };
                let outcome = machine.run(&handler, 64);
                // Capture resource-free observations while the original machine is resident.
                let (original_roles_present, all_done, original_witness_stored) = {
                    let coroutines = machine.session_coroutines(owner.session_id());
                    let mut roles: Vec<_> = coroutines.iter().map(|coro| coro.role.as_str()).collect();
                    roles.sort_unstable();
                    let expected: Vec<_> = image.programs.keys().map(String::as_str).collect();
                    (
                        !expected.is_empty() && roles == expected,
                        coroutines.iter().all(|coro| coro.status == telltale_machine::CoroStatus::Done),
                        coroutines.iter().any(|coro| coro.role == "A" &&
                            matches!(&coro.regs[2], Value::Readiness(stored) if stored == &witness)),
                    )
                };
                let consumed = owner.consume_readiness_witness(&mut machine, &witness);
                let calls = handler.calls.lock().expect("calls").clone();
                ($dispose)(machine);
                assert_eq!(
                    outcome.expect("actual command"),
                    telltale_machine::RunStatus::AllDone
                );
                assert!(original_roles_present);
                assert!(all_done);
                assert!(original_witness_stored);
                assert!(matches!(
                    consumed,
                    Err(telltale_machine::OwnershipError::WitnessConsumed { .. })
                ));
                assert_eq!(calls.len(), 1);
            }

            #[test]
            fn readiness_refuses_boolean_forged_wrong_predicate_and_consumed_results() {
                for case in 0..4 {
                    let image = compile_command_operation(&readiness_source(), "Check", &windows())
                        .expect("authoritative source");
                    let mut machine = ($make)(ProtocolMachineConfig::default());
                    let owner = machine
                        .load_choreography_owned(&image, "readiness-owner")
                        .expect("owner");
                    let mut witness = owner
                        .issue_readiness_witness(&mut machine, "Host.ready")
                        .expect("issuer");
                    let value = match case {
                        0 => NominalCommandValue::Bool(true),
                        1 => {
                            witness.witness_id += 1;
                            NominalCommandValue::Readiness(witness.clone())
                        }
                        2 => {
                            witness.predicate_ref = "Other.ready".into();
                            NominalCommandValue::Readiness(witness.clone())
                        }
                        _ => {
                            owner
                                .consume_readiness_witness(&mut machine, &witness)
                                .expect("prior actual consume");
                            NominalCommandValue::Readiness(witness.clone())
                        }
                    };
                    let handler = ReadinessReply {
                        result: Ok(value),
                        calls: Mutex::new(Vec::new()),
                    };
                    let outcome = machine.run(&handler, 64);
                    let original_registers_unchanged = machine.session_coroutines(owner.session_id())
                        .iter().filter(|coro| coro.role == "A").map(|coro| &coro.regs[2])
                        .eq(std::iter::once(&Value::Unit));
                    ($dispose)(machine);
                    assert!(outcome.is_err(), "case {case}");
                    assert!(original_registers_unchanged);
                    assert_eq!(handler.calls.lock().expect("calls").len(), 1);
                }
            }

            #[test]
            fn foreign_session_and_committed_transfer_cannot_reuse_readiness() {
                for transfer_case in [false, true] {
                    let image = compile_command_operation(&readiness_source(), "Check", &windows())
                        .expect("source");
                    let mut machine = ($make)(ProtocolMachineConfig::default());
                    let owner = machine
                        .load_choreography_owned(&image, "original-owner")
                        .expect("owner");
                    let witness = if transfer_case {
                        let witness = owner
                            .issue_readiness_witness(&mut machine, "Host.ready")
                            .expect("original issuer");
                        let receipt = owner
                            .begin_transfer(
                                &mut machine,
                                "next-owner",
                                telltale_machine::OwnershipScope::Session,
                            )
                            .expect("actual transfer");
                        let next = owner
                            .commit_transfer(&mut machine, &receipt)
                            .expect("actual new owner");
                        assert!(next
                            .consume_readiness_witness(&mut machine, &witness)
                            .is_err());
                        let fresh = next
                            .issue_readiness_witness(&mut machine, "Host.ready")
                            .expect("new original issuer");
                        next.consume_readiness_witness(&mut machine, &fresh)
                            .expect("same new owner consumes fresh evidence");
                        witness
                    } else {
                        let foreign = machine
                            .load_choreography_owned(&image, "foreign-owner")
                            .expect("different original session");
                        foreign
                            .issue_readiness_witness(&mut machine, "Host.ready")
                            .expect("genuine foreign issuance")
                    };
                    let handler = ReadinessReply {
                        result: Ok(NominalCommandValue::Readiness(witness)),
                        calls: Mutex::new(Vec::new()),
                    };
                    let outcome = machine.run(&handler, 64);
                    let original_registers_unchanged = machine.session_coroutines(owner.session_id())
                        .iter().filter(|coro| coro.role == "A").map(|coro| &coro.regs[2])
                        .eq(std::iter::once(&Value::Unit));
                    let calls = handler.calls.lock().expect("calls").len();
                    ($dispose)(machine);
                    assert!(outcome.is_err());
                    assert!(original_registers_unchanged);
                    assert_eq!(calls, usize::from(!transfer_case));
                }
            }

            #[test]
            fn cross_session_readiness_commit_and_rejection_reach_canonical_audit_exports() {
                use telltale_machine::{AuthorityArtifact, AuthorityAuditEvent};
                use telltale_machine::SemanticAuditRecord;
                let image = compile_command_operation(&readiness_source(), "Check", &windows()).expect("source");
                let mut machine = ($make)(ProtocolMachineConfig::default());
                let first = machine.load_choreography_owned(&image, "first-owner").expect("first owner");
                let second = machine.load_choreography_owned(&image, "second-owner").expect("second owner");
                let first_witness = first.issue_readiness_witness(&mut machine, "Host.ready").expect("first genuine issuance initializes audit owner");
                let second_witness = second.issue_readiness_witness(&mut machine, "Host.ready").expect("second genuine issuance");
                let handler = PendingReadinessReply {
                    original: ReadinessReply { result: Err("unused fallback".into()), calls: Mutex::new(Vec::new()) },
                    // Callback data only: canonical session registries remain sole authority.
                    witness: Mutex::new(vec![first_witness.clone(), second_witness.clone()]),
                };
                let outcome = machine.run(&handler, 64);
                let repeated = first.consume_readiness_witness(&mut machine, &first_witness);
                let records: Vec<_> = machine.semantic_audit_log().into_iter().filter_map(|record| match record {
                    SemanticAuditRecord::Authority { tick, artifact: AuthorityArtifact::Readiness(witness), event, reason, .. } => Some((tick, witness, event, reason)),
                    _ => None,
                }).collect();
                let reads = machine.semantic_objects().authoritative_reads;
                let callbacks = handler.original.calls.lock().expect("actual callbacks").len();
                ($dispose)(machine);
                assert_eq!(outcome.expect("actual two-session transaction"), telltale_machine::RunStatus::AllDone);
                assert!(matches!(repeated, Err(telltale_machine::OwnershipError::WitnessConsumed { .. })));
                assert_eq!(callbacks, 2);
                assert_eq!(records.len(), 5, "initialized canonical journal must retain both commit consumers and rejection");
                assert_eq!(records.iter().map(|record| record.2).collect::<Vec<_>>(), vec![AuthorityAuditEvent::Issued, AuthorityAuditEvent::Issued, AuthorityAuditEvent::Consumed, AuthorityAuditEvent::Consumed, AuthorityAuditEvent::Rejected]);
                assert!(records.iter().all(|record| record.0.is_some()), "actual selected machine tick on every producer");
                assert_eq!(records[0].1, first_witness);
                assert_eq!(records[1].1, second_witness);
                assert_eq!(records[4].1, first_witness);
                assert!(records.windows(2).all(|pair| pair[0].0 <= pair[1].0));
                for witness in [first_witness, second_witness] {
                    assert!(records[2..4].iter().any(|record| record.1 == witness));
                    assert!(reads.iter().any(|read| read.session == Some(witness.session_id) &&
                        read.witness_id == Some(witness.witness_id) && read.owner_id.as_deref() == Some(witness.owner_id.as_str()) &&
                        read.lifecycle == telltale_machine::semantic_objects::AuthoritativeReadLifecycle::Consumed));
                }
            }

            #[test]
            fn output_refusal_retains_actual_witness_unconsumed() {
                let image = compile_command_operation(&readiness_source(), "Check", &windows())
                    .expect("source");
                let mut config = ProtocolMachineConfig::default();
                config.output_condition_policy =
                    telltale_machine::model::output_condition::OutputConditionPolicy::DenyAll;
                let mut machine = ($make)(config);
                let owner = machine
                    .load_choreography_owned(&image, "readiness-owner")
                    .expect("owner");
                let witness = owner
                    .issue_readiness_witness(&mut machine, "Host.ready")
                    .expect("issuer");
                let handler = ReadinessReply {
                    result: Ok(NominalCommandValue::Readiness(witness.clone())),
                    calls: Mutex::new(Vec::new()),
                };
                let outcome = machine.run(&handler, 64);
                let calls = handler.calls.lock().expect("calls").clone();
                let still_issued = owner.consume_readiness_witness(&mut machine, &witness);
                ($dispose)(machine);
                assert!(outcome.is_err());
                assert_eq!(
                    calls.len(),
                    1,
                    "actual callback happened before selected output refusal"
                );
                assert!(
                    still_issued.is_ok(),
                    "gate refusal cannot consume readiness authority"
                );
            }
        }
    };
}

readiness_backend_cases!(
    readiness_cooperative,
    ProtocolMachine::new,
    |_: ProtocolMachine| {}
);
#[cfg(all(feature = "multi-thread", not(target_arch = "wasm32")))]
readiness_backend_cases!(
    readiness_threaded,
    |config| telltale_machine::ThreadedProtocolMachine::with_workers(config, 1),
    |machine: telltale_machine::ThreadedProtocolMachine| {
        let disposal = machine
            .shutdown_worker_pool()
            .expect("same actual workers joined");
        assert_eq!(disposal.joined_workers(), 1);
    }
);
