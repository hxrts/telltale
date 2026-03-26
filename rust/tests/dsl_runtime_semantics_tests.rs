#![allow(clippy::expect_used)]

//! End-to-end DSL-to-runtime semantic conformance tests.

use std::collections::BTreeMap;

use telltale::tell;
use telltale_language::ast::convert::{choreography_to_global, local_to_local_r};
use telltale_language::compiler::parser::parse_choreography_file;
use telltale_machine::coroutine::Value;
use telltale_machine::model::effects::{
    EffectFailure, EffectHandler, EffectResult, SendDecision, SendDecisionInput,
};
use telltale_machine::runtime::loader::CodeImage;
use telltale_machine::{ProgressState, ProtocolMachine, ProtocolMachineConfig};
use tempfile::NamedTempFile;

const SIMPLE_DSL: &str = r#"
    protocol PingPong =
        roles A, B

        A -> B : Ping
        B -> A : Pong
"#;

const COMMITMENT_DSL: &str = r#"
profile Replay fairness eventual admissibility replay escalation_window bounded
agreement_profile SoftSafe
  visibility pending
  rule aura_soft_safe
  usable_at soft_safe
  finalized_at finalized
  evidence commit_fact

operation syncLedger(entryId : Int) at Coordinator progress LedgerProgress requires Replay within bounded on timeout => escalate on stall => diagnose agreement SoftSafe prestate LedgerState compose first_success =
  publish SyncQueued(entryId)

protocol CommitLifecycle under Replay =
  roles Coordinator, Worker
  begin syncLedger(42) progress LedgerProgress requires Replay within bounded on timeout => escalate on stall => diagnose
  Coordinator -> Worker : Prepare
  await syncLedger
  resolve syncLedger as Success
"#;

const AUTHORITY_DSL: &str = r#"
effect Runtime
  authoritative ready : Session -> Result ReadyErr ReadyWitness
  {
    class : authoritative
    progress : may_block
    region : fragment
    agreement_use : required
    reentrancy : reject_same_fragment
  }
  observe watchPresence : Session -> PresenceView
  {
    class : observational
    progress : immediate
    region : session
    agreement_use : forbidden
    reentrancy : allow
  }

type ReadyErr =
  | NotReady

type alias ReadyWitness =
{
  epoch : Int
  issuedBy : Role
}

protocol AuthorityFlow uses Runtime =
  roles Coordinator, Worker
  observe let presence = observe Runtime.watchPresence(commitSession)
  authoritative let witness = check Runtime.ready(commitSession)
  publish witness as AcceptedPublication
  materialize acceptedProof from AcceptedPublication
  let receipt = transfer Session from Coordinator to Worker
  handoff acceptInvite to Worker with receipt
  Coordinator -> Worker : Commit
"#;

tell! {
    profile Replay fairness eventual admissibility replay escalation_window bounded
    agreement_profile SoftSafe
      visibility pending
      rule aura_soft_safe
      usable_at soft_safe
      finalized_at finalized
      evidence commit_fact

    operation syncLedger(entryId : Int) at Coordinator progress LedgerProgress requires Replay within bounded on timeout => escalate on stall => diagnose agreement SoftSafe prestate LedgerState compose first_success =
      publish SyncQueued(entryId)

    protocol MacroCommitLifecycle under Replay =
      roles Coordinator, Worker
      begin syncLedger(42) progress LedgerProgress requires Replay within bounded on timeout => escalate on stall => diagnose
      Coordinator -> Worker : Prepare
      await syncLedger
      resolve syncLedger as Success
}

tell! {
    effect Runtime
      authoritative ready : Session -> Result ReadyErr ReadyWitness
      {
        class : authoritative
        progress : may_block
        region : fragment
        agreement_use : required
        reentrancy : reject_same_fragment
      }
      observe watchPresence : Session -> PresenceView
      {
        class : observational
        progress : immediate
        region : session
        agreement_use : forbidden
        reentrancy : allow
      }

    type ReadyErr =
      | NotReady

    type alias ReadyWitness =
    {
      epoch : Int
      issuedBy : Role
    }

    protocol MacroAuthorityFlow uses Runtime =
      roles Coordinator, Worker
      observe let presence = observe Runtime.watchPresence(commitSession)
      authoritative let witness = check Runtime.ready(commitSession)
      publish witness as AcceptedPublication
      materialize acceptedProof from AcceptedPublication
      let receipt = transfer Session from Coordinator to Worker
      handoff acceptInvite to Worker with receipt
      Coordinator -> Worker : Commit
}

#[derive(Debug, Clone, Copy)]
struct NoopHandler;

impl EffectHandler for NoopHandler {
    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &[Value],
    ) -> EffectResult<Value> {
        EffectResult::success(Value::Unit)
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
        match labels.first().cloned() {
            Some(label) => EffectResult::success(label),
            None => EffectResult::failure(EffectFailure::invalid_input("no labels available")),
        }
    }

    fn step(&self, _role: &str, _state: &mut Vec<Value>) -> EffectResult<()> {
        EffectResult::success(())
    }
}

fn code_image_from_dsl(input: &str) -> CodeImage {
    let choreography = telltale_language::parse_choreography_str(input).expect("parse DSL");
    code_image_from_choreography(&choreography)
}

fn code_image_from_choreography(choreography: &telltale_language::ast::Choreography) -> CodeImage {
    let global = choreography_to_global(choreography).expect("convert choreography to global");
    let mut locals = BTreeMap::new();
    for role in &choreography.roles {
        let local = telltale_language::project(choreography, role).expect("project local type");
        let local_r = local_to_local_r(&local).expect("convert local type");
        locals.insert(role.name().to_string(), local_r);
    }
    CodeImage::from_local_types(&locals, &global)
}

#[test]
fn supported_dsl_surface_lowers_to_runtime_semantic_objects() {
    let image = code_image_from_dsl(SIMPLE_DSL);
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    machine.load_choreography(&image).expect("load image");
    machine.run(&NoopHandler, 64).expect("run protocol machine");

    let semantic_objects = machine.semantic_objects();
    assert!(
        semantic_objects.parity_critical_operations_have_progress_contracts(),
        "lowered DSL surface should preserve parity-critical progress contracts"
    );
    assert!(
        semantic_objects
            .publication_events
            .iter()
            .any(|publication| publication.publication == "effect.succeeded"),
        "lowered DSL run should emit canonical effect publications"
    );
    assert!(
        semantic_objects
            .progress_contracts
            .iter()
            .any(|contract| contract.state == ProgressState::Succeeded),
        "lowered DSL run should surface successful progress contracts"
    );
}

#[test]
fn supported_tell_file_surface_lowers_to_runtime_semantic_objects() {
    let mut file = NamedTempFile::with_suffix(".tell").expect("create .tell fixture");
    std::io::Write::write_all(&mut file, SIMPLE_DSL.as_bytes()).expect("write .tell fixture");

    let choreography = parse_choreography_file(file.path()).expect("parse .tell file");
    let image = code_image_from_choreography(&choreography);

    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    machine.load_choreography(&image).expect("load image");
    machine.run(&NoopHandler, 64).expect("run protocol machine");

    let semantic_objects = machine.semantic_objects();
    assert!(
        semantic_objects.parity_critical_operations_have_progress_contracts(),
        ".tell file surface should preserve parity-critical progress contracts"
    );
    assert!(
        semantic_objects
            .publication_events
            .iter()
            .any(|publication| publication.publication == "effect.succeeded"),
        ".tell file surface should emit canonical effect publications"
    );
}

#[test]
fn generated_commitment_metadata_matches_declared_semantic_contracts() {
    let choreography =
        telltale_language::parse_choreography_str(COMMITMENT_DSL).expect("parse DSL");
    choreography
        .validate()
        .expect("validate commitment surface");

    let operation = &choreography.operation_declarations()[0];
    let progress = operation
        .progress_contract
        .as_ref()
        .expect("operation should carry explicit progress metadata");
    let agreement = operation
        .agreement
        .as_ref()
        .expect("operation should carry named agreement metadata");

    let metadata = MacroCommitLifecycle::commitments::operation("syncLedger")
        .expect("macro commitment metadata");
    let operation_instance = metadata.operation_instance("syncLedger#1");
    let progress_contract = metadata.progress_contract("syncLedger#1");
    let agreement_metadata = MacroCommitLifecycle::agreements::operation("syncLedger")
        .expect("macro agreement metadata");
    let agreement_contract = agreement_metadata.agreement_contract("syncLedger#1");
    let prestate_binding = agreement_metadata
        .prestate_binding("syncLedger#1", "digest:ledger")
        .expect("prestate binding");
    let agreement_profile =
        MacroCommitLifecycle::agreements::profile("SoftSafe").expect("macro agreement profile");

    assert_eq!(metadata.operation_name, operation.name);
    assert_eq!(metadata.owner_role, operation.owner_role);
    assert_eq!(metadata.progress.contract_name, progress.contract_name);
    assert_eq!(
        metadata.progress.requires_profile,
        progress.requires_profile.as_deref()
    );
    assert_eq!(
        metadata.progress.within_window,
        progress.within_window.as_deref()
    );
    assert_eq!(metadata.progress.on_timeout, progress.on_timeout.as_deref());
    assert_eq!(metadata.progress.on_stall, progress.on_stall.as_deref());
    assert_eq!(operation_instance.kind, operation.name);
    assert!(operation_instance.requires_proof);
    assert!(progress_contract.bounded);
    assert_eq!(agreement_metadata.profile_name, agreement.profile_name);
    assert_eq!(agreement_metadata.prestate, agreement.prestate.as_deref());
    assert_eq!(agreement_contract.profile_name.as_deref(), Some("SoftSafe"));
    assert_eq!(prestate_binding.binding_id, "prestate:syncLedger#1");
    assert_eq!(prestate_binding.epoch_ref.as_deref(), Some("LedgerState"));
    assert_eq!(agreement_profile.profile_name, "SoftSafe");
    assert_eq!(
        MacroCommitLifecycle::proof_status::AGREEMENT_PROFILE_NAMES,
        ["SoftSafe"]
    );
    assert_eq!(
        MacroCommitLifecycle::proof_status::EXECUTION_PROFILES,
        ["Replay"]
    );
    const _: () = assert!(MacroCommitLifecycle::proof_status::PROTOCOL_MACHINE_EXECUTABLE);
    const _: () = assert!(!MacroCommitLifecycle::proof_status::SESSION_PROJECTABLE);
}

#[test]
fn generated_authority_metadata_matches_semantic_object_shapes() {
    let choreography = telltale_language::parse_choreography_str(AUTHORITY_DSL).expect("parse DSL");
    choreography.validate().expect("validate authority surface");

    let effect_metadata = choreography.effect_contract_declarations();
    assert!(effect_metadata.iter().any(|op| {
        op.interface_name == "Runtime"
            && op.operation_name == "ready"
            && op.semantic_class == "authoritative"
    }));
    assert!(effect_metadata.iter().any(|op| {
        op.interface_name == "Runtime"
            && op.operation_name == "watchPresence"
            && op.semantic_class == "observational"
    }));

    let authoritative =
        MacroAuthorityFlow::authority::authoritative_binding("witness").expect("auth binding");
    let observed =
        MacroAuthorityFlow::authority::observed_binding("presence").expect("observed binding");
    let publication =
        MacroAuthorityFlow::authority::publication("AcceptedPublication").expect("publication");
    let materialization =
        MacroAuthorityFlow::authority::materialization("acceptedProof").expect("materialization");
    let handoff = MacroAuthorityFlow::authority::handoff("acceptInvite").expect("semantic handoff");

    let authoritative_read = authoritative.authoritative_read("read#1");
    let observed_read = observed.observed_read("observe#1", 7, "handler");
    let publication_event = publication.publication_event("publication#1", "acceptInvite");
    let materialization_proof =
        materialization.materialization_proof("proof#1", "Runtime.ready", "digest:ready");
    let canonical_handle = materialization.canonical_handle("handle#1", &materialization_proof);
    let semantic_handoff = handoff.semantic_handoff(9, 1, 0, 1);

    assert_eq!(authoritative.effect_interface, "Runtime");
    assert_eq!(authoritative.effect_operation, "ready");
    assert_eq!(
        authoritative_read.predicate_ref.as_deref(),
        Some("Runtime.ready")
    );
    assert_eq!(observed.effect_interface, "Runtime");
    assert_eq!(observed.effect_operation, "watchPresence");
    assert_eq!(observed_read.effect_id, 7);
    assert_eq!(publication_event.publication, "AcceptedPublication");
    assert_eq!(
        materialization_proof.witness_ref.as_deref(),
        Some("AcceptedPublication")
    );
    assert_eq!(canonical_handle.proof_ref.as_deref(), Some("proof#1"));
    assert_eq!(handoff.target_role, "Worker");
    assert_eq!(semantic_handoff.activated_owner_id, "Worker");
    const _: () = assert!(!MacroAuthorityFlow::proof_status::SESSION_PROJECTABLE);
    const _: () = assert!(MacroAuthorityFlow::proof_status::PROTOCOL_MACHINE_EXECUTABLE);
}

#[test]
fn unsupported_commitment_lifecycle_surface_fails_closed_before_theory_lowering() {
    let input = r#"
        protocol CommitLifecycle =
            roles Coordinator, Worker

            begin syncLedger(42)
            Coordinator -> Worker : Prepare
            await syncLedger
            resolve syncLedger as Success
    "#;

    let choreography = telltale_language::parse_choreography_str(input).expect("parse DSL");
    let err = choreography_to_global(&choreography)
        .expect_err("unsupported lifecycle lowering must fail");
    assert!(
        err.to_string().contains("CommitmentLifecycle"),
        "expected explicit fail-closed lowering error, got {err}"
    );
}

#[test]
fn implicit_authoritative_binding_fails_closed() {
    let input = r#"
effect Runtime
  authoritative ready : Session -> Result ReadyErr ReadyWitness
  {
    class : authoritative
    progress : may_block
    region : fragment
    agreement_use : required
    reentrancy : reject_same_fragment
  }

protocol CommitFlow uses Runtime =
  roles Coordinator, Worker
  let readiness = check Runtime.ready(session)
  Coordinator -> Worker : Continue(readiness)
"#;

    let choreography = telltale_language::parse_choreography_str(input).expect("parse DSL");
    let err = choreography
        .validate()
        .expect_err("implicit authoritative binding must fail closed");
    assert!(err.to_string().contains("authoritative let"));
}

#[test]
fn legacy_child_effect_composition_keywords_fail_closed() {
    for keyword in ["race", "fallback", "quorum(2)"] {
        let input = format!(
            r#"
agreement_profile SoftSafe
  visibility pending
  rule aura_soft_safe
  usable_at soft_safe
  finalized_at finalized
  evidence commit_fact

profile Replay fairness eventual admissibility replay escalation_window bounded

operation syncLedger(entryId : Int) at Coordinator progress LedgerProgress requires Replay within bounded on timeout => escalate on stall => diagnose agreement SoftSafe prestate LedgerState compose {keyword} =
  publish SyncQueued(entryId)

protocol CommitLifecycle under Replay =
  roles Coordinator, Worker
  begin syncLedger(42) progress LedgerProgress requires Replay within bounded on timeout => escalate on stall => diagnose
  Coordinator -> Worker : Prepare
"#
        );

        let err =
            telltale_language::parse_choreography_str(&input).expect_err("legacy compose keyword");
        let message = err.to_string();
        assert!(
            message.contains("all_success")
                || message.contains("first_success")
                || message.contains("threshold_success"),
            "unexpected parser error for `{keyword}`: {message}"
        );
    }
}

#[test]
fn structure_surface_remains_fail_closed_in_projection() {
    let choreography = telltale_language::parse_choreography_str(AUTHORITY_DSL).expect("parse DSL");
    assert!(
        choreography
            .language_tier_status()
            .protocol_machine_executable
    );
    assert!(!choreography.language_tier_status().session_projectable);

    let err = telltale_language::project(&choreography, &choreography.roles[0])
        .expect_err("authority/structure surface must remain fail-closed in projection");
    assert!(!err.to_string().is_empty());
}
