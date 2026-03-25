#![cfg(not(target_arch = "wasm32"))]
#![allow(missing_docs)]

#[allow(dead_code, unreachable_pub)]
#[path = "support/mod.rs"]
mod test_support;

use std::collections::{BTreeMap, BTreeSet};

use cfg_if::cfg_if;
use telltale_machine::coroutine::Value;
use telltale_machine::instr::{ImmValue, Instr};
use telltale_machine::model::effects::{
    EffectFailure, EffectHandler, EffectResult, SendDecision, SendDecisionInput,
};
use telltale_machine::runtime::loader::CodeImage;
use telltale_machine::ObsEvent;
use telltale_machine::{
    protocol_machine_semantic_objects, run_loaded_protocol_machine_record_replay_conformance,
    AuthoritativeReadKind, CanonicalHandleKind, DelegationStatus, Edge, OperationInstance,
    OperationPhase, OwnershipError, OwnershipScope, ProgressState, ProtocolMachine,
    ProtocolMachineConfig, PublicationStatus, SemanticAuditRecord, SessionHostMutation,
};
use telltale_types::{GlobalType, LocalTypeR, ValType};
use test_support::simple_send_recv_image;

cfg_if! {
    if #[cfg(feature = "multi-thread")] {
        use telltale_machine::ThreadedGuestRuntime;
    }
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

fn transfer_image() -> CodeImage {
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

#[test]
fn ownership_owned_session_transfer_invalidates_stale_handles() {
    let image = simple_send_recv_image("A", "B", "m");
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    let owned = machine
        .load_choreography_owned(&image, "runtime/owner")
        .expect("owned open should succeed");
    let receipt = owned
        .begin_transfer(
            &mut machine,
            "runtime/owner",
            OwnershipScope::Fragments(BTreeSet::from(["A".to_string()])),
        )
        .expect("transfer staging should succeed");
    let narrowed = owned
        .commit_transfer(&mut machine, &receipt)
        .expect("transfer commit should succeed");
    let edge = Edge::new(owned.session_id(), "A", "B");

    let stale = owned
        .apply_host_mutation(
            &mut machine,
            SessionHostMutation::UpdateTrace {
                edge: edge.clone(),
                trace: vec![ValType::Nat],
            },
        )
        .expect_err("stale owner must be rejected");
    assert!(matches!(
        stale,
        OwnershipError::StaleCapability {
            owner_id,
            expected_generation: 0,
            actual_generation: 1,
            ..
        } if owner_id == "runtime/owner"
    ));

    let scope = narrowed
        .apply_host_mutation(
            &mut machine,
            SessionHostMutation::UpdateTrace {
                edge,
                trace: vec![ValType::Bool],
            },
        )
        .expect_err("fragment-scoped owner must not mutate session-local host state");
    assert!(matches!(
        scope,
        OwnershipError::ScopeViolation {
            required: OwnershipScope::Session,
            actual: OwnershipScope::Fragments(_),
            ..
        }
    ));
}

#[test]
fn ownership_transfer_record_replay_preserves_observable_handoff() {
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    machine
        .load_choreography(&transfer_image())
        .expect("load transfer fixture");

    let report =
        run_loaded_protocol_machine_record_replay_conformance(&mut machine, &NoopHandler, 32)
            .expect("record/replay harness should succeed");

    assert!(report.replay_consistent);
    assert!(report.exact_trace_match);
    assert!(
        machine.trace()
            .iter()
            .any(|event| matches!(event, ObsEvent::Transferred { role, from, to, .. } if role == "A" && from == &0 && to == &1)),
        "transfer fixture must emit an observable handoff"
    );
    let audit = machine
        .delegation_audit_log()
        .last()
        .expect("transfer fixture should emit a delegation audit");
    assert_eq!(audit.status, DelegationStatus::Committed);
    assert_eq!(
        audit.receipt.scope,
        OwnershipScope::Fragments(BTreeSet::from(["A".to_string()]))
    );
    assert!(
        machine.semantic_audit_log().iter().any(|record| matches!(
            record,
            SemanticAuditRecord::Delegation { status, .. } if *status == DelegationStatus::Committed
        )),
        "semantic audit surface should retain committed delegation records"
    );
    assert!(
        machine.semantic_audit_log().iter().any(|record| matches!(
            record,
            SemanticAuditRecord::TransformationObligation { obligation, .. }
                if obligation.handoff_id == audit.receipt.receipt_id
                    && obligation.publication_revoked_from == "coro:0"
                    && obligation.publication_activated_to == "coro:1"
        )),
        "semantic audit surface should retain handoff obligation bundles"
    );
    let semantic_objects = machine.semantic_objects();
    assert!(
        semantic_objects
            .semantic_handoffs
            .iter()
            .any(|handoff| handoff.handoff_id == audit.receipt.receipt_id),
        "canonical semantic object surface should retain semantic handoffs"
    );
    assert!(
        semantic_objects
            .semantic_handoffs
            .iter()
            .any(|handoff| handoff.revoked_owner_id == "coro:0"
                && handoff.activated_owner_id == "coro:1"),
        "semantic handoff should make owner revocation/activation explicit"
    );
    assert!(
        semantic_objects
            .transformation_obligations
            .iter()
            .any(
                |obligation| obligation.handoff_id == audit.receipt.receipt_id
                    && obligation.transformed_fragments == vec!["A".to_string()]
            ),
        "canonical semantic object surface should retain transformation-local obligations"
    );
    assert!(
        semantic_objects
            .canonical_handles
            .iter()
            .any(|handle| matches!(handle.kind, CanonicalHandleKind::Handoff)),
        "committed handoff should produce a canonical handle"
    );
    assert!(
        semantic_objects
            .progress_contracts
            .iter()
            .any(|contract| matches!(contract.state, ProgressState::HandedOff)),
        "handoff should surface a progress contract state"
    );
}

#[test]
fn ownership_semantic_objects_expose_authoritative_reads() {
    let image = simple_send_recv_image("A", "B", "m");
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    let owned = machine
        .load_choreography_owned(&image, "runtime/owner")
        .expect("owned open should succeed");

    let witness = owned
        .issue_readiness_witness(&mut machine, "session.ready")
        .expect("issue readiness witness");
    owned
        .consume_readiness_witness(&mut machine, &witness)
        .expect("consume readiness witness");

    let semantic_objects = machine.semantic_objects();
    assert!(
        semantic_objects
            .authoritative_reads
            .iter()
            .any(|read| matches!(read.kind, AuthoritativeReadKind::Readiness)),
        "semantic objects should expose readiness witnesses as authoritative reads"
    );
}

#[test]
fn ownership_observed_reads_are_rejected_on_semantic_paths() {
    let image = simple_send_recv_image("A", "B", "m");
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    machine.load_choreography(&image).expect("load image");
    machine.run(&NoopHandler, 32).expect("run image");

    let observed = machine
        .semantic_objects()
        .observed_reads
        .first()
        .cloned()
        .expect("runtime should surface at least one observed read");
    let err = machine
        .require_authoritative_read(&observed.read_id)
        .expect_err("observational reads must be rejected on semantic paths");
    assert!(err.to_string().contains("observed read"));
}

#[test]
fn ownership_proof_bearing_success_is_enforced_for_publication() {
    let objects = protocol_machine_semantic_objects(
        &[],
        &[],
        &[OperationInstance {
            operation_id: "accept:1".to_string(),
            session: Some(1),
            owner_id: Some("runtime/owner".to_string()),
            kind: "acceptInvite".to_string(),
            phase: OperationPhase::Succeeded,
            handler_identity: Some("host/runtime".to_string()),
            effect_ids: Vec::new(),
            dependent_operation_ids: Vec::new(),
            terminal_publication: Some("accept.succeeded".to_string()),
            budget_ticks: Some(1),
            requires_proof: true,
        }],
        &[],
        &[],
        &[],
        &[],
    );
    let publication = objects
        .publication_events
        .iter()
        .find(|event| event.operation_id == "accept:1")
        .expect("publication event");
    assert_eq!(publication.status, PublicationStatus::Rejected);
    assert_eq!(
        publication.reason.as_deref(),
        Some("proof-bearing success required")
    );
}

#[test]
fn ownership_canonical_handle_is_required_on_parity_critical_paths() {
    let image = simple_send_recv_image("A", "B", "m");
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    machine.load_choreography(&image).expect("load image");
    machine.run(&NoopHandler, 32).expect("run image");

    let semantic_objects = machine.semantic_objects();
    let handle = semantic_objects
        .canonical_handles
        .first()
        .expect("successful output-condition checks should yield a canonical handle");
    let bound = machine
        .require_canonical_handle(&handle.handle_id)
        .expect("existing canonical handle must bind");
    assert_eq!(bound.handle_id, handle.handle_id);

    let err = machine
        .require_canonical_handle("materialization:missing")
        .expect_err("missing canonical handles must be rejected");
    assert!(err.to_string().contains("canonical handle"));
}

#[test]
fn ownership_publication_path_is_canonical_and_unique() {
    let objects = protocol_machine_semantic_objects(
        &[],
        &[],
        &[
            OperationInstance {
                operation_id: "effect:1".to_string(),
                session: Some(1),
                owner_id: Some("runtime/owner".to_string()),
                kind: "readChannel".to_string(),
                phase: OperationPhase::Succeeded,
                handler_identity: Some("host/runtime".to_string()),
                effect_ids: Vec::new(),
                dependent_operation_ids: Vec::new(),
                terminal_publication: Some("effect.succeeded".to_string()),
                budget_ticks: Some(1),
                requires_proof: false,
            },
            OperationInstance {
                operation_id: "effect:1".to_string(),
                session: Some(1),
                owner_id: Some("runtime/owner".to_string()),
                kind: "readChannel".to_string(),
                phase: OperationPhase::Succeeded,
                handler_identity: Some("host/runtime".to_string()),
                effect_ids: Vec::new(),
                dependent_operation_ids: Vec::new(),
                terminal_publication: Some("effect.succeeded".to_string()),
                budget_ticks: Some(1),
                requires_proof: false,
            },
        ],
        &[],
        &[],
        &[],
        &[],
    );
    assert_eq!(
        objects.publication_events.len(),
        1,
        "duplicate publication roots must collapse into one canonical publication event"
    );
}

cfg_if! {
    if #[cfg(feature = "multi-thread")] {
        #[test]
        fn threaded_owned_open_claims_host_authority() {
            let image = simple_send_recv_image("A", "B", "m");
            let mut threaded = ThreadedGuestRuntime::with_workers(ProtocolMachineConfig::default(), 2);
            let owned = threaded
                .load_choreography_owned(&image, "threaded/runtime")
                .expect("threaded owned open should succeed");

            assert_eq!(owned.capability().owner_id, "threaded/runtime");
            assert_eq!(owned.capability().generation, 0);
            assert!(matches!(owned.capability().scope, OwnershipScope::Session));
        }

        #[test]
        fn threaded_ownership_transfer_matches_cooperative_audit_surface() {
            let image = transfer_image();

            let mut coop = ProtocolMachine::new(ProtocolMachineConfig::default());
            coop.load_choreography(&image)
                .expect("load cooperative transfer fixture");
            coop.run(&NoopHandler, 32)
                .expect("run cooperative transfer fixture");

            let mut threaded = ThreadedGuestRuntime::with_workers(ProtocolMachineConfig::default(), 2);
            threaded
                .load_choreography_owned(&image, "threaded/ownership_contracts")
                .expect("load threaded transfer fixture");
            threaded
                .run(&NoopHandler, 32)
                .expect("run threaded transfer fixture");

            let coop_transfers: Vec<_> = coop
                .trace()
                .iter()
                .filter_map(|event| match event {
                    ObsEvent::Transferred {
                        session,
                        role,
                        from,
                        to,
                        ..
                    } => Some((*session, role.clone(), *from, *to)),
                    _ => None,
                })
                .collect();
            let threaded_transfers: Vec<_> = threaded
                .trace()
                .iter()
                .filter_map(|event| match event {
                    ObsEvent::Transferred {
                        session,
                        role,
                        from,
                        to,
                        ..
                    } => Some((*session, role.clone(), *from, *to)),
                    _ => None,
                })
                .collect();

            assert_eq!(coop_transfers, threaded_transfers);

            let coop_audit = coop
                .delegation_audit_log()
                .last()
                .expect("cooperative transfer should emit audit");
            let threaded_audit = threaded
                .machine()
                .delegation_audit_log()
                .last()
                .expect("threaded transfer should emit audit");

            assert_eq!(coop_audit.status, threaded_audit.status);
            assert_eq!(coop_audit.receipt.endpoint, threaded_audit.receipt.endpoint);
            assert_eq!(coop_audit.receipt.scope, threaded_audit.receipt.scope);
            assert_eq!(coop_audit.receipt.from_coro, threaded_audit.receipt.from_coro);
            assert_eq!(coop_audit.receipt.to_coro, threaded_audit.receipt.to_coro);
        }
    }
}
