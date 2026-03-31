#![cfg(not(target_arch = "wasm32"))]
#![allow(missing_docs)]

#[allow(dead_code, unreachable_pub)]
#[path = "support/mod.rs"]
mod test_support;

use std::collections::{BTreeMap, BTreeSet};

use cfg_if::cfg_if;
use std::time::Duration;
use telltale_machine::coroutine::Value;
use telltale_machine::instr::{Endpoint, ImmValue, Instr};
use telltale_machine::model::effects::{
    EffectFailure, EffectHandler, EffectResult, SendDecision, SendDecisionInput,
    TopologyPerturbation,
};
use telltale_machine::runtime::loader::CodeImage;
use telltale_machine::ObsEvent;
use telltale_machine::{
    protocol_machine_semantic_objects, run_loaded_protocol_machine_record_replay_conformance,
    AuthoritativeReadKind, AuthorityArtifact, AuthorityAuditEvent, AuthorityAuditRecord,
    CanonicalHandleKind, DelegationAuditRecord, DelegationReceipt, DelegationStatus, Edge,
    FinalizationReadClass, FinalizationStage, OperationInstance, OperationPhase, OutstandingEffect,
    OwnershipError, OwnershipScope, ProgressState, ProtocolCriticalCapabilityArtifact,
    ProtocolCriticalCapabilityLifecycleState, ProtocolMachine, ProtocolMachineConfig,
    PublicationStatus, ReadinessWitness, SemanticAuditRecord, SessionHostMutation,
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

#[derive(Debug, Clone, Copy)]
struct TimeoutReplacementHandler;

impl EffectHandler for TimeoutReplacementHandler {
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

    fn topology_events(&self, tick: u64) -> EffectResult<Vec<TopologyPerturbation>> {
        match tick {
            1 => EffectResult::success(vec![TopologyPerturbation::Timeout {
                site: "A".to_string(),
                duration: Duration::from_millis(20),
            }]),
            2 => EffectResult::success(vec![TopologyPerturbation::Timeout {
                site: "A".to_string(),
                duration: Duration::from_millis(40),
            }]),
            _ => EffectResult::success(Vec::new()),
        }
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
fn ownership_transfer_exposes_first_class_capability_lifecycle_audit() {
    let image = simple_send_recv_image("A", "B", "m");
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    let owned = machine
        .load_choreography_owned(&image, "runtime/owner")
        .expect("owned open should succeed");
    let receipt = owned
        .begin_transfer(
            &mut machine,
            "runtime/worker",
            OwnershipScope::Fragments(BTreeSet::from(["A".to_string()])),
        )
        .expect("transfer staging should succeed");
    let _narrowed = owned
        .commit_transfer(&mut machine, &receipt)
        .expect("transfer commit should succeed");

    let lifecycle = machine.capability_lifecycle_audit_log();
    assert!(
        lifecycle.iter().any(|record| matches!(
            (&record.artifact, record.lifecycle),
            (
                ProtocolCriticalCapabilityArtifact::OwnershipCapability(capability),
                ProtocolCriticalCapabilityLifecycleState::Issued,
            ) if capability.owner_id == "runtime/owner" && capability.generation == 0
        )),
        "expected issued lifecycle record for the initial ownership capability"
    );
    assert!(
        lifecycle.iter().any(|record| matches!(
            (&record.artifact, record.lifecycle),
            (
                ProtocolCriticalCapabilityArtifact::OwnershipReceipt(staged_receipt),
                ProtocolCriticalCapabilityLifecycleState::Issued,
            ) if staged_receipt.claim_id == receipt.claim_id
        )),
        "expected issued lifecycle record for the staged transfer receipt"
    );
    assert!(
        lifecycle.iter().any(|record| matches!(
            (&record.artifact, record.lifecycle),
            (
                ProtocolCriticalCapabilityArtifact::OwnershipReceipt(committed_receipt),
                ProtocolCriticalCapabilityLifecycleState::Committed,
            ) if committed_receipt.claim_id == receipt.claim_id
        )),
        "expected committed lifecycle record for the transfer receipt"
    );
    assert!(
        lifecycle.iter().any(|record| matches!(
            (&record.artifact, record.lifecycle),
            (
                ProtocolCriticalCapabilityArtifact::OwnershipCapability(capability),
                ProtocolCriticalCapabilityLifecycleState::Invalidated,
            ) if capability.owner_id == "runtime/owner" && capability.generation == 0
        )),
        "expected invalidation lifecycle record for the old ownership capability"
    );
    assert!(
        lifecycle.iter().any(|record| matches!(
            (&record.artifact, record.lifecycle),
            (
                ProtocolCriticalCapabilityArtifact::OwnershipCapability(capability),
                ProtocolCriticalCapabilityLifecycleState::Issued,
            ) if capability.owner_id == "runtime/worker" && capability.generation == 1
        )),
        "expected issued lifecycle record for the committed target capability"
    );
}

#[test]
fn timeout_replacement_preserves_linear_lifecycle_order_in_capability_audit() {
    let image = simple_send_recv_image("A", "B", "m");
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    machine
        .load_choreography(&image)
        .expect("load choreography");

    let _ = machine
        .step(&TimeoutReplacementHandler)
        .expect("first timeout ingress should not fault");
    let _ = machine
        .step(&TimeoutReplacementHandler)
        .expect("second timeout ingress should not fault");

    let timeout_lifecycle: Vec<_> = machine
        .capability_lifecycle_audit_log()
        .into_iter()
        .filter_map(|record| match record.artifact {
            ProtocolCriticalCapabilityArtifact::TimeoutWitness(witness) if witness.site == "A" => {
                Some((witness, record.lifecycle))
            }
            _ => None,
        })
        .collect();

    assert_eq!(timeout_lifecycle.len(), 3);
    assert_eq!(
        timeout_lifecycle
            .iter()
            .map(|(_, lifecycle)| *lifecycle)
            .collect::<Vec<_>>(),
        vec![
            ProtocolCriticalCapabilityLifecycleState::Issued,
            ProtocolCriticalCapabilityLifecycleState::Invalidated,
            ProtocolCriticalCapabilityLifecycleState::Issued,
        ]
    );
    assert_eq!(
        timeout_lifecycle[0].0.witness_id,
        timeout_lifecycle[1].0.witness_id
    );
    assert_ne!(
        timeout_lifecycle[1].0.witness_id,
        timeout_lifecycle[2].0.witness_id
    );
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
fn ownership_handoff_invalidates_pretransfer_readiness_witnesses() {
    let image = simple_send_recv_image("A", "B", "m");
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    let owned = machine
        .load_choreography_owned(&image, "runtime/owner")
        .expect("owned open should succeed");

    let witness = owned
        .issue_readiness_witness(&mut machine, "session.ready")
        .expect("issue readiness witness");
    let receipt = owned
        .begin_transfer(&mut machine, "runtime/next-owner", OwnershipScope::Session)
        .expect("begin transfer");
    let transferred = owned
        .commit_transfer(&mut machine, &receipt)
        .expect("commit transfer");

    let stale_err = owned
        .consume_readiness_witness(&mut machine, &witness)
        .expect_err("pre-transfer witness must be stale under revoked ownership");
    assert!(matches!(
        stale_err,
        OwnershipError::StaleCapability {
            session_id,
            ref owner_id,
            expected_generation,
            actual_generation,
        } if session_id == transferred.session_id()
            && owner_id == "runtime/owner"
            && expected_generation == 0
            && actual_generation == 1
    ));

    let new_owner_err = transferred
        .consume_readiness_witness(&mut machine, &witness)
        .expect_err("pre-transfer witness must not validate under the activated owner");
    assert!(matches!(
        new_owner_err,
        OwnershipError::InvalidWitness {
            reason,
            ..
        } if reason.contains("live ownership no longer matches witness")
    ));
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
    assert!(
        machine
            .semantic_objects()
            .finalization()
            .observed_read_is_noncanonical(&observed.read_id),
        "observed reads must stay non-canonical until explicit proof-bearing materialization"
    );
}

#[test]
fn ownership_finalization_path_marks_observed_only_results_noncanonical() {
    let objects = protocol_machine_semantic_objects(
        &[],
        &[],
        &[OperationInstance {
            operation_id: "effect:1".to_string(),
            session: Some(1),
            owner_id: Some("runtime/owner".to_string()),
            kind: "readChannel".to_string(),
            phase: OperationPhase::Succeeded,
            handler_identity: Some("host/runtime".to_string()),
            effect_ids: vec![7],
            dependent_operation_ids: Vec::new(),
            terminal_publication: None,
            budget_ticks: Some(1),
            requires_proof: false,
        }],
        &[OutstandingEffect {
            effect_id: 7,
            operation_id: "effect:1".to_string(),
            session: Some(1),
            owner_id: Some("runtime/owner".to_string()),
            effect_interface: Some("runtime/io".to_string()),
            effect_operation: Some("read".to_string()),
            effect_kind: "read".to_string(),
            handler_identity: "host/runtime".to_string(),
            status: telltale_machine::OutstandingEffectStatus::Succeeded,
            ordering_key: 1,
            budget_ticks: Some(1),
            retry_policy: "never".to_string(),
            invalidation_token: "inv#1".to_string(),
            completed_at_tick: Some(1),
            inputs: serde_json::json!({}),
            outputs: serde_json::json!({"value": "ok"}),
        }],
        &[],
        &[],
        &[],
    );

    let path = objects
        .finalization()
        .path_for_operation_id("effect:1")
        .expect("finalization path");
    assert_eq!(path.read_class, FinalizationReadClass::ObservedOnly);
    assert_eq!(path.stage, FinalizationStage::Observed);
    assert_eq!(path.observed_read_ids, vec!["effect:7".to_string()]);
}

#[test]
fn ownership_finalization_path_marks_authoritative_reads_explicitly() {
    let witness = ReadinessWitness {
        witness_id: 7,
        session_id: 1,
        owner_id: "runtime/owner".to_string(),
        generation: 0,
        scope: OwnershipScope::Session,
        predicate_ref: "session.ready".to_string(),
    };
    let objects = protocol_machine_semantic_objects(
        &[AuthorityAuditRecord {
            tick: Some(1),
            event: AuthorityAuditEvent::Issued,
            artifact: AuthorityArtifact::Readiness(witness),
            reason: None,
        }],
        &[],
        &[OperationInstance {
            operation_id: "gate:1".to_string(),
            session: Some(1),
            owner_id: Some("runtime/owner".to_string()),
            kind: "gate".to_string(),
            phase: OperationPhase::Succeeded,
            handler_identity: Some("host/runtime".to_string()),
            effect_ids: Vec::new(),
            dependent_operation_ids: Vec::new(),
            terminal_publication: None,
            budget_ticks: Some(1),
            requires_proof: false,
        }],
        &[],
        &[],
        &[],
        &[],
    );

    let path = objects
        .finalization()
        .path_for_operation_id("gate:1")
        .expect("finalization path");
    assert_eq!(path.read_class, FinalizationReadClass::AuthoritativeOnly);
    assert_eq!(path.stage, FinalizationStage::Authoritative);
    assert_eq!(
        path.authoritative_read_ids,
        vec!["readiness:7:Issued".to_string()]
    );
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
    let path = objects
        .finalization()
        .path_for_operation_id("accept:1")
        .expect("finalization path");
    assert_eq!(path.stage, FinalizationStage::Rejected);
    assert_eq!(
        path.rejected_publication_ids,
        vec![publication.publication_id.clone()]
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
    let operation = semantic_objects
        .operation_instances
        .iter()
        .find(|operation| operation.operation_id.starts_with("materialization:"))
        .expect("materialization operation");
    let path = semantic_objects
        .finalization()
        .path_for_operation(operation);
    assert_eq!(path.stage, FinalizationStage::Canonical);
    assert!(
        path.canonical_handle_ids
            .iter()
            .any(|id| id == &handle.handle_id),
        "materialized canonical path should carry the issued canonical handle"
    );
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
fn ownership_handoff_invalidates_finalization_path_for_affected_operations() {
    let objects = protocol_machine_semantic_objects(
        &[],
        &[DelegationAuditRecord {
            tick: 9,
            receipt: DelegationReceipt {
                receipt_id: 9,
                session: 1,
                endpoint: Endpoint {
                    sid: 1,
                    role: "A".to_string(),
                },
                from_coro: 0,
                to_coro: 1,
                scope: OwnershipScope::Fragments(BTreeSet::from(["A".to_string()])),
            },
            status: telltale_machine::DelegationStatus::Committed,
            reason: None,
        }],
        &[OperationInstance {
            operation_id: "effect:1".to_string(),
            session: Some(1),
            owner_id: Some("runtime/owner".to_string()),
            kind: "receive".to_string(),
            phase: OperationPhase::Blocked,
            handler_identity: Some("host/runtime".to_string()),
            effect_ids: vec![7],
            dependent_operation_ids: Vec::new(),
            terminal_publication: None,
            budget_ticks: Some(9),
            requires_proof: false,
        }],
        &[OutstandingEffect {
            effect_id: 7,
            operation_id: "effect:1".to_string(),
            session: Some(1),
            owner_id: Some("runtime/owner".to_string()),
            effect_interface: Some("runtime/io".to_string()),
            effect_operation: Some("recv".to_string()),
            effect_kind: "recv".to_string(),
            handler_identity: "host/runtime".to_string(),
            status: telltale_machine::OutstandingEffectStatus::Invalidated,
            ordering_key: 9,
            budget_ticks: Some(9),
            retry_policy: "never".to_string(),
            invalidation_token: "handoff#9".to_string(),
            completed_at_tick: Some(9),
            inputs: serde_json::json!({}),
            outputs: serde_json::json!({}),
        }],
        &[],
        &[],
        &[],
    );

    let path = objects
        .finalization()
        .path_for_operation_id("effect:1")
        .expect("finalization path");
    assert_eq!(path.stage, FinalizationStage::Invalidated);
    assert_eq!(path.invalidated_by_handoff_ids, vec![9]);
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
