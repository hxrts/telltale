//! Focused typed durability contract tests.

use std::collections::BTreeMap;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

use telltale_machine::coroutine::Value;
use telltale_machine::instr::InvokeAction;
use telltale_machine::model::durability::{
    AgreementWal, AgreementWalArtifact, AgreementWalEntry, AgreementWalHandler,
    DurableRecoveryMetadata, EvidenceOutcomeCacheArtifact, EvidenceOutcomeCacheEntry,
    EvidencePersistenceHandler, FileAgreementWal, FileEvidenceOutcomeCache, InMemoryAgreementWal,
    InMemoryEvidenceOutcomeCache, PersistedDurabilityArtifact, PersistedDurabilityPayload,
    WalSyncMode, WalSyncRequest,
};
use telltale_machine::model::effects::{
    EffectHandler, EffectOutcome, EffectRequest, EffectRequestBody, EffectResponse, EffectResult,
    RecordingEffectHandler, ReplayEffectHandler,
};
use telltale_machine::model::output_condition::{OutputConditionHint, OutputConditionPolicy};
use telltale_machine::model::semantic_objects::{
    AgreementEvidence, AgreementEvidenceKind, AgreementLevel, AgreementState, FinalizationOutcome,
    ProgressState,
};
use telltale_machine::runtime::loader::CodeImage;
use telltale_machine::{Instr, ProtocolMachine, ProtocolMachineConfig, StepResult};
use telltale_types::{GlobalType, LocalTypeR};
use tempfile::tempdir;

fn sample_wal_artifact() -> AgreementWalArtifact {
    AgreementWalArtifact {
        entries: vec![
            AgreementWalEntry::EvidenceProduced {
                evidence: AgreementEvidence {
                    evidence_id: "evidence#1".to_string(),
                    operation_id: "op#1".to_string(),
                    session: None,
                    owner_id: None,
                    level: AgreementLevel::SoftSafe,
                    kind: AgreementEvidenceKind::CommitFact,
                    reference: "commit://1".to_string(),
                    authoritative: true,
                },
                tick: 4,
            },
            AgreementWalEntry::Escalation {
                operation_id: "op#1".to_string(),
                previous_level: AgreementLevel::Provisional,
                new_level: AgreementLevel::SoftSafe,
                evidence_id: Some("evidence#1".to_string()),
                tick: 4,
            },
            AgreementWalEntry::Finalization {
                operation_id: "op#1".to_string(),
                outcome: FinalizationOutcome::Finalized,
                materialization_proof_id: Some("proof#1".to_string()),
                canonical_handle_id: Some("handle#1".to_string()),
                tick: 6,
            },
            AgreementWalEntry::VisibilityGateCrossing {
                operation_id: "op#1".to_string(),
                downstream_coroutine_id: "coro#9".to_string(),
                gate_level: AgreementLevel::Finalized,
                tick: 7,
            },
        ],
    }
}

fn sample_wal_sync_request() -> WalSyncRequest {
    WalSyncRequest {
        operation_id: "op#1".to_string(),
        downstream_coroutine_id: "coro#9".to_string(),
        gate_level: AgreementLevel::Finalized,
        agreement_state: Some(AgreementState {
            operation_id: "op#1".to_string(),
            session: None,
            owner_id: None,
            contract_name: "agreement:op#1".to_string(),
            level: AgreementLevel::Finalized,
            finalization: Some(FinalizationOutcome::Finalized),
            evidence_ids: vec!["evidence#1".to_string(), "proof#1".to_string()],
            last_updated_tick: Some(7),
            reason: None,
        }),
        agreement_evidence: vec![AgreementEvidence {
            evidence_id: "evidence#1".to_string(),
            operation_id: "op#1".to_string(),
            session: None,
            owner_id: None,
            level: AgreementLevel::Finalized,
            kind: AgreementEvidenceKind::Materialization,
            reference: "proof://1".to_string(),
            authoritative: true,
        }],
        tick: 7,
    }
}

fn single_role_end_image(program: Vec<Instr>) -> CodeImage {
    CodeImage {
        programs: {
            let mut programs = BTreeMap::new();
            programs.insert("A".to_string(), program);
            programs
        },
        global_type: GlobalType::End,
        local_types: {
            let mut local_types = BTreeMap::new();
            local_types.insert("A".to_string(), LocalTypeR::End);
            local_types
        },
    }
}

#[derive(Debug, Clone, Copy)]
struct HintedInvokeHandler;

impl EffectHandler for HintedInvokeHandler {
    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &[Value],
    ) -> EffectResult<Value> {
        EffectResult::success(Value::Unit)
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
        EffectResult::success(labels.first().cloned().unwrap_or_default())
    }

    fn step(&self, _role: &str, _state: &mut Vec<Value>) -> EffectResult<()> {
        EffectResult::success(())
    }

    fn output_condition_hint(
        &self,
        sid: usize,
        role: &str,
        _state: &[Value],
    ) -> Option<OutputConditionHint> {
        Some(OutputConditionHint {
            predicate_ref: "machine.custom.observable".to_string(),
            witness_ref: Some(format!("sid:{sid}:role:{role}")),
        })
    }
}

#[derive(Debug, Default)]
struct CountingHandler {
    acquire_calls: Arc<AtomicUsize>,
    step_calls: Arc<AtomicUsize>,
}

impl EffectHandler for CountingHandler {
    fn handler_identity(&self) -> String {
        "counting_handler".to_string()
    }

    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &[Value],
    ) -> telltale_machine::model::effects::EffectResult<Value> {
        telltale_machine::model::effects::EffectResult::success(Value::Unit)
    }

    fn handle_recv(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &mut Vec<Value>,
        _payload: &Value,
    ) -> telltale_machine::model::effects::EffectResult<()> {
        telltale_machine::model::effects::EffectResult::success(())
    }

    fn handle_choose(
        &self,
        _role: &str,
        _partner: &str,
        labels: &[String],
        _state: &[Value],
    ) -> telltale_machine::model::effects::EffectResult<String> {
        telltale_machine::model::effects::EffectResult::success(
            labels.first().cloned().unwrap_or_default(),
        )
    }

    fn step(
        &self,
        _role: &str,
        _state: &mut Vec<Value>,
    ) -> telltale_machine::model::effects::EffectResult<()> {
        self.step_calls.fetch_add(1, Ordering::Relaxed);
        telltale_machine::model::effects::EffectResult::success(())
    }

    fn handle_acquire(
        &self,
        _sid: usize,
        _role: &str,
        _layer: &str,
        _state: &[Value],
    ) -> telltale_machine::model::effects::EffectResult<Value> {
        let call = self.acquire_calls.fetch_add(1, Ordering::Relaxed) + 1;
        telltale_machine::model::effects::EffectResult::success(Value::Str(format!(
            "evidence-value-{call}"
        )))
    }
}

fn acquire_request(operation_id: &str) -> EffectRequest {
    EffectRequest::acquire(
        1,
        7,
        Some(operation_id.to_string()),
        "Coordinator",
        "Storage",
        &[],
    )
}

fn step_request(operation_id: &str) -> EffectRequest {
    EffectRequest::invoke_step(
        2,
        Some(7),
        Some(operation_id.to_string()),
        "Coordinator",
        &[],
    )
}

#[test]
fn persisted_durability_artifact_round_trips_wal_entries() {
    let artifact = PersistedDurabilityArtifact::agreement_wal(sample_wal_artifact());

    let bytes = artifact.to_cbor().expect("encode durability artifact");
    let decoded =
        PersistedDurabilityArtifact::from_slice(&bytes).expect("decode durability artifact");
    assert_eq!(decoded, artifact);
}

#[test]
fn agreement_wal_handler_records_and_replays_wal_sync() {
    let base = CountingHandler::default();
    let wal_handler = AgreementWalHandler::new(&base, InMemoryAgreementWal::new());
    let recorder = RecordingEffectHandler::new(&wal_handler);
    let sync = sample_wal_sync_request();

    assert!(matches!(
        recorder.wal_sync(&sync),
        EffectResult::Success(())
    ));

    let exchanges = recorder.effect_exchanges();
    let last = exchanges.last().expect("recorded wal_sync exchange");
    assert!(matches!(
        last.request.body,
        EffectRequestBody::WalSync { .. }
    ));
    assert!(matches!(
        last.outcome.response,
        Some(EffectResponse::WalSync)
    ));

    let replay = ReplayEffectHandler::new(recorder.effect_trace());
    assert!(matches!(replay.wal_sync(&sync), EffectResult::Success(())));
}

#[test]
fn agreement_wal_backends_preserve_order_and_filter_by_tick() {
    fn exercise_backend(
        wal: &mut dyn AgreementWal,
        expected: &AgreementWalArtifact,
    ) -> Result<(), String> {
        for entry in &expected.entries {
            wal.append(entry.clone())?;
        }
        let loaded = wal.load()?;
        assert_eq!(loaded.entries, expected.entries);
        let suffix = wal.read_since(4)?;
        assert_eq!(suffix, expected.entries[2..].to_vec());
        Ok(())
    }

    let expected = sample_wal_artifact();
    exercise_backend(&mut InMemoryAgreementWal::new(), &expected).expect("exercise in-memory wal");

    let dir = tempdir().expect("create temp dir");
    let path = dir.path().join("wal.cbor");
    exercise_backend(&mut FileAgreementWal::new(path), &expected).expect("exercise file wal");
}

#[test]
fn agreement_wal_artifact_validates_monotonic_escalation_order() {
    let artifact = AgreementWalArtifact {
        entries: vec![
            AgreementWalEntry::Escalation {
                operation_id: "op#regress".to_string(),
                previous_level: AgreementLevel::SoftSafe,
                new_level: AgreementLevel::Provisional,
                evidence_id: None,
                tick: 5,
            },
            AgreementWalEntry::Escalation {
                operation_id: "op#regress".to_string(),
                previous_level: AgreementLevel::Provisional,
                new_level: AgreementLevel::SoftSafe,
                evidence_id: None,
                tick: 6,
            },
        ],
    };

    let error = artifact
        .validate_monotonic_escalations()
        .expect_err("regression should fail validation");
    assert!(error.contains("regression"));
}

#[test]
fn agreement_wal_serialization_is_byte_stable_for_identical_entries() {
    let first = PersistedDurabilityArtifact::agreement_wal(sample_wal_artifact())
        .to_cbor()
        .expect("encode first wal");
    let second = PersistedDurabilityArtifact::agreement_wal(sample_wal_artifact())
        .to_cbor()
        .expect("encode second wal");
    assert_eq!(first, second);

    let identities: Vec<_> = sample_wal_artifact()
        .entries
        .into_iter()
        .map(|entry| entry.stable_identity())
        .collect();
    assert_eq!(
        identities,
        vec![
            "evidence:op#1:evidence#1:SoftSafe:4".to_string(),
            "escalation:op#1:Provisional:SoftSafe:evidence#1:4".to_string(),
            "finalization:op#1:Finalized:proof#1:handle#1:6".to_string(),
            "gate:op#1:coro#9:Finalized:7".to_string()
        ]
    );
}

#[test]
fn persisted_durability_artifact_round_trips_cache_and_recovery_metadata() {
    let cache = PersistedDurabilityArtifact::evidence_outcome_cache(EvidenceOutcomeCacheArtifact {
        entries: vec![EvidenceOutcomeCacheEntry {
            evidence_id: "evidence#2".to_string(),
            interface_name: "Storage".to_string(),
            operation_name: "write".to_string(),
            outcome: EffectOutcome::blocked(),
        }],
    });
    let recovery = PersistedDurabilityArtifact::recovery_metadata(DurableRecoveryMetadata {
        checkpoint_tick: 10,
        wal_tail_start_tick: Some(11),
        highest_recovered_tick: Some(13),
        resumed_operation_ids: vec!["op#2".to_string()],
        terminal_operation_ids: vec!["op#1".to_string()],
        cached_evidence_ids: vec!["evidence#2".to_string()],
    });

    let dir = tempdir().expect("create temp dir");
    let cache_path = dir.path().join("cache.cbor");
    let recovery_path = dir.path().join("recovery.cbor");
    cache
        .write_to_path(&cache_path)
        .expect("write cache artifact");
    recovery
        .write_to_path(&recovery_path)
        .expect("write recovery artifact");

    let loaded_cache =
        PersistedDurabilityArtifact::from_path(&cache_path).expect("load cache artifact");
    let loaded_recovery =
        PersistedDurabilityArtifact::from_path(&recovery_path).expect("load recovery artifact");
    assert_eq!(loaded_cache, cache);
    assert_eq!(loaded_recovery, recovery);
    assert!(matches!(
        loaded_cache.payload,
        PersistedDurabilityPayload::EvidenceOutcomeCache(_)
    ));
    assert!(matches!(
        loaded_recovery.payload,
        PersistedDurabilityPayload::RecoveryMetadata(_)
    ));
}

#[test]
fn evidence_persistence_handler_reuses_cached_outcomes_across_recovery() {
    let handler = CountingHandler::default();
    let dir = tempdir().expect("create temp dir");
    let path = dir.path().join("evidence-cache.cbor");

    let first_wrapper = EvidencePersistenceHandler::new(
        &handler,
        FileEvidenceOutcomeCache::new(&path),
        |request: &EffectRequest| {
            request
                .operation_id
                .as_ref()
                .map(|operation_id| format!("evidence::{operation_id}"))
        },
    );
    let first = first_wrapper.handle_effect(acquire_request("op#recover"));
    assert!(matches!(
        first.response,
        Some(EffectResponse::Acquire { .. })
    ));
    assert_eq!(handler.acquire_calls.load(Ordering::Relaxed), 1);

    let second_wrapper = EvidencePersistenceHandler::new(
        &handler,
        FileEvidenceOutcomeCache::new(&path),
        |request: &EffectRequest| {
            request
                .operation_id
                .as_ref()
                .map(|operation_id| format!("evidence::{operation_id}"))
        },
    );
    let second = second_wrapper.handle_effect(acquire_request("op#recover"));
    assert_eq!(handler.acquire_calls.load(Ordering::Relaxed), 1);
    assert_eq!(first, second);
    assert!(second_wrapper
        .cached_outcome("evidence::op#recover")
        .expect("load cached outcome")
        .is_some());
}

#[test]
fn evidence_persistence_handler_ignores_non_agreement_requests() {
    let handler = CountingHandler::default();
    let wrapper = EvidencePersistenceHandler::new(
        &handler,
        InMemoryEvidenceOutcomeCache::new(),
        |_request: &EffectRequest| None,
    );

    let first = wrapper.handle_effect(step_request("op#step"));
    let second = wrapper.handle_effect(step_request("op#step"));
    assert_eq!(handler.step_calls.load(Ordering::Relaxed), 2);
    assert_eq!(first, second);
    assert_eq!(
        wrapper
            .cache_snapshot()
            .expect("load cache snapshot")
            .entries
            .len(),
        0
    );
}

#[test]
fn evidence_persistence_handler_composes_with_recording_and_replay() {
    let handler = CountingHandler::default();
    let wrapper = EvidencePersistenceHandler::new(
        &handler,
        InMemoryEvidenceOutcomeCache::new(),
        |request: &EffectRequest| {
            request
                .operation_id
                .as_ref()
                .map(|operation_id| format!("evidence::{operation_id}"))
        },
    );
    let recording = RecordingEffectHandler::new(&wrapper);

    let first = recording.handle_effect(acquire_request("op#trace"));
    let second = recording.handle_effect(acquire_request("op#trace"));
    assert_eq!(handler.acquire_calls.load(Ordering::Relaxed), 1);
    assert_eq!(first, second);
    assert_eq!(recording.effect_trace().len(), 2);

    let replay = ReplayEffectHandler::new(recording.effect_trace());
    let replay_first = replay.handle_effect(acquire_request("op#trace"));
    let replay_second = replay.handle_effect(acquire_request("op#trace"));
    assert_eq!(replay_first, first);
    assert_eq!(replay_second, second);
    assert_eq!(replay.remaining(), 0);
}

#[test]
fn protocol_machine_requires_successful_wal_sync_before_visibility_gate_crossing() {
    let image = single_role_end_image(vec![
        Instr::Invoke {
            action: InvokeAction::Reg(0),
        },
        Instr::Halt,
    ]);
    let cfg = ProtocolMachineConfig {
        output_condition_policy: OutputConditionPolicy::AllowAll,
        ..ProtocolMachineConfig::default()
    };

    let mut success_machine = ProtocolMachine::new(cfg.clone());
    success_machine
        .load_choreography(&image)
        .expect("load choreography");
    let hinted = HintedInvokeHandler;
    let success_handler = AgreementWalHandler::new(&hinted, InMemoryAgreementWal::new());
    let step = success_machine
        .step_round(&success_handler, 1)
        .expect("successful wal_sync step");
    assert!(matches!(step, StepResult::Continue));
    assert_eq!(success_machine.output_condition_checks().len(), 1);
    assert!(success_machine
        .effect_exchanges()
        .iter()
        .any(
            |exchange| matches!(exchange.request.body, EffectRequestBody::WalSync { .. })
                && exchange.outcome.status.is_success()
        ));
    let wal_snapshot = success_handler
        .wal_snapshot()
        .expect("load successful wal snapshot");
    assert!(
        wal_snapshot
            .entries
            .iter()
            .any(|entry| matches!(entry, AgreementWalEntry::VisibilityGateCrossing { .. })),
        "successful wal_sync should persist a gate crossing before commit"
    );

    let mut blocked_machine = ProtocolMachine::new(cfg);
    blocked_machine
        .load_choreography(&image)
        .expect("load choreography");
    let blocked_handler = AgreementWalHandler::with_sync_mode(
        &hinted,
        InMemoryAgreementWal::new(),
        WalSyncMode::Blocked,
    );
    let blocked_step = blocked_machine
        .step_round(&blocked_handler, 1)
        .expect("blocked wal_sync step");
    assert!(matches!(blocked_step, StepResult::Continue));
    assert!(blocked_machine.output_condition_checks().is_empty());
    assert!(
        !blocked_machine
            .trace()
            .iter()
            .any(|event| matches!(event, telltale_machine::ObsEvent::Invoked { .. })),
        "gate crossing must not commit observable output when wal_sync blocks"
    );
    assert!(blocked_machine
        .effect_exchanges()
        .iter()
        .any(
            |exchange| matches!(exchange.request.body, EffectRequestBody::WalSync { .. })
                && matches!(
                    exchange.outcome.status,
                    telltale_machine::model::effects::EffectOutcomeStatus::Blocked
                )
        ));
}

#[test]
fn blocked_wal_sync_escalates_through_progress_contract_states() {
    let image = single_role_end_image(vec![
        Instr::Invoke {
            action: InvokeAction::Reg(0),
        },
        Instr::Halt,
    ]);
    let cfg = ProtocolMachineConfig {
        output_condition_policy: OutputConditionPolicy::AllowAll,
        ..ProtocolMachineConfig::default()
    };
    let mut machine = ProtocolMachine::new(cfg);
    machine
        .load_choreography(&image)
        .expect("load choreography");
    let hinted = HintedInvokeHandler;
    let handler = AgreementWalHandler::with_sync_mode(
        &hinted,
        InMemoryAgreementWal::new(),
        WalSyncMode::Blocked,
    );

    machine
        .step_round(&handler, 1)
        .expect("initial blocked wal_sync round");
    let operation_id = machine
        .effect_exchanges()
        .iter()
        .rev()
        .find_map(|exchange| match &exchange.request.body {
            EffectRequestBody::WalSync { .. } => exchange.request.operation_id.clone(),
            _ => None,
        })
        .expect("blocked wal_sync operation id");

    for _ in 0..4 {
        let _ = machine
            .step_round(&handler, 1)
            .expect("progress-escalation round should remain deterministic");
    }

    let objects = machine.semantic_objects();
    let contract = objects
        .progress_contracts
        .iter()
        .find(|contract| contract.operation_id == operation_id)
        .expect("wal_sync progress contract");
    assert_eq!(contract.state, ProgressState::TimedOut);

    let transitions: Vec<_> = objects
        .progress_transitions
        .iter()
        .filter(|transition| transition.operation_id == operation_id)
        .map(|transition| transition.to_state)
        .collect();
    assert_eq!(
        transitions,
        vec![
            ProgressState::Blocked,
            ProgressState::NoProgress,
            ProgressState::Degraded,
            ProgressState::TimedOut,
        ]
    );
}
