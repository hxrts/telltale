//! Focused typed durability contract tests.

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

use telltale_machine::coroutine::Value;
use telltale_machine::model::durability::{
    AgreementWal, AgreementWalArtifact, AgreementWalEntry, DurableRecoveryMetadata,
    EvidenceOutcomeCacheArtifact, EvidenceOutcomeCacheEntry, EvidencePersistenceHandler,
    FileAgreementWal, FileEvidenceOutcomeCache, InMemoryAgreementWal, InMemoryEvidenceOutcomeCache,
    PersistedDurabilityArtifact, PersistedDurabilityPayload,
};
use telltale_machine::model::effects::{
    EffectHandler, EffectOutcome, EffectRequest, EffectResponse, RecordingEffectHandler,
    ReplayEffectHandler,
};
use telltale_machine::model::semantic_objects::{
    AgreementEvidence, AgreementEvidenceKind, AgreementLevel, FinalizationOutcome,
};
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
