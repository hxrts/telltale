//! Focused typed durability contract tests.

use telltale_machine::model::durability::{
    AgreementJournalArtifact, AgreementJournalEntry, DurableRecoveryMetadata,
    EvidenceOutcomeCacheArtifact, EvidenceOutcomeCacheEntry, PersistedDurabilityArtifact,
    PersistedDurabilityPayload,
};
use telltale_machine::model::effects::EffectOutcome;
use telltale_machine::model::semantic_objects::{
    AgreementEvidence, AgreementEvidenceKind, AgreementLevel, FinalizationOutcome,
};
use tempfile::tempdir;

#[test]
fn persisted_durability_artifact_round_trips_journal_entries() {
    let artifact = PersistedDurabilityArtifact::agreement_journal(AgreementJournalArtifact {
        entries: vec![
            AgreementJournalEntry::EvidenceProduced {
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
            AgreementJournalEntry::Escalation {
                operation_id: "op#1".to_string(),
                previous_level: AgreementLevel::Provisional,
                new_level: AgreementLevel::SoftSafe,
                evidence_id: Some("evidence#1".to_string()),
                tick: 4,
            },
            AgreementJournalEntry::Finalization {
                operation_id: "op#1".to_string(),
                outcome: FinalizationOutcome::Finalized,
                materialization_proof_id: Some("proof#1".to_string()),
                canonical_handle_id: Some("handle#1".to_string()),
                tick: 6,
            },
            AgreementJournalEntry::VisibilityGateCrossing {
                operation_id: "op#1".to_string(),
                downstream_coroutine_id: "coro#9".to_string(),
                gate_level: AgreementLevel::Finalized,
                tick: 7,
            },
        ],
    });

    let bytes = artifact.to_cbor().expect("encode durability artifact");
    let decoded =
        PersistedDurabilityArtifact::from_slice(&bytes).expect("decode durability artifact");
    assert_eq!(decoded, artifact);
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
        journal_tail_start_tick: Some(11),
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
