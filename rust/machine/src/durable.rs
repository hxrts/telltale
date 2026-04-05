//! Typed durability artifacts for agreement journals, evidence outcome caches,
//! and recovery metadata.

use std::path::Path;

use serde::{Deserialize, Serialize};

use crate::effect::EffectOutcome;
use crate::semantic_objects::{AgreementEvidence, AgreementLevel, FinalizationOutcome};

/// Stable schema version for persisted durability artifacts.
pub const PERSISTED_DURABILITY_SCHEMA_VERSION: &str = "telltale.machine.durability.v1";

/// One append-only agreement journal entry.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case", tag = "kind")]
pub enum AgreementJournalEntry {
    /// Agreement level advanced for one operation.
    Escalation {
        /// Operation whose agreement level changed.
        operation_id: String,
        /// Previous agreement level before the transition.
        previous_level: AgreementLevel,
        /// New agreement level after the transition.
        new_level: AgreementLevel,
        /// Evidence attached to the transition when one exists.
        #[serde(default)]
        evidence_id: Option<String>,
        /// Tick at which the transition was observed.
        tick: u64,
    },
    /// Agreement evidence became durable.
    EvidenceProduced {
        /// Full typed evidence object.
        evidence: AgreementEvidence,
        /// Tick at which the evidence was observed.
        tick: u64,
    },
    /// Finalization outcome became durable.
    Finalization {
        /// Operation that finalized or reached a terminal resolution.
        operation_id: String,
        /// Finalization or terminal outcome.
        outcome: FinalizationOutcome,
        /// Materialization proof id when one exists.
        #[serde(default)]
        materialization_proof_id: Option<String>,
        /// Canonical handle id when one exists.
        #[serde(default)]
        canonical_handle_id: Option<String>,
        /// Tick at which the outcome was observed.
        tick: u64,
    },
    /// One visibility gate was crossed after durable confirmation.
    VisibilityGateCrossing {
        /// Operation whose visibility gate was crossed.
        operation_id: String,
        /// Downstream coroutine released by the gate.
        downstream_coroutine_id: String,
        /// Required agreement level for the gate.
        gate_level: AgreementLevel,
        /// Tick at which the gate crossing was observed.
        tick: u64,
    },
}

/// Typed agreement-journal artifact.
#[derive(Debug, Clone, Default, Serialize, Deserialize, PartialEq, Eq)]
pub struct AgreementJournalArtifact {
    /// Append-only journal entries in canonical order.
    pub entries: Vec<AgreementJournalEntry>,
}

/// One persisted effect outcome keyed by semantic evidence id.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct EvidenceOutcomeCacheEntry {
    /// Semantic evidence id used as the idempotency key.
    pub evidence_id: String,
    /// Effect interface name associated with the cached outcome.
    pub interface_name: String,
    /// Effect operation name associated with the cached outcome.
    pub operation_name: String,
    /// Cached typed effect outcome.
    pub outcome: EffectOutcome,
}

/// Typed evidence outcome cache artifact.
#[derive(Debug, Clone, Default, Serialize, Deserialize, PartialEq)]
pub struct EvidenceOutcomeCacheArtifact {
    /// Persisted evidence-scoped effect outcomes.
    pub entries: Vec<EvidenceOutcomeCacheEntry>,
}

/// Typed recovery metadata derived from one checkpoint plus durable journal
/// suffix.
#[derive(Debug, Clone, Default, Serialize, Deserialize, PartialEq, Eq)]
pub struct DurableRecoveryMetadata {
    /// Checkpoint tick used as the recovery base.
    pub checkpoint_tick: u64,
    /// First tick in the journal suffix applied on top of the checkpoint.
    #[serde(default)]
    pub journal_tail_start_tick: Option<u64>,
    /// Highest tick observed in the durable suffix.
    #[serde(default)]
    pub highest_recovered_tick: Option<u64>,
    /// Operation ids whose durable state was replayed during recovery.
    #[serde(default)]
    pub resumed_operation_ids: Vec<String>,
    /// Operation ids that were already terminal at recovery time.
    #[serde(default)]
    pub terminal_operation_ids: Vec<String>,
    /// Cached evidence ids reused during recovery.
    #[serde(default)]
    pub cached_evidence_ids: Vec<String>,
}

/// Kind-tagged persisted durability payload family.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[serde(rename_all = "snake_case", tag = "kind", content = "payload")]
pub enum PersistedDurabilityPayload {
    /// Agreement journal payload.
    AgreementJournal(AgreementJournalArtifact),
    /// Evidence outcome cache payload.
    EvidenceOutcomeCache(EvidenceOutcomeCacheArtifact),
    /// Recovery metadata payload.
    RecoveryMetadata(DurableRecoveryMetadata),
}

/// Typed persisted durability wrapper for on-disk durable execution artifacts.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct PersistedDurabilityArtifact {
    /// Stable schema version for this persisted artifact family.
    pub schema_version: String,
    /// Concrete durable payload.
    pub payload: PersistedDurabilityPayload,
}

impl PersistedDurabilityArtifact {
    /// Wrap one agreement-journal artifact for persistence.
    #[must_use]
    pub fn agreement_journal(journal: AgreementJournalArtifact) -> Self {
        Self {
            schema_version: PERSISTED_DURABILITY_SCHEMA_VERSION.to_string(),
            payload: PersistedDurabilityPayload::AgreementJournal(journal),
        }
    }

    /// Wrap one evidence outcome cache artifact for persistence.
    #[must_use]
    pub fn evidence_outcome_cache(cache: EvidenceOutcomeCacheArtifact) -> Self {
        Self {
            schema_version: PERSISTED_DURABILITY_SCHEMA_VERSION.to_string(),
            payload: PersistedDurabilityPayload::EvidenceOutcomeCache(cache),
        }
    }

    /// Wrap one recovery metadata artifact for persistence.
    #[must_use]
    pub fn recovery_metadata(metadata: DurableRecoveryMetadata) -> Self {
        Self {
            schema_version: PERSISTED_DURABILITY_SCHEMA_VERSION.to_string(),
            payload: PersistedDurabilityPayload::RecoveryMetadata(metadata),
        }
    }

    /// Decode one persisted durability artifact from CBOR bytes.
    ///
    /// # Errors
    ///
    /// Returns an error if the bytes are invalid CBOR, the schema version is
    /// unsupported, or the payload does not decode.
    pub fn from_slice(bytes: &[u8]) -> Result<Self, String> {
        let artifact: Self = serde_cbor::from_slice(bytes)
            .map_err(|err| format!("decode persisted durability artifact: {err}"))?;
        if artifact.schema_version != PERSISTED_DURABILITY_SCHEMA_VERSION {
            return Err(format!(
                "unsupported persisted durability schema version `{}`",
                artifact.schema_version
            ));
        }
        Ok(artifact)
    }

    /// Load one persisted durability artifact from disk.
    ///
    /// # Errors
    ///
    /// Returns an error if the file cannot be read or the artifact cannot be
    /// decoded.
    pub fn from_path(path: impl AsRef<Path>) -> Result<Self, String> {
        let path = path.as_ref();
        let bytes = std::fs::read(path).map_err(|err| {
            format!(
                "read persisted durability artifact {}: {err}",
                path.display()
            )
        })?;
        Self::from_slice(&bytes)
    }

    /// Encode the artifact as CBOR bytes.
    ///
    /// # Errors
    ///
    /// Returns an error when serialization fails.
    pub fn to_cbor(&self) -> Result<Vec<u8>, String> {
        serde_cbor::to_vec(self)
            .map_err(|err| format!("encode persisted durability artifact: {err}"))
    }

    /// Persist the artifact to disk as CBOR.
    ///
    /// # Errors
    ///
    /// Returns an error if serialization or file writing fails.
    pub fn write_to_path(&self, path: impl AsRef<Path>) -> Result<(), String> {
        let path = path.as_ref();
        let bytes = self.to_cbor()?;
        std::fs::write(path, bytes).map_err(|err| {
            format!(
                "write persisted durability artifact {}: {err}",
                path.display()
            )
        })
    }
}
