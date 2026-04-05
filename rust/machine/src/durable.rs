//! Typed durability artifacts for agreement journals, evidence outcome caches,
//! and recovery metadata.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

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

impl AgreementJournalEntry {
    /// Tick at which this journal entry was observed.
    #[must_use]
    pub const fn tick(&self) -> u64 {
        match self {
            Self::Escalation { tick, .. }
            | Self::EvidenceProduced { tick, .. }
            | Self::Finalization { tick, .. }
            | Self::VisibilityGateCrossing { tick, .. } => *tick,
        }
    }

    /// Stable operation id associated with this journal entry.
    #[must_use]
    pub fn operation_id(&self) -> &str {
        match self {
            Self::Escalation { operation_id, .. }
            | Self::Finalization { operation_id, .. }
            | Self::VisibilityGateCrossing { operation_id, .. } => operation_id,
            Self::EvidenceProduced { evidence, .. } => &evidence.operation_id,
        }
    }

    /// Deterministic identity string for testing and replay-oriented analysis.
    #[must_use]
    pub fn stable_identity(&self) -> String {
        match self {
            Self::Escalation {
                operation_id,
                previous_level,
                new_level,
                evidence_id,
                tick,
            } => format!(
                "escalation:{operation_id}:{previous_level:?}:{new_level:?}:{}:{tick}",
                evidence_id.as_deref().unwrap_or("-")
            ),
            Self::EvidenceProduced { evidence, tick } => format!(
                "evidence:{}:{}:{:?}:{tick}",
                evidence.operation_id, evidence.evidence_id, evidence.level
            ),
            Self::Finalization {
                operation_id,
                outcome,
                materialization_proof_id,
                canonical_handle_id,
                tick,
            } => format!(
                "finalization:{operation_id}:{outcome:?}:{}:{}:{tick}",
                materialization_proof_id.as_deref().unwrap_or("-"),
                canonical_handle_id.as_deref().unwrap_or("-")
            ),
            Self::VisibilityGateCrossing {
                operation_id,
                downstream_coroutine_id,
                gate_level,
                tick,
            } => format!("gate:{operation_id}:{downstream_coroutine_id}:{gate_level:?}:{tick}"),
        }
    }
}

impl AgreementJournalArtifact {
    /// Return the journal suffix strictly after `tick`.
    #[must_use]
    pub fn read_since(&self, tick: u64) -> Vec<AgreementJournalEntry> {
        self.entries
            .iter()
            .filter(|entry| entry.tick() > tick)
            .cloned()
            .collect()
    }

    /// Validate monotonic escalation ordering for each operation.
    ///
    /// # Errors
    ///
    /// Returns an error if an escalation entry regresses agreement level or
    /// appears out of order for one operation.
    pub fn validate_monotonic_escalations(&self) -> Result<(), String> {
        let mut last_levels = BTreeMap::<String, AgreementLevel>::new();
        for entry in &self.entries {
            let AgreementJournalEntry::Escalation {
                operation_id,
                previous_level,
                new_level,
                ..
            } = entry
            else {
                continue;
            };
            if new_level.rank() < previous_level.rank() {
                return Err(format!(
                    "agreement journal regression for `{operation_id}`: {previous_level:?} -> {new_level:?}"
                ));
            }
            if let Some(last) = last_levels.get(operation_id) {
                if previous_level.rank() < last.rank() || new_level.rank() < last.rank() {
                    return Err(format!(
                        "agreement journal reordered or regressed for `{operation_id}`: last={last:?}, entry={previous_level:?}->{new_level:?}"
                    ));
                }
            }
            last_levels.insert(operation_id.clone(), *new_level);
        }
        Ok(())
    }
}

/// Narrow append/query contract for durable agreement journals.
pub trait AgreementJournal {
    /// Append one journal entry.
    ///
    /// # Errors
    ///
    /// Returns an error if the backend cannot persist the entry or if the
    /// resulting journal violates monotonic escalation ordering.
    fn append(&mut self, entry: AgreementJournalEntry) -> Result<(), String>;

    /// Read entries strictly after `tick`.
    ///
    /// # Errors
    ///
    /// Returns an error if the backend cannot load the journal.
    fn read_since(&self, tick: u64) -> Result<Vec<AgreementJournalEntry>, String>;

    /// Load the full journal artifact.
    ///
    /// # Errors
    ///
    /// Returns an error if the backend cannot load the journal.
    fn load(&self) -> Result<AgreementJournalArtifact, String>;
}

/// In-memory agreement journal backend useful for focused tests and
/// deterministic in-process integrations.
#[derive(Debug, Clone, Default)]
pub struct InMemoryAgreementJournal {
    artifact: AgreementJournalArtifact,
}

impl InMemoryAgreementJournal {
    /// Create one empty in-memory agreement journal.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }
}

impl AgreementJournal for InMemoryAgreementJournal {
    fn append(&mut self, entry: AgreementJournalEntry) -> Result<(), String> {
        self.artifact.entries.push(entry);
        self.artifact.validate_monotonic_escalations()
    }

    fn read_since(&self, tick: u64) -> Result<Vec<AgreementJournalEntry>, String> {
        Ok(self.artifact.read_since(tick))
    }

    fn load(&self) -> Result<AgreementJournalArtifact, String> {
        Ok(self.artifact.clone())
    }
}

/// File-backed agreement journal backend for the initial local durability
/// rollout.
#[derive(Debug, Clone)]
pub struct FileAgreementJournal {
    path: PathBuf,
}

impl FileAgreementJournal {
    /// Create one file-backed journal rooted at `path`.
    #[must_use]
    pub fn new(path: impl Into<PathBuf>) -> Self {
        Self { path: path.into() }
    }

    fn load_artifact(&self) -> Result<AgreementJournalArtifact, String> {
        if !self.path.exists() {
            return Ok(AgreementJournalArtifact::default());
        }
        PersistedDurabilityArtifact::from_path(&self.path)?.into_agreement_journal()
    }

    fn store_artifact(&self, artifact: &AgreementJournalArtifact) -> Result<(), String> {
        artifact.validate_monotonic_escalations()?;
        PersistedDurabilityArtifact::agreement_journal(artifact.clone()).write_to_path(&self.path)
    }
}

impl AgreementJournal for FileAgreementJournal {
    fn append(&mut self, entry: AgreementJournalEntry) -> Result<(), String> {
        let mut artifact = self.load_artifact()?;
        artifact.entries.push(entry);
        self.store_artifact(&artifact)
    }

    fn read_since(&self, tick: u64) -> Result<Vec<AgreementJournalEntry>, String> {
        Ok(self.load_artifact()?.read_since(tick))
    }

    fn load(&self) -> Result<AgreementJournalArtifact, String> {
        self.load_artifact()
    }
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

    /// Borrow the agreement-journal payload when this artifact wraps one.
    #[must_use]
    pub fn agreement_journal_artifact(&self) -> Option<&AgreementJournalArtifact> {
        match &self.payload {
            PersistedDurabilityPayload::AgreementJournal(journal) => Some(journal),
            PersistedDurabilityPayload::EvidenceOutcomeCache(_)
            | PersistedDurabilityPayload::RecoveryMetadata(_) => None,
        }
    }

    /// Consume the wrapper into one agreement-journal artifact.
    ///
    /// # Errors
    ///
    /// Returns an error if this persisted artifact is not an agreement-journal
    /// payload.
    pub fn into_agreement_journal(self) -> Result<AgreementJournalArtifact, String> {
        match self.payload {
            PersistedDurabilityPayload::AgreementJournal(journal) => Ok(journal),
            PersistedDurabilityPayload::EvidenceOutcomeCache(_) => Err(
                "persisted durability artifact contains an evidence outcome cache payload, not an agreement journal"
                    .to_string(),
            ),
            PersistedDurabilityPayload::RecoveryMetadata(_) => Err(
                "persisted durability artifact contains recovery metadata, not an agreement journal"
                    .to_string(),
            ),
        }
    }
}
