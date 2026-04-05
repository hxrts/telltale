//! Typed durability artifacts for agreement journals, evidence outcome caches,
//! and recovery metadata.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::sync::Mutex;

use serde::{Deserialize, Serialize};

use crate::effect::{EffectFailure, EffectHandler, EffectOutcome, EffectRequest};
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

impl EvidenceOutcomeCacheArtifact {
    /// Return one cached effect outcome by evidence id.
    #[must_use]
    pub fn get(&self, evidence_id: &str) -> Option<&EvidenceOutcomeCacheEntry> {
        self.entries
            .iter()
            .find(|entry| entry.evidence_id == evidence_id)
    }
}

/// Narrow append/query contract for persisted evidence outcome caches.
pub trait EvidenceOutcomeCache {
    /// Load one cached outcome by evidence id.
    ///
    /// # Errors
    ///
    /// Returns an error if the backend cannot load the cache.
    fn get(&self, evidence_id: &str) -> Result<Option<EvidenceOutcomeCacheEntry>, String>;

    /// Persist one cached outcome.
    ///
    /// # Errors
    ///
    /// Returns an error if the backend cannot persist the cache entry.
    fn put(&mut self, entry: EvidenceOutcomeCacheEntry) -> Result<(), String>;

    /// Load the full cache artifact.
    ///
    /// # Errors
    ///
    /// Returns an error if the backend cannot load the cache.
    fn load(&self) -> Result<EvidenceOutcomeCacheArtifact, String>;
}

/// In-memory evidence outcome cache backend.
#[derive(Debug, Clone, Default)]
pub struct InMemoryEvidenceOutcomeCache {
    artifact: EvidenceOutcomeCacheArtifact,
}

impl InMemoryEvidenceOutcomeCache {
    /// Create one empty in-memory cache.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }
}

impl EvidenceOutcomeCache for InMemoryEvidenceOutcomeCache {
    fn get(&self, evidence_id: &str) -> Result<Option<EvidenceOutcomeCacheEntry>, String> {
        Ok(self.artifact.get(evidence_id).cloned())
    }

    fn put(&mut self, entry: EvidenceOutcomeCacheEntry) -> Result<(), String> {
        self.artifact
            .entries
            .retain(|candidate| candidate.evidence_id != entry.evidence_id);
        self.artifact.entries.push(entry);
        Ok(())
    }

    fn load(&self) -> Result<EvidenceOutcomeCacheArtifact, String> {
        Ok(self.artifact.clone())
    }
}

/// File-backed evidence outcome cache backend for local durable execution.
#[derive(Debug, Clone)]
pub struct FileEvidenceOutcomeCache {
    path: PathBuf,
}

impl FileEvidenceOutcomeCache {
    /// Create one file-backed cache rooted at `path`.
    #[must_use]
    pub fn new(path: impl Into<PathBuf>) -> Self {
        Self { path: path.into() }
    }

    fn load_artifact(&self) -> Result<EvidenceOutcomeCacheArtifact, String> {
        if !self.path.exists() {
            return Ok(EvidenceOutcomeCacheArtifact::default());
        }
        PersistedDurabilityArtifact::from_path(&self.path)?.into_evidence_outcome_cache()
    }

    fn store_artifact(&self, artifact: &EvidenceOutcomeCacheArtifact) -> Result<(), String> {
        PersistedDurabilityArtifact::evidence_outcome_cache(artifact.clone())
            .write_to_path(&self.path)
    }
}

impl EvidenceOutcomeCache for FileEvidenceOutcomeCache {
    fn get(&self, evidence_id: &str) -> Result<Option<EvidenceOutcomeCacheEntry>, String> {
        Ok(self.load_artifact()?.get(evidence_id).cloned())
    }

    fn put(&mut self, entry: EvidenceOutcomeCacheEntry) -> Result<(), String> {
        let mut artifact = self.load_artifact()?;
        artifact
            .entries
            .retain(|candidate| candidate.evidence_id != entry.evidence_id);
        artifact.entries.push(entry);
        self.store_artifact(&artifact)
    }

    fn load(&self) -> Result<EvidenceOutcomeCacheArtifact, String> {
        self.load_artifact()
    }
}

/// Request-to-evidence-id resolver used by evidence-scoped persistence.
pub trait EvidenceIdResolver: Send + Sync {
    /// Resolve the evidence id for one request when the request should be
    /// cached durably.
    fn evidence_id_for_request(&self, request: &EffectRequest) -> Option<String>;
}

impl<F> EvidenceIdResolver for F
where
    F: Fn(&EffectRequest) -> Option<String> + Send + Sync,
{
    fn evidence_id_for_request(&self, request: &EffectRequest) -> Option<String> {
        self(request)
    }
}

/// Effect-handler wrapper that persists agreement-relevant outcomes keyed by
/// semantic evidence id.
pub struct EvidencePersistenceHandler<'a, C, R>
where
    C: EvidenceOutcomeCache,
    R: EvidenceIdResolver,
{
    inner: &'a dyn EffectHandler,
    cache: Mutex<C>,
    resolver: R,
}

impl<'a, C, R> EvidencePersistenceHandler<'a, C, R>
where
    C: EvidenceOutcomeCache,
    R: EvidenceIdResolver,
{
    /// Create one evidence-persistence wrapper around an inner handler.
    #[must_use]
    pub fn new(inner: &'a dyn EffectHandler, cache: C, resolver: R) -> Self {
        Self {
            inner,
            cache: Mutex::new(cache),
            resolver,
        }
    }

    /// Load one cached outcome by evidence id.
    ///
    /// # Errors
    ///
    /// Returns an error if the cache cannot be loaded.
    pub fn cached_outcome(&self, evidence_id: &str) -> Result<Option<EffectOutcome>, String> {
        let cache = self
            .cache
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        Ok(cache.get(evidence_id)?.map(|entry| entry.outcome))
    }

    /// Load the full typed cache artifact.
    ///
    /// # Errors
    ///
    /// Returns an error if the cache cannot be loaded.
    pub fn cache_snapshot(&self) -> Result<EvidenceOutcomeCacheArtifact, String> {
        let cache = self
            .cache
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        cache.load()
    }
}

impl<C, R> EffectHandler for EvidencePersistenceHandler<'_, C, R>
where
    C: EvidenceOutcomeCache + Send,
    R: EvidenceIdResolver,
{
    fn handler_identity(&self) -> String {
        format!("evidence_persistence<{}>", self.inner.handler_identity())
    }

    fn handle_effect(&self, request: EffectRequest) -> EffectOutcome {
        let evidence_id = self.resolver.evidence_id_for_request(&request);
        let interface_name = request.metadata.interface_name.clone();
        let operation_name = request.metadata.operation_name.clone();

        if let Some(evidence_id) = evidence_id.clone() {
            let cache = self
                .cache
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner());
            match cache.get(&evidence_id) {
                Ok(Some(entry)) => return entry.outcome,
                Ok(None) => {}
                Err(err) => {
                    return EffectOutcome::failure(EffectFailure::unavailable(format!(
                        "load evidence outcome cache `{evidence_id}`: {err}"
                    )));
                }
            }
        }

        let outcome = self.inner.handle_effect(request);
        let Some(evidence_id) = evidence_id else {
            return outcome;
        };

        let entry = EvidenceOutcomeCacheEntry {
            evidence_id: evidence_id.clone(),
            interface_name,
            operation_name,
            outcome: outcome.clone(),
        };
        let mut cache = self
            .cache
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        if let Err(err) = cache.put(entry) {
            return EffectOutcome::failure(EffectFailure::unavailable(format!(
                "persist evidence outcome `{evidence_id}`: {err}"
            )));
        }
        outcome
    }

    fn handle_send(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        state: &[crate::coroutine::Value],
    ) -> crate::effect::EffectResult<crate::coroutine::Value> {
        self.inner.handle_send(role, partner, label, state)
    }

    fn send_decision(
        &self,
        input: crate::effect::SendDecisionInput<'_>,
    ) -> crate::effect::EffectResult<crate::effect::SendDecision> {
        self.inner.send_decision(input)
    }

    fn handle_recv(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        state: &mut Vec<crate::coroutine::Value>,
        payload: &crate::coroutine::Value,
    ) -> crate::effect::EffectResult<()> {
        self.inner.handle_recv(role, partner, label, state, payload)
    }

    fn handle_choose(
        &self,
        role: &str,
        partner: &str,
        labels: &[String],
        state: &[crate::coroutine::Value],
    ) -> crate::effect::EffectResult<String> {
        self.inner.handle_choose(role, partner, labels, state)
    }

    fn step(
        &self,
        role: &str,
        state: &mut Vec<crate::coroutine::Value>,
    ) -> crate::effect::EffectResult<()> {
        self.inner.step(role, state)
    }
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

    /// Borrow the evidence-outcome-cache payload when this artifact wraps one.
    #[must_use]
    pub fn evidence_outcome_cache_artifact(&self) -> Option<&EvidenceOutcomeCacheArtifact> {
        match &self.payload {
            PersistedDurabilityPayload::EvidenceOutcomeCache(cache) => Some(cache),
            PersistedDurabilityPayload::AgreementJournal(_)
            | PersistedDurabilityPayload::RecoveryMetadata(_) => None,
        }
    }

    /// Consume the wrapper into one evidence outcome cache artifact.
    ///
    /// # Errors
    ///
    /// Returns an error if this persisted artifact is not an evidence outcome
    /// cache payload.
    pub fn into_evidence_outcome_cache(self) -> Result<EvidenceOutcomeCacheArtifact, String> {
        match self.payload {
            PersistedDurabilityPayload::EvidenceOutcomeCache(cache) => Ok(cache),
            PersistedDurabilityPayload::AgreementJournal(_) => Err(
                "persisted durability artifact contains an agreement journal payload, not an evidence outcome cache"
                    .to_string(),
            ),
            PersistedDurabilityPayload::RecoveryMetadata(_) => Err(
                "persisted durability artifact contains recovery metadata, not an evidence outcome cache"
                    .to_string(),
            ),
        }
    }
}
