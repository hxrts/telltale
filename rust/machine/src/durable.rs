//! Typed durability artifacts for agreement WALs, evidence outcome caches,
//! and recovery metadata.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::sync::Mutex;

use serde::{Deserialize, Serialize};

use crate::effect::{EffectFailure, EffectHandler, EffectOutcome, EffectRequest, EffectResult};
use crate::semantic_objects::{
    AgreementEvidence, AgreementLevel, AgreementState, FinalizationOutcome,
};

/// Stable schema version for persisted durability artifacts.
pub const PERSISTED_DURABILITY_SCHEMA_VERSION: &str = "telltale.machine.durability.v1";

/// One append-only agreement WAL entry.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case", tag = "kind")]
pub enum AgreementWalEntry {
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

/// Typed agreement-WAL artifact.
#[derive(Debug, Clone, Default, Serialize, Deserialize, PartialEq, Eq)]
pub struct AgreementWalArtifact {
    /// Append-only WAL entries in canonical order.
    pub entries: Vec<AgreementWalEntry>,
}

/// Typed request payload for the internal `wal_sync` effect.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct WalSyncRequest {
    /// Operation whose durable state is being synchronized.
    pub operation_id: String,
    /// Coroutine released by the visibility gate on success.
    pub downstream_coroutine_id: String,
    /// Required agreement level for the gated step.
    pub gate_level: AgreementLevel,
    /// Current agreement state snapshot for the operation when available.
    #[serde(default)]
    pub agreement_state: Option<AgreementState>,
    /// Agreement evidence attached to the operation when available.
    #[serde(default)]
    pub agreement_evidence: Vec<AgreementEvidence>,
    /// Tick at which the gate is attempting to cross.
    pub tick: u64,
}

impl AgreementWalEntry {
    /// Tick at which this WAL entry was observed.
    #[must_use]
    pub const fn tick(&self) -> u64 {
        match self {
            Self::Escalation { tick, .. }
            | Self::EvidenceProduced { tick, .. }
            | Self::Finalization { tick, .. }
            | Self::VisibilityGateCrossing { tick, .. } => *tick,
        }
    }

    /// Stable operation id associated with this WAL entry.
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

impl AgreementWalArtifact {
    /// Return the WAL suffix strictly after `tick`.
    #[must_use]
    pub fn read_since(&self, tick: u64) -> Vec<AgreementWalEntry> {
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
            let AgreementWalEntry::Escalation {
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
                    "agreement WAL regression for `{operation_id}`: {previous_level:?} -> {new_level:?}"
                ));
            }
            if let Some(last) = last_levels.get(operation_id) {
                if previous_level.rank() < last.rank() || new_level.rank() < last.rank() {
                    return Err(format!(
                        "agreement WAL reordered or regressed for `{operation_id}`: last={last:?}, entry={previous_level:?}->{new_level:?}"
                    ));
                }
            }
            last_levels.insert(operation_id.clone(), *new_level);
        }
        Ok(())
    }
}

/// Narrow append/query contract for durable agreement WALs.
pub trait AgreementWal {
    /// Append one WAL entry.
    ///
    /// # Errors
    ///
    /// Returns an error if the backend cannot persist the entry or if the
    /// resulting WAL violates monotonic escalation ordering.
    fn append(&mut self, entry: AgreementWalEntry) -> Result<(), String>;

    /// Read entries strictly after `tick`.
    ///
    /// # Errors
    ///
    /// Returns an error if the backend cannot load the WAL.
    fn read_since(&self, tick: u64) -> Result<Vec<AgreementWalEntry>, String>;

    /// Load the full WAL artifact.
    ///
    /// # Errors
    ///
    /// Returns an error if the backend cannot load the WAL.
    fn load(&self) -> Result<AgreementWalArtifact, String>;
}

/// In-memory agreement WAL backend useful for focused tests and
/// deterministic in-process integrations.
#[derive(Debug, Clone, Default)]
pub struct InMemoryAgreementWal {
    artifact: AgreementWalArtifact,
}

impl InMemoryAgreementWal {
    /// Create one empty in-memory agreement WAL.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }
}

impl AgreementWal for InMemoryAgreementWal {
    fn append(&mut self, entry: AgreementWalEntry) -> Result<(), String> {
        self.artifact.entries.push(entry);
        self.artifact.validate_monotonic_escalations()
    }

    fn read_since(&self, tick: u64) -> Result<Vec<AgreementWalEntry>, String> {
        Ok(self.artifact.read_since(tick))
    }

    fn load(&self) -> Result<AgreementWalArtifact, String> {
        Ok(self.artifact.clone())
    }
}

/// File-backed agreement WAL backend for the initial local durability
/// rollout.
#[derive(Debug, Clone)]
pub struct FileAgreementWal {
    path: PathBuf,
}

impl FileAgreementWal {
    /// Create one file-backed WAL rooted at `path`.
    #[must_use]
    pub fn new(path: impl Into<PathBuf>) -> Self {
        Self { path: path.into() }
    }

    fn load_artifact(&self) -> Result<AgreementWalArtifact, String> {
        if !self.path.exists() {
            return Ok(AgreementWalArtifact::default());
        }
        PersistedDurabilityArtifact::from_path(&self.path)?.into_agreement_wal()
    }

    fn store_artifact(&self, artifact: &AgreementWalArtifact) -> Result<(), String> {
        artifact.validate_monotonic_escalations()?;
        PersistedDurabilityArtifact::agreement_wal(artifact.clone()).write_to_path(&self.path)
    }
}

impl AgreementWal for FileAgreementWal {
    fn append(&mut self, entry: AgreementWalEntry) -> Result<(), String> {
        let mut artifact = self.load_artifact()?;
        artifact.entries.push(entry);
        self.store_artifact(&artifact)
    }

    fn read_since(&self, tick: u64) -> Result<Vec<AgreementWalEntry>, String> {
        Ok(self.load_artifact()?.read_since(tick))
    }

    fn load(&self) -> Result<AgreementWalArtifact, String> {
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

/// Test and integration behavior for the internal `wal_sync` effect.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WalSyncMode {
    /// Persist entries and report immediate success.
    Immediate,
    /// Block at the visibility gate without persisting.
    Blocked,
    /// Fail the visibility gate without persisting.
    Failure {
        /// Stable error surfaced by the internal effect.
        message: String,
    },
}

impl Default for WalSyncMode {
    fn default() -> Self {
        Self::Immediate
    }
}

/// Effect-handler wrapper that owns one durable agreement WAL and services the
/// internal `wal_sync` effect.
pub struct AgreementWalHandler<'a, W>
where
    W: AgreementWal,
{
    inner: &'a dyn EffectHandler,
    wal: Mutex<W>,
    sync_mode: WalSyncMode,
}

impl<'a, W> AgreementWalHandler<'a, W>
where
    W: AgreementWal,
{
    /// Create one agreement-WAL wrapper around an inner handler.
    #[must_use]
    pub fn new(inner: &'a dyn EffectHandler, wal: W) -> Self {
        Self {
            inner,
            wal: Mutex::new(wal),
            sync_mode: WalSyncMode::Immediate,
        }
    }

    /// Create one agreement-WAL wrapper with an explicit sync mode.
    #[must_use]
    pub fn with_sync_mode(inner: &'a dyn EffectHandler, wal: W, sync_mode: WalSyncMode) -> Self {
        Self {
            inner,
            wal: Mutex::new(wal),
            sync_mode,
        }
    }

    /// Load the current typed WAL snapshot.
    ///
    /// # Errors
    ///
    /// Returns an error if the WAL backend cannot be loaded.
    pub fn wal_snapshot(&self) -> Result<AgreementWalArtifact, String> {
        let wal = self
            .wal
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        wal.load()
    }

    fn build_entries(
        &self,
        wal: &W,
        sync: &WalSyncRequest,
    ) -> Result<Vec<AgreementWalEntry>, String> {
        let existing = wal.load()?;
        let existing_ids: std::collections::BTreeSet<_> = existing
            .entries
            .iter()
            .map(AgreementWalEntry::stable_identity)
            .collect();
        let mut entries = Vec::new();

        for evidence in sync
            .agreement_evidence
            .iter()
            .filter(|evidence| evidence.operation_id == sync.operation_id)
        {
            let entry = AgreementWalEntry::EvidenceProduced {
                evidence: evidence.clone(),
                tick: sync.tick,
            };
            if !existing_ids.contains(&entry.stable_identity()) {
                entries.push(entry);
            }
        }

        if let Some(state) = &sync.agreement_state {
            let previous_level = existing
                .entries
                .iter()
                .filter_map(|entry| match entry {
                    AgreementWalEntry::Escalation {
                        operation_id,
                        new_level,
                        ..
                    } if operation_id == &sync.operation_id => Some(*new_level),
                    _ => None,
                })
                .max_by_key(|level| level.rank())
                .unwrap_or(AgreementLevel::None);
            if state.level.rank() > previous_level.rank() {
                let entry = AgreementWalEntry::Escalation {
                    operation_id: sync.operation_id.clone(),
                    previous_level,
                    new_level: state.level,
                    evidence_id: state.evidence_ids.last().cloned(),
                    tick: sync.tick,
                };
                if !existing_ids.contains(&entry.stable_identity()) {
                    entries.push(entry);
                }
            }
            if let Some(outcome) = state.finalization {
                let entry = AgreementWalEntry::Finalization {
                    operation_id: sync.operation_id.clone(),
                    outcome,
                    materialization_proof_id: state
                        .evidence_ids
                        .iter()
                        .find(|evidence_id| evidence_id.contains("proof"))
                        .cloned(),
                    canonical_handle_id: None,
                    tick: sync.tick,
                };
                if !existing_ids.contains(&entry.stable_identity()) {
                    entries.push(entry);
                }
            }
        }

        let gate = AgreementWalEntry::VisibilityGateCrossing {
            operation_id: sync.operation_id.clone(),
            downstream_coroutine_id: sync.downstream_coroutine_id.clone(),
            gate_level: sync.gate_level,
            tick: sync.tick,
        };
        if !existing_ids.contains(&gate.stable_identity()) {
            entries.push(gate);
        }

        Ok(entries)
    }
}

impl<W> EffectHandler for AgreementWalHandler<'_, W>
where
    W: AgreementWal + Send,
{
    fn handler_identity(&self) -> String {
        format!("agreement_wal<{}>", self.inner.handler_identity())
    }

    fn supports_wal_sync(&self) -> bool {
        true
    }

    fn wal_sync(&self, sync: &WalSyncRequest) -> EffectResult<()> {
        match &self.sync_mode {
            WalSyncMode::Immediate => {
                let mut wal = self
                    .wal
                    .lock()
                    .unwrap_or_else(|poisoned| poisoned.into_inner());
                let entries = match self.build_entries(&*wal, sync) {
                    Ok(entries) => entries,
                    Err(err) => {
                        return EffectResult::failure(EffectFailure::unavailable(format!(
                            "load agreement WAL for `{}`: {err}",
                            sync.operation_id
                        )));
                    }
                };
                for entry in entries {
                    if let Err(err) = wal.append(entry) {
                        return EffectResult::failure(EffectFailure::unavailable(format!(
                            "persist agreement WAL for `{}`: {err}",
                            sync.operation_id
                        )));
                    }
                }
                EffectResult::success(())
            }
            WalSyncMode::Blocked => EffectResult::Blocked,
            WalSyncMode::Failure { message } => {
                EffectResult::failure(EffectFailure::unavailable(message.clone()))
            }
        }
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

/// Typed recovery metadata derived from one checkpoint plus durable WAL
/// suffix.
#[derive(Debug, Clone, Default, Serialize, Deserialize, PartialEq, Eq)]
pub struct DurableRecoveryMetadata {
    /// Checkpoint tick used as the recovery base.
    pub checkpoint_tick: u64,
    /// First tick in the WAL suffix applied on top of the checkpoint.
    #[serde(default)]
    pub wal_tail_start_tick: Option<u64>,
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

/// Resume action chosen for one operation during durable recovery.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum DurableRecoveryAction {
    /// No durable transition exists beyond the checkpoint.
    ReexecuteFromScratch,
    /// Replay from the last persisted evidence boundary.
    ResumeFromEvidenceBoundary,
    /// Reuse the finalized durable result without re-executing.
    ReuseFinalized,
    /// Preserve the terminal rejected/aborted/timed-out outcome.
    PreserveTerminal,
}

/// Typed recovery decision for one durable operation.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct DurableRecoveryDecision {
    /// Operation being classified for recovery.
    pub operation_id: String,
    /// Highest agreement level observed in the WAL suffix.
    pub level: AgreementLevel,
    /// Terminal finalization outcome when one exists.
    #[serde(default)]
    pub finalization: Option<FinalizationOutcome>,
    /// Recovery action derived from the durable suffix.
    pub action: DurableRecoveryAction,
    /// Evidence ids available in the persisted evidence cache.
    #[serde(default)]
    pub cached_evidence_ids: Vec<String>,
    /// Whether the WAL suffix proves a visibility-gate crossing.
    #[serde(default)]
    pub gate_crossed: bool,
}

/// Typed durable recovery state derived from one checkpoint plus WAL suffix.
#[derive(Debug, Serialize, Deserialize)]
pub struct DurableRecoveryPlan {
    /// Decoded machine state at the checkpoint boundary.
    pub machine: crate::ProtocolMachine,
    /// Typed summary metadata for the durable suffix.
    pub metadata: DurableRecoveryMetadata,
    /// WAL entries strictly after the checkpoint tick.
    pub wal_suffix: Vec<AgreementWalEntry>,
    /// Evidence cache snapshot available during recovery.
    pub evidence_cache: EvidenceOutcomeCacheArtifact,
    /// Per-operation recovery decisions derived from the suffix.
    pub decisions: Vec<DurableRecoveryDecision>,
}

/// Kind-tagged persisted durability payload family.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[serde(rename_all = "snake_case", tag = "kind", content = "payload")]
pub enum PersistedDurabilityPayload {
    /// Agreement WAL payload.
    AgreementWal(AgreementWalArtifact),
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
    /// Wrap one agreement-WAL artifact for persistence.
    #[must_use]
    pub fn agreement_wal(wal: AgreementWalArtifact) -> Self {
        Self {
            schema_version: PERSISTED_DURABILITY_SCHEMA_VERSION.to_string(),
            payload: PersistedDurabilityPayload::AgreementWal(wal),
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

    /// Borrow the agreement-WAL payload when this artifact wraps one.
    #[must_use]
    pub fn agreement_wal_artifact(&self) -> Option<&AgreementWalArtifact> {
        match &self.payload {
            PersistedDurabilityPayload::AgreementWal(wal) => Some(wal),
            PersistedDurabilityPayload::EvidenceOutcomeCache(_)
            | PersistedDurabilityPayload::RecoveryMetadata(_) => None,
        }
    }

    /// Consume the wrapper into one agreement-WAL artifact.
    ///
    /// # Errors
    ///
    /// Returns an error if this persisted artifact is not an agreement-WAL
    /// payload.
    pub fn into_agreement_wal(self) -> Result<AgreementWalArtifact, String> {
        match self.payload {
            PersistedDurabilityPayload::AgreementWal(wal) => Ok(wal),
            PersistedDurabilityPayload::EvidenceOutcomeCache(_) => Err(
                "persisted durability artifact contains an evidence outcome cache payload, not an agreement WAL"
                    .to_string(),
            ),
            PersistedDurabilityPayload::RecoveryMetadata(_) => Err(
                "persisted durability artifact contains recovery metadata, not an agreement WAL"
                    .to_string(),
            ),
        }
    }

    /// Borrow the evidence-outcome-cache payload when this artifact wraps one.
    #[must_use]
    pub fn evidence_outcome_cache_artifact(&self) -> Option<&EvidenceOutcomeCacheArtifact> {
        match &self.payload {
            PersistedDurabilityPayload::EvidenceOutcomeCache(cache) => Some(cache),
            PersistedDurabilityPayload::AgreementWal(_)
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
            PersistedDurabilityPayload::AgreementWal(_) => Err(
                "persisted durability artifact contains an agreement WAL payload, not an evidence outcome cache"
                    .to_string(),
            ),
            PersistedDurabilityPayload::RecoveryMetadata(_) => Err(
                "persisted durability artifact contains recovery metadata, not an evidence outcome cache"
                    .to_string(),
            ),
        }
    }
}

impl DurableRecoveryPlan {
    /// Build a typed recovery plan from one checkpointed machine and durable suffix.
    ///
    /// # Errors
    ///
    /// Returns an error if the WAL suffix violates monotonic escalation ordering.
    pub fn from_checkpoint(
        checkpoint_tick: u64,
        machine: crate::ProtocolMachine,
        wal: &AgreementWalArtifact,
        evidence_cache: EvidenceOutcomeCacheArtifact,
    ) -> Result<Self, String> {
        wal.validate_monotonic_escalations()?;
        let wal_suffix = wal.read_since(checkpoint_tick);
        let metadata = DurableRecoveryMetadata {
            checkpoint_tick,
            wal_tail_start_tick: wal_suffix.first().map(AgreementWalEntry::tick),
            highest_recovered_tick: wal_suffix.last().map(AgreementWalEntry::tick),
            resumed_operation_ids: Vec::new(),
            terminal_operation_ids: Vec::new(),
            cached_evidence_ids: evidence_cache
                .entries
                .iter()
                .map(|entry| entry.evidence_id.clone())
                .collect(),
        };
        let mut plan = Self {
            machine,
            metadata,
            wal_suffix,
            evidence_cache,
            decisions: Vec::new(),
        };
        plan.decisions = plan.build_decisions();
        plan.metadata.resumed_operation_ids = plan
            .decisions
            .iter()
            .filter(|decision| {
                matches!(
                    decision.action,
                    DurableRecoveryAction::ReexecuteFromScratch
                        | DurableRecoveryAction::ResumeFromEvidenceBoundary
                )
            })
            .map(|decision| decision.operation_id.clone())
            .collect();
        plan.metadata.terminal_operation_ids = plan
            .decisions
            .iter()
            .filter(|decision| {
                matches!(
                    decision.action,
                    DurableRecoveryAction::ReuseFinalized | DurableRecoveryAction::PreserveTerminal
                )
            })
            .map(|decision| decision.operation_id.clone())
            .collect();
        Ok(plan)
    }

    fn build_decisions(&self) -> Vec<DurableRecoveryDecision> {
        let mut operation_ids = std::collections::BTreeSet::new();
        for entry in &self.wal_suffix {
            operation_ids.insert(entry.operation_id().to_string());
        }

        operation_ids
            .into_iter()
            .map(|operation_id| {
                let mut level = AgreementLevel::None;
                let mut finalization = None;
                let mut gate_crossed = false;
                let mut evidence_ids = Vec::new();

                for entry in self
                    .wal_suffix
                    .iter()
                    .filter(|entry| entry.operation_id() == operation_id)
                {
                    match entry {
                        AgreementWalEntry::Escalation { new_level, .. } => {
                            if new_level.rank() > level.rank() {
                                level = *new_level;
                            }
                        }
                        AgreementWalEntry::EvidenceProduced { evidence, .. } => {
                            evidence_ids.push(evidence.evidence_id.clone());
                            if evidence.level.rank() > level.rank() {
                                level = evidence.level;
                            }
                        }
                        AgreementWalEntry::Finalization { outcome, .. } => {
                            finalization = Some(*outcome);
                            if matches!(outcome, FinalizationOutcome::Finalized) {
                                level = AgreementLevel::Finalized;
                            }
                        }
                        AgreementWalEntry::VisibilityGateCrossing { .. } => {
                            gate_crossed = true;
                        }
                    }
                }

                let cached_evidence_ids = self
                    .evidence_cache
                    .entries
                    .iter()
                    .filter(|entry| {
                        evidence_ids
                            .iter()
                            .any(|evidence_id| evidence_id == &entry.evidence_id)
                    })
                    .map(|entry| entry.evidence_id.clone())
                    .collect::<Vec<_>>();
                let action = match finalization {
                    Some(FinalizationOutcome::Finalized) => DurableRecoveryAction::ReuseFinalized,
                    Some(
                        FinalizationOutcome::Aborted
                        | FinalizationOutcome::Rejected
                        | FinalizationOutcome::TimedOut,
                    ) => DurableRecoveryAction::PreserveTerminal,
                    None if level.at_least(AgreementLevel::SoftSafe) => {
                        DurableRecoveryAction::ResumeFromEvidenceBoundary
                    }
                    None => DurableRecoveryAction::ReexecuteFromScratch,
                };

                DurableRecoveryDecision {
                    operation_id,
                    level,
                    finalization,
                    action,
                    cached_evidence_ids,
                    gate_crossed,
                }
            })
            .collect()
    }
}
