//! Simulator-side durability helpers for fault injection, crash/recovery runs,
//! and durable property monitoring.

use serde::{Deserialize, Serialize};
use std::collections::BTreeSet;

use crate::environment::EnvironmentModels;
use crate::runner::{
    resume_with_durable_checkpoint_artifact, run_with_scenario, DurableResumeArtifacts,
    ScenarioResult,
};
use crate::scenario::Scenario;
use telltale_machine::model::durability::{
    AgreementWal, AgreementWalArtifact, AgreementWalEntry, EvidenceOutcomeCacheArtifact,
};
use telltale_machine::model::effects::{EffectExchangeRecord, EffectHandler, EffectRequestBody};
use telltale_types::{FixedQ32, GlobalType, LocalTypeR};

/// One scheduled durable-backend fault.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct ScheduledDurableFault {
    /// Tick at which the fault becomes active.
    pub tick: u64,
    /// Fault behavior to apply.
    pub kind: DurableFaultKind,
}

/// Deterministic durable fault kinds for WAL-backed execution.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum DurableFaultKind {
    /// Reject one WAL write.
    WriteFailure,
    /// Accept the write but record deterministic latency.
    Latency {
        /// Deterministic latency in simulator ticks.
        ticks: u64,
    },
    /// Reject one append as a simulated partial write.
    PartialWrite,
    /// Reject appends throughout one availability window.
    AvailabilityWindow {
        /// First unavailable tick, inclusive.
        start_tick: u64,
        /// Last unavailable tick, inclusive.
        end_tick: u64,
    },
}

/// One deterministic durable fault program.
#[derive(Debug, Clone, Default, Serialize, Deserialize, PartialEq, Eq)]
pub struct DurableFaultProgram {
    /// Ordered durable fault declarations.
    pub faults: Vec<ScheduledDurableFault>,
}

/// Outcome observed for one triggered durable fault.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum DurableFaultOutcome {
    /// Write was rejected.
    Failed,
    /// Write was accepted after deterministic latency.
    Delayed {
        /// Deterministic latency in simulator ticks.
        ticks: u64,
    },
    /// Backend was unavailable for this write.
    Unavailable,
}

/// One durable fault record captured during WAL append simulation.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct DurableFaultRecord {
    /// Tick at which the write was attempted.
    pub tick: u64,
    /// Operation id carried by the WAL entry.
    pub operation_id: String,
    /// Fault kind applied.
    pub kind: DurableFaultKind,
    /// Resulting deterministic outcome.
    pub outcome: DurableFaultOutcome,
}

/// WAL wrapper that deterministically injects durable-backend faults.
pub struct FaultInjectingAgreementWal<W> {
    inner: W,
    program: DurableFaultProgram,
    history: Vec<DurableFaultRecord>,
}

impl<W> FaultInjectingAgreementWal<W> {
    /// Wrap one authoritative WAL backend with deterministic fault hooks.
    #[must_use]
    pub fn new(inner: W, program: DurableFaultProgram) -> Self {
        Self {
            inner,
            program,
            history: Vec::new(),
        }
    }

    /// Borrow the durable fault history captured so far.
    #[must_use]
    pub fn history(&self) -> &[DurableFaultRecord] {
        &self.history
    }

    /// Consume the wrapper and return the inner backend.
    #[must_use]
    pub fn into_inner(self) -> W {
        self.inner
    }

    fn matching_fault(&self, tick: u64) -> Option<DurableFaultKind> {
        self.program
            .faults
            .iter()
            .find_map(|fault| match &fault.kind {
                DurableFaultKind::AvailabilityWindow {
                    start_tick,
                    end_tick,
                } if tick >= *start_tick && tick <= *end_tick => Some(fault.kind.clone()),
                _ if fault.tick == tick => Some(fault.kind.clone()),
                _ => None,
            })
    }
}

impl<W: AgreementWal> AgreementWal for FaultInjectingAgreementWal<W> {
    fn append(&mut self, entry: AgreementWalEntry) -> Result<(), String> {
        let tick = entry.tick();
        let operation_id = entry.operation_id().to_string();
        if let Some(kind) = self.matching_fault(tick) {
            match &kind {
                DurableFaultKind::WriteFailure => {
                    self.history.push(DurableFaultRecord {
                        tick,
                        operation_id,
                        kind,
                        outcome: DurableFaultOutcome::Failed,
                    });
                    return Err(format!("simulated WAL write failure at tick {tick}"));
                }
                DurableFaultKind::PartialWrite => {
                    self.history.push(DurableFaultRecord {
                        tick,
                        operation_id,
                        kind,
                        outcome: DurableFaultOutcome::Failed,
                    });
                    return Err(format!("simulated WAL partial write at tick {tick}"));
                }
                DurableFaultKind::AvailabilityWindow { .. } => {
                    self.history.push(DurableFaultRecord {
                        tick,
                        operation_id,
                        kind,
                        outcome: DurableFaultOutcome::Unavailable,
                    });
                    return Err(format!(
                        "simulated WAL backend unavailable for append at tick {tick}"
                    ));
                }
                DurableFaultKind::Latency { ticks } => {
                    self.history.push(DurableFaultRecord {
                        tick,
                        operation_id,
                        kind: kind.clone(),
                        outcome: DurableFaultOutcome::Delayed { ticks: *ticks },
                    });
                }
            }
        }
        self.inner.append(entry)
    }

    fn read_since(&self, tick: u64) -> Result<Vec<AgreementWalEntry>, String> {
        self.inner.read_since(tick)
    }

    fn load(&self) -> Result<AgreementWalArtifact, String> {
        self.inner.load()
    }
}

/// Typed result for one simulator crash/recovery comparison.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct DurableRecoveryRun {
    /// Crash tick requested by the caller.
    pub crash_tick: u64,
    /// Checkpoint tick actually used as the durable recovery base.
    pub checkpoint_tick: u64,
    /// Uninterrupted authoritative run.
    pub uninterrupted: ScenarioResult,
    /// Durable checkpoint-plus-WAL resume run.
    pub resumed: ScenarioResult,
}

/// Run one deterministic crash/recovery comparison through the typed durable resume path.
///
/// # Errors
///
/// Returns an error if the uninterrupted run fails, if no checkpoint exists at or
/// before `crash_tick`, or if durable resume fails.
pub fn run_durable_recovery_case(
    local_types: &std::collections::BTreeMap<String, LocalTypeR>,
    global_type: &GlobalType,
    initial_states: &std::collections::BTreeMap<String, Vec<FixedQ32>>,
    scenario: &Scenario,
    handler: &dyn EffectHandler,
    environment_models: Option<EnvironmentModels<'_>>,
    crash_tick: u64,
    durable: &DurableResumeArtifacts,
) -> Result<DurableRecoveryRun, String> {
    let uninterrupted =
        run_with_scenario(local_types, global_type, initial_states, scenario, handler)?;
    let checkpoint = uninterrupted
        .replay
        .checkpoints
        .iter()
        .filter(|checkpoint| checkpoint.tick <= crash_tick)
        .max_by_key(|checkpoint| checkpoint.tick)
        .ok_or_else(|| {
            format!(
                "no checkpoint exists at or before crash tick {crash_tick} for scenario `{}`",
                scenario.name
            )
        })?;
    let resumed = resume_with_durable_checkpoint_artifact(
        scenario,
        checkpoint,
        durable,
        handler,
        environment_models,
        None,
    )?;
    Ok(DurableRecoveryRun {
        crash_tick,
        checkpoint_tick: checkpoint.tick,
        uninterrupted,
        resumed,
    })
}

/// Durable property report derived from one WAL, cache, and run pair.
#[derive(Debug, Clone, Default, Serialize, Deserialize, PartialEq, Eq)]
pub struct DurablePropertyReport {
    /// Whether the write-ahead property held.
    pub write_ahead: bool,
    /// Whether WAL levels remained monotonic.
    pub monotonic_wal_levels: bool,
    /// Whether evidence cache ids matched durable WAL evidence.
    pub evidence_consistency: bool,
    /// Whether recovered and uninterrupted runs are authoritative equivalents.
    pub recovery_equivalence: bool,
    /// Human-readable violations for any failed property.
    pub violations: Vec<String>,
}

/// Projection kind for one durable WAL entry in inspection tooling.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum DurableWalEntryKind {
    /// Agreement-level escalation entry.
    Escalation,
    /// Evidence production entry.
    EvidenceProduced,
    /// Finalization entry.
    Finalization,
    /// Visibility-gate crossing entry.
    VisibilityGateCrossing,
}

/// Observed-only projection of one durable WAL entry.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct DurableWalEntryProjection {
    /// Tick at which the durable transition was observed.
    pub tick: u64,
    /// Stable operation id for the entry.
    pub operation_id: String,
    /// Projection kind for viewer/CLI tooling.
    pub kind: DurableWalEntryKind,
    /// Human-readable detail string.
    pub detail: String,
}

/// Observed-only projection of one evidence-cache entry.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct EvidenceCacheEntryProjection {
    /// Stable evidence id.
    pub evidence_id: String,
    /// Effect interface that produced the cached evidence.
    pub interface_name: String,
    /// Effect operation that produced the cached evidence.
    pub operation_name: String,
    /// Stable outcome-status label.
    pub outcome_status: String,
}

/// Observed-only durable inspection report for viewer and CLI surfaces.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct DurableInspectionReport {
    /// Projected WAL entries.
    pub wal_entries: Vec<DurableWalEntryProjection>,
    /// Projected evidence-cache entries.
    pub evidence_cache_entries: Vec<EvidenceCacheEntryProjection>,
    /// Typed durable recovery summary when available.
    #[serde(default)]
    pub recovery: Option<crate::runner::DurableResumeSummary>,
}

/// Evaluate the durable property monitors used by simulator assurance tests.
#[must_use]
pub fn durable_property_report(
    wal: &AgreementWalArtifact,
    evidence_cache: &EvidenceOutcomeCacheArtifact,
    effect_exchanges: &[EffectExchangeRecord],
    uninterrupted: &ScenarioResult,
    resumed: &ScenarioResult,
) -> DurablePropertyReport {
    let mut report = DurablePropertyReport::default();
    match monitor_write_ahead(wal, effect_exchanges) {
        Ok(()) => report.write_ahead = true,
        Err(err) => report.violations.push(err),
    }
    match monitor_monotonic_wal_levels(wal) {
        Ok(()) => report.monotonic_wal_levels = true,
        Err(err) => report.violations.push(err),
    }
    match monitor_evidence_consistency(wal, evidence_cache) {
        Ok(()) => report.evidence_consistency = true,
        Err(err) => report.violations.push(err),
    }
    match monitor_recovery_equivalence(uninterrupted, resumed) {
        Ok(()) => report.recovery_equivalence = true,
        Err(err) => report.violations.push(err),
    }
    report
}

/// Project authoritative durable artifacts into one observed-only inspection report.
#[must_use]
pub fn inspect_durable_artifacts(
    wal: &AgreementWalArtifact,
    evidence_cache: &EvidenceOutcomeCacheArtifact,
    recovery: Option<&crate::runner::DurableResumeSummary>,
) -> DurableInspectionReport {
    DurableInspectionReport {
        wal_entries: wal
            .entries
            .iter()
            .map(|entry| match entry {
                AgreementWalEntry::Escalation {
                    operation_id,
                    previous_level,
                    new_level,
                    evidence_id,
                    tick,
                } => DurableWalEntryProjection {
                    tick: *tick,
                    operation_id: operation_id.clone(),
                    kind: DurableWalEntryKind::Escalation,
                    detail: format!(
                        "{previous_level:?} -> {new_level:?}{}",
                        evidence_id
                            .as_ref()
                            .map(|evidence_id| format!(" evidence={evidence_id}"))
                            .unwrap_or_default()
                    ),
                },
                AgreementWalEntry::EvidenceProduced { evidence, tick } => {
                    DurableWalEntryProjection {
                        tick: *tick,
                        operation_id: evidence.operation_id.clone(),
                        kind: DurableWalEntryKind::EvidenceProduced,
                        detail: format!(
                            "{:?} level={:?} authoritative={}",
                            evidence.kind, evidence.level, evidence.authoritative
                        ),
                    }
                }
                AgreementWalEntry::Finalization {
                    operation_id,
                    outcome,
                    materialization_proof_id,
                    canonical_handle_id,
                    tick,
                } => DurableWalEntryProjection {
                    tick: *tick,
                    operation_id: operation_id.clone(),
                    kind: DurableWalEntryKind::Finalization,
                    detail: format!(
                        "{outcome:?} proof={} handle={}",
                        materialization_proof_id.as_deref().unwrap_or("-"),
                        canonical_handle_id.as_deref().unwrap_or("-")
                    ),
                },
                AgreementWalEntry::VisibilityGateCrossing {
                    operation_id,
                    downstream_coroutine_id,
                    gate_level,
                    tick,
                } => DurableWalEntryProjection {
                    tick: *tick,
                    operation_id: operation_id.clone(),
                    kind: DurableWalEntryKind::VisibilityGateCrossing,
                    detail: format!("downstream={downstream_coroutine_id} gate={gate_level:?}"),
                },
            })
            .collect(),
        evidence_cache_entries: evidence_cache
            .entries
            .iter()
            .map(|entry| EvidenceCacheEntryProjection {
                evidence_id: entry.evidence_id.clone(),
                interface_name: entry.interface_name.clone(),
                operation_name: entry.operation_name.clone(),
                outcome_status: format!("{:?}", entry.outcome.status),
            })
            .collect(),
        recovery: recovery.cloned(),
    }
}

/// Check the write-ahead property against WAL gate crossings and recorded `wal_sync` effects.
///
/// # Errors
///
/// Returns an error if any gate crossing lacks a successful prior `wal_sync`.
pub fn monitor_write_ahead(
    wal: &AgreementWalArtifact,
    effect_exchanges: &[EffectExchangeRecord],
) -> Result<(), String> {
    for entry in &wal.entries {
        let AgreementWalEntry::VisibilityGateCrossing {
            operation_id,
            downstream_coroutine_id,
            gate_level,
            tick,
        } = entry
        else {
            continue;
        };
        let seen = effect_exchanges.iter().any(|exchange| {
            exchange.succeeded()
                && matches!(
                    &exchange.request.body,
                    EffectRequestBody::WalSync { sync }
                        if sync.operation_id == *operation_id
                            && sync.downstream_coroutine_id == *downstream_coroutine_id
                            && sync.gate_level == *gate_level
                            && sync.tick <= *tick
                )
        });
        if !seen {
            return Err(format!(
                "write-ahead violation: gate crossing for `{operation_id}` at tick {tick} has no successful prior wal_sync"
            ));
        }
    }
    Ok(())
}

/// Check that the WAL never regresses agreement levels.
///
/// # Errors
///
/// Returns an error if the typed WAL violates monotonic escalation ordering.
pub fn monitor_monotonic_wal_levels(wal: &AgreementWalArtifact) -> Result<(), String> {
    wal.validate_monotonic_escalations()
}

/// Check that cached evidence ids are justified by durable WAL evidence.
///
/// # Errors
///
/// Returns an error if any cache entry lacks a matching WAL evidence id.
pub fn monitor_evidence_consistency(
    wal: &AgreementWalArtifact,
    evidence_cache: &EvidenceOutcomeCacheArtifact,
) -> Result<(), String> {
    let wal_evidence_ids = wal.entries.iter().fold(BTreeSet::new(), |mut ids, entry| {
        match entry {
            AgreementWalEntry::Escalation { evidence_id, .. } => {
                if let Some(evidence_id) = evidence_id {
                    ids.insert(evidence_id.clone());
                }
            }
            AgreementWalEntry::EvidenceProduced { evidence, .. } => {
                ids.insert(evidence.evidence_id.clone());
            }
            AgreementWalEntry::Finalization { .. }
            | AgreementWalEntry::VisibilityGateCrossing { .. } => {}
        }
        ids
    });
    for entry in &evidence_cache.entries {
        if !wal_evidence_ids.contains(&entry.evidence_id) {
            return Err(format!(
                "evidence cache entry `{}` has no matching WAL evidence id",
                entry.evidence_id
            ));
        }
    }
    Ok(())
}

/// Check that recovered and uninterrupted runs converge to the same authoritative artifacts.
///
/// # Errors
///
/// Returns an error if any authoritative replay artifact differs.
pub fn monitor_recovery_equivalence(
    uninterrupted: &ScenarioResult,
    resumed: &ScenarioResult,
) -> Result<(), String> {
    if uninterrupted.replay.theorem_profile != resumed.replay.theorem_profile {
        return Err("recovery equivalence failed: theorem profile drifted".to_string());
    }
    if uninterrupted.replay.obs_trace != resumed.replay.obs_trace {
        return Err("recovery equivalence failed: observable trace drifted".to_string());
    }
    if uninterrupted.replay.effect_exchanges != resumed.replay.effect_exchanges {
        return Err("recovery equivalence failed: effect exchanges drifted".to_string());
    }
    if uninterrupted.replay.output_condition_trace != resumed.replay.output_condition_trace {
        return Err("recovery equivalence failed: output-condition trace drifted".to_string());
    }
    if uninterrupted.replay.semantic_audit_log != resumed.replay.semantic_audit_log {
        return Err("recovery equivalence failed: semantic audit drifted".to_string());
    }
    if uninterrupted.replay.semantic_objects != resumed.replay.semantic_objects {
        return Err("recovery equivalence failed: semantic objects drifted".to_string());
    }
    if uninterrupted.replay.reconfiguration_trace != resumed.replay.reconfiguration_trace {
        return Err("recovery equivalence failed: reconfiguration trace drifted".to_string());
    }
    if uninterrupted.replay.environment_trace != resumed.replay.environment_trace {
        return Err("recovery equivalence failed: environment trace drifted".to_string());
    }
    Ok(())
}
