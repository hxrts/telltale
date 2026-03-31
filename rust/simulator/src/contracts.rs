//! Contract checks for simulator runs.
//!
//! These checks give integrators a stable way to assert that a run produced
//! replay-ready artifacts and respected expected runtime invariants.

use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};
use telltale_machine::{
    ObsEvent, ProgressState, ProtocolMachineSemanticObjects, PublicationStatus,
};

use crate::runner::ScenarioResult;

fn default_true() -> bool {
    true
}

fn progress_state_name(state: ProgressState) -> &'static str {
    match state {
        ProgressState::Pending => "pending",
        ProgressState::Blocked => "blocked",
        ProgressState::NoProgress => "no_progress",
        ProgressState::Degraded => "degraded",
        ProgressState::Succeeded => "succeeded",
        ProgressState::Failed => "failed",
        ProgressState::Cancelled => "cancelled",
        ProgressState::TimedOut => "timed_out",
        ProgressState::HandedOff => "handed_off",
    }
}

fn publication_status_name(status: PublicationStatus) -> &'static str {
    match status {
        PublicationStatus::Published => "published",
        PublicationStatus::Rejected => "rejected",
    }
}

/// Expected progress contract state for one operation.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExpectedProgressState {
    /// Operation identifier to match.
    pub operation_id: String,
    /// Expected progress state name in snake_case.
    pub state: String,
}

/// Expected publication outcome for one operation.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExpectedPublication {
    /// Operation identifier to match.
    pub operation_id: String,
    /// Expected terminal publication name.
    pub publication: String,
    /// Expected publication status name in snake_case.
    pub status: String,
}

/// Expected semantic handoff owner transition.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExpectedHandoff {
    /// Expected revoked owner id.
    pub revoked_owner_id: String,
    /// Expected activated owner id.
    pub activated_owner_id: String,
}

/// Contract checks to apply after a simulator run.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ContractCheckConfig {
    /// Require that the run produced no property violations.
    #[serde(default = "default_true")]
    pub no_property_violations: bool,
    /// Require replay metadata to be internally coherent.
    #[serde(default = "default_true")]
    pub replay_coherence: bool,
    /// Require at least this many ProtocolMachine rounds to execute.
    #[serde(default)]
    pub min_rounds_executed: Option<u64>,
    /// Require at least one sampled state for each listed role.
    #[serde(default)]
    pub expected_roles: Vec<String>,
    /// Require parity-critical semantic operations to carry progress contracts.
    #[serde(default = "default_true")]
    pub parity_progress_contracts: bool,
    /// Require effect/export state to remain exact-once and internally unique.
    #[serde(default = "default_true")]
    pub exact_once_effect_resolution: bool,
    /// Require publication ids to remain canonical and unique.
    #[serde(default = "default_true")]
    pub canonical_publication_uniqueness: bool,
    /// Require observed reads to stay rejected on authoritative paths.
    #[serde(default = "default_true")]
    pub authoritative_observed_separation: bool,
    /// Require blocked/degraded/timed-out progress states to remain replay-visible.
    #[serde(default = "default_true")]
    pub progress_escalation_visibility: bool,
    /// Require semantic objects to remain coherent across handoff/publication/handle surfaces.
    #[serde(default = "default_true")]
    pub semantic_object_coherence: bool,
    /// Require these specific progress states when provided.
    #[serde(default)]
    pub expected_progress_states: Vec<ExpectedProgressState>,
    /// Require these specific publications when provided.
    #[serde(default)]
    pub expected_publications: Vec<ExpectedPublication>,
    /// Require these specific handoff owner transitions when provided.
    #[serde(default)]
    pub expected_handoffs: Vec<ExpectedHandoff>,
}

impl Default for ContractCheckConfig {
    fn default() -> Self {
        Self {
            no_property_violations: true,
            replay_coherence: true,
            min_rounds_executed: None,
            expected_roles: Vec::new(),
            parity_progress_contracts: true,
            exact_once_effect_resolution: true,
            canonical_publication_uniqueness: true,
            authoritative_observed_separation: true,
            progress_escalation_visibility: true,
            semantic_object_coherence: true,
            expected_progress_states: Vec::new(),
            expected_publications: Vec::new(),
            expected_handoffs: Vec::new(),
        }
    }
}

/// Contract-check result for one simulator run.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ContractCheckReport {
    /// True when all enabled checks passed.
    pub passed: bool,
    /// Human-readable failure messages.
    pub failures: Vec<String>,
}

impl ContractCheckReport {
    /// Return an empty passing report.
    #[must_use]
    pub fn pass() -> Self {
        Self {
            passed: true,
            failures: Vec::new(),
        }
    }
}

/// Evaluate simulator run contracts and return a structured report.
#[must_use]
pub fn evaluate_contracts(
    result: &ScenarioResult,
    config: &ContractCheckConfig,
) -> ContractCheckReport {
    let mut failures = Vec::new();
    let semantic_objects = &result.replay.semantic_objects;

    if config.no_property_violations && !result.violations.is_empty() {
        failures.push(format!(
            "expected no property violations, got {}",
            result.violations.len()
        ));
    }

    if config.replay_coherence {
        if result.stats.total_obs_events != result.replay.obs_trace.len() {
            failures.push(format!(
                "obs event count mismatch: stats={} replay={}",
                result.stats.total_obs_events,
                result.replay.obs_trace.len()
            ));
        }

        let observed_invokes = result
            .replay
            .obs_trace
            .iter()
            .filter(|event| matches!(event, ObsEvent::Invoked { .. }))
            .count();
        if result.stats.total_invoked_events != observed_invokes {
            failures.push(format!(
                "invoked event count mismatch: stats={} replay={observed_invokes}",
                result.stats.total_invoked_events
            ));
        }

        if result.replay.effect_trace.len() > result.replay.obs_trace.len() {
            failures.push(format!(
                "effect trace longer than observable trace: effect={} obs={}",
                result.replay.effect_trace.len(),
                result.replay.obs_trace.len()
            ));
        }
    }

    if let Some(min_rounds) = config.min_rounds_executed {
        if result.stats.rounds_executed < min_rounds {
            failures.push(format!(
                "rounds executed below minimum: got={} min={min_rounds}",
                result.stats.rounds_executed
            ));
        }
    }

    if !config.expected_roles.is_empty() {
        let present = result
            .trace
            .records
            .iter()
            .map(|record| record.role.as_str())
            .collect::<BTreeSet<_>>();
        for role in &config.expected_roles {
            if !present.contains(role.as_str()) {
                failures.push(format!("missing sampled trace records for role `{role}`"));
            }
        }
    }

    if config.exact_once_effect_resolution {
        let replay_effect_ids = result
            .replay
            .effect_trace
            .iter()
            .map(|entry| entry.effect_id)
            .collect::<Vec<_>>();
        let semantic_effect_ids = semantic_objects
            .outstanding_effects
            .iter()
            .map(|effect| effect.effect_id)
            .collect::<Vec<_>>();

        if replay_effect_ids.len()
            != replay_effect_ids
                .iter()
                .copied()
                .collect::<BTreeSet<_>>()
                .len()
        {
            failures.push("effect trace re-used an effect_id".to_string());
        }
        if semantic_effect_ids.len()
            != semantic_effect_ids
                .iter()
                .copied()
                .collect::<BTreeSet<_>>()
                .len()
        {
            failures.push("semantic objects re-used an effect_id".to_string());
        }
    }

    if config.parity_progress_contracts
        && !semantic_objects.parity_critical_operations_have_progress_contracts()
    {
        failures
            .push("parity-critical semantic operations are missing progress contracts".to_string());
    }
    if config.parity_progress_contracts
        && !semantic_objects.parity_critical_operations_have_canonical_handles()
    {
        failures.push(
            "parity-critical semantic operations are missing explicit canonical-handle paths"
                .to_string(),
        );
    }

    if config.canonical_publication_uniqueness {
        let unique_publications = semantic_objects
            .publication_events
            .iter()
            .map(|publication| publication.publication_id.clone())
            .collect::<BTreeSet<_>>();
        if unique_publications.len() != semantic_objects.publication_events.len() {
            failures.push("publication ids were not canonical and unique".to_string());
        }
    }

    if config.authoritative_observed_separation {
        let finalization = semantic_objects.finalization();
        for observed in &semantic_objects.observed_reads {
            if finalization
                .require_authoritative_read(&observed.read_id)
                .is_ok()
            {
                failures.push(format!(
                    "observed read `{}` was accepted as authoritative",
                    observed.read_id
                ));
            }
            if !finalization.observed_read_is_noncanonical(&observed.read_id) {
                failures.push(format!(
                    "observed read `{}` reached canonical truth without explicit materialization",
                    observed.read_id
                ));
            }
        }
        for authoritative in &semantic_objects.authoritative_reads {
            if finalization
                .require_authoritative_read(&authoritative.read_id)
                .is_err()
            {
                failures.push(format!(
                    "authoritative read `{}` was not retrievable from semantic objects",
                    authoritative.read_id
                ));
            }
        }
    }

    if config.progress_escalation_visibility {
        for contract in &semantic_objects.progress_contracts {
            if !matches!(
                contract.state,
                ProgressState::Blocked
                    | ProgressState::NoProgress
                    | ProgressState::Degraded
                    | ProgressState::TimedOut
            ) {
                continue;
            }
            if !semantic_objects
                .progress_transitions
                .iter()
                .any(|transition| {
                    transition.operation_id == contract.operation_id
                        && transition.to_state == contract.state
                })
            {
                failures.push(format!(
                    "progress escalation for operation `{}` in state `{}` was not replay-visible",
                    contract.operation_id,
                    progress_state_name(contract.state)
                ));
            }
        }
    }

    if config.semantic_object_coherence {
        check_semantic_object_coherence(semantic_objects, &mut failures);
    }

    for expected in &config.expected_progress_states {
        let Some(contract) = semantic_objects
            .progress_contracts
            .iter()
            .find(|contract| contract.operation_id == expected.operation_id)
        else {
            failures.push(format!(
                "missing expected progress contract for operation `{}`",
                expected.operation_id
            ));
            continue;
        };
        let actual = progress_state_name(contract.state);
        if actual != expected.state {
            failures.push(format!(
                "progress state mismatch for `{}`: expected `{}` got `{actual}`",
                expected.operation_id, expected.state
            ));
        }
    }

    for expected in &config.expected_publications {
        let Some(publication) = semantic_objects
            .publication_events
            .iter()
            .find(|publication| {
                publication.operation_id == expected.operation_id
                    && publication.publication == expected.publication
            })
        else {
            failures.push(format!(
                "missing expected publication `{}` for operation `{}`",
                expected.publication, expected.operation_id
            ));
            continue;
        };
        let actual = publication_status_name(publication.status);
        if actual != expected.status {
            failures.push(format!(
                "publication status mismatch for `{}` on `{}`: expected `{}` got `{actual}`",
                expected.publication, expected.operation_id, expected.status
            ));
        }
    }

    for expected in &config.expected_handoffs {
        if !semantic_objects.semantic_handoffs.iter().any(|handoff| {
            handoff.revoked_owner_id == expected.revoked_owner_id
                && handoff.activated_owner_id == expected.activated_owner_id
        }) {
            failures.push(format!(
                "missing expected semantic handoff {} -> {}",
                expected.revoked_owner_id, expected.activated_owner_id
            ));
        }
    }

    ContractCheckReport {
        passed: failures.is_empty(),
        failures,
    }
}

fn check_semantic_object_coherence(
    semantic_objects: &ProtocolMachineSemanticObjects,
    failures: &mut Vec<String>,
) {
    for handoff in &semantic_objects.semantic_handoffs {
        if handoff.revoked_owner_id == handoff.activated_owner_id {
            failures.push(format!(
                "semantic handoff `{}` did not revoke and activate distinct owners",
                handoff.handoff_id
            ));
        }

        let operation_id = format!("handoff:{}", handoff.handoff_id);
        if !semantic_objects.progress_contracts.iter().any(|contract| {
            contract.operation_id == operation_id && contract.state == ProgressState::HandedOff
        }) {
            failures.push(format!(
                "semantic handoff `{}` is missing a handed-off progress contract",
                handoff.handoff_id
            ));
        }
        if !semantic_objects
            .canonical_handles
            .iter()
            .any(|handle| handle.handle_id == format!("handoff:{}", handoff.handoff_id))
        {
            failures.push(format!(
                "semantic handoff `{}` is missing a canonical handoff handle",
                handoff.handoff_id
            ));
        }
        if !semantic_objects
            .publication_events
            .iter()
            .any(|publication| {
                publication.operation_id == operation_id
                    && publication.publication == "handoff.committed"
                    && publication.status == PublicationStatus::Published
            })
        {
            failures.push(format!(
                "semantic handoff `{}` is missing a canonical publication",
                handoff.handoff_id
            ));
        }
        if !semantic_objects
            .transformation_obligations
            .iter()
            .any(|obligation| obligation.handoff_id == handoff.handoff_id)
        {
            failures.push(format!(
                "semantic handoff `{}` is missing a transformation obligation bundle",
                handoff.handoff_id
            ));
        }
    }

    for publication in &semantic_objects.publication_events {
        if publication.status != PublicationStatus::Published {
            continue;
        }
        if publication.proof_ref.is_some() && publication.handle_ref.is_none() {
            failures.push(format!(
                "publication `{}` is proof-backed but missing a canonical handle",
                publication.publication_id
            ));
        }
    }

    for operation in &semantic_objects.operation_instances {
        if !operation.requires_explicit_finalization() {
            continue;
        }
        let path = semantic_objects
            .finalization()
            .path_for_operation(operation);
        if matches!(path.stage, telltale_machine::FinalizationStage::Observed) {
            failures.push(format!(
                "parity-critical operation `{}` remained on an observed-only path",
                operation.operation_id
            ));
        }
    }
}

/// Assert simulator run contracts and return a single error string on failure.
///
/// # Errors
///
/// Returns an error if any enabled contract check fails.
pub fn assert_contracts(
    result: &ScenarioResult,
    config: &ContractCheckConfig,
) -> Result<(), String> {
    let report = evaluate_contracts(result, config);
    if report.passed {
        return Ok(());
    }
    Err(report.failures.join("; "))
}
