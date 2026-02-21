//! Contract checks for simulator runs.
//!
//! These checks give integrators a stable way to assert that a run produced
//! replay-ready artifacts and respected expected runtime invariants.

use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};
use telltale_vm::vm::ObsEvent;

use crate::runner::ScenarioResult;

fn default_true() -> bool {
    true
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
    /// Require at least this many VM rounds to execute.
    #[serde(default)]
    pub min_rounds_executed: Option<u64>,
    /// Require at least one sampled state for each listed role.
    #[serde(default)]
    pub expected_roles: Vec<String>,
}

impl Default for ContractCheckConfig {
    fn default() -> Self {
        Self {
            no_property_violations: true,
            replay_coherence: true,
            min_rounds_executed: None,
            expected_roles: Vec::new(),
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

    ContractCheckReport {
        passed: failures.is_empty(),
        failures,
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
