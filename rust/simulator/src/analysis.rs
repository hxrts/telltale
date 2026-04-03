//! Post-hoc validation checks for simulation traces.
//!
//! Checks conservation (probability sum = 1), convergence (distance to
//! equilibrium decreases), simplex invariance (all non-negative), and
//! normalized observability classes for envelope-aware comparison.

use crate::reconfiguration::{
    ReconfigurationAction, ReconfigurationEffect, ReconfigurationFootprint, ReconfigurationRecord,
};
use crate::trace::Trace;
use serde::{Deserialize, Serialize};
use telltale_machine::trace::normalize_trace;
use telltale_machine::ObsEvent;
use telltale_types::FixedQ32;

/// Tolerance for fixed-point comparisons (approximately 1e-8).
fn tolerance() -> FixedQ32 {
    FixedQ32::from_ratio(1, 100_000_000).expect("tolerance must be representable")
}

/// Result of running validation checks on a trace.
#[derive(Debug)]
pub struct ValidationResult {
    /// Whether all checks passed.
    pub passed: bool,
    /// Individual check results.
    pub checks: Vec<CheckResult>,
}

/// Result of a single validation check.
#[derive(Debug)]
pub struct CheckResult {
    /// Check name.
    pub name: String,
    /// Whether the check passed.
    pub passed: bool,
    /// Description of the result.
    pub message: String,
}

/// Validate that probability sums equal 1 at every step for every role.
#[must_use]
pub fn check_conservation(trace: &Trace) -> CheckResult {
    let one = FixedQ32::one();
    let tol = tolerance();
    for record in &trace.records {
        let sum: FixedQ32 = record.state.iter().sum();
        if (sum - one).abs() > tol {
            return CheckResult {
                name: "conservation".into(),
                passed: false,
                message: format!(
                    "step {} role {}: sum = {sum} (expected 1.0)",
                    record.step, record.role
                ),
            };
        }
    }
    CheckResult {
        name: "conservation".into(),
        passed: true,
        message: "probability sum = 1 at all steps".into(),
    }
}

/// Validate that all concentrations are non-negative at every step.
#[must_use]
pub fn check_simplex(trace: &Trace) -> CheckResult {
    let neg_tol = -tolerance();
    for record in &trace.records {
        for (i, &x) in record.state.iter().enumerate() {
            if x < neg_tol {
                return CheckResult {
                    name: "simplex".into(),
                    passed: false,
                    message: format!(
                        "step {} role {}: state[{i}] = {x} (negative)",
                        record.step, record.role
                    ),
                };
            }
        }
    }
    CheckResult {
        name: "simplex".into(),
        passed: true,
        message: "all concentrations non-negative".into(),
    }
}

/// Validate that distance to equilibrium decreases over time for a given role.
///
/// The equilibrium for subcritical mean-field Ising (`beta < 1`) is `[0.5, 0.5]`.
#[must_use]
pub fn check_convergence(trace: &Trace, role: &str, equilibrium: &[FixedQ32]) -> CheckResult {
    let records = trace.records_for_role(role);
    if records.len() < 2 {
        return CheckResult {
            name: "convergence".into(),
            passed: true,
            message: "too few steps to check convergence".into(),
        };
    }

    let distance = |state: &[FixedQ32]| -> FixedQ32 {
        state
            .iter()
            .zip(equilibrium.iter())
            .map(|(a, b)| (*a - *b).powi(2))
            .sum::<FixedQ32>()
            .sqrt()
    };

    // Check that final distance is less than initial distance.
    let d_first = distance(&records[0].state);
    let d_last = distance(&records[records.len() - 1].state);

    if d_last < d_first {
        CheckResult {
            name: "convergence".into(),
            passed: true,
            message: format!("distance decreased: {d_first:.6} -> {d_last:.6}"),
        }
    } else {
        CheckResult {
            name: "convergence".into(),
            passed: false,
            message: format!("distance did not decrease: {d_first:.6} -> {d_last:.6}"),
        }
    }
}

/// Validate energy conservation for Hamiltonian traces.
///
/// Energy = sum over roles of (p^2 / 2m) + k/2 * (q_A - q_B)^2.
/// State per role is [position, momentum].
#[must_use]
pub fn check_energy_conservation(
    trace: &Trace,
    roles: &[&str],
    mass: FixedQ32,
    spring_constant: FixedQ32,
) -> CheckResult {
    if roles.len() != 2 {
        return CheckResult {
            name: "energy_conservation".into(),
            passed: false,
            message: "energy check requires exactly 2 roles".into(),
        };
    }

    let records_a = trace.records_for_role(roles[0]);
    let records_b = trace.records_for_role(roles[1]);

    if records_a.is_empty() || records_b.is_empty() {
        return CheckResult {
            name: "energy_conservation".into(),
            passed: true,
            message: "no records to check".into(),
        };
    }

    let two = FixedQ32::from_ratio(2, 1).expect("2 must be representable");
    let energy = |a: &[FixedQ32], b: &[FixedQ32]| -> FixedQ32 {
        let ke = a[1].powi(2) / (two * mass) + b[1].powi(2) / (two * mass);
        let pe = spring_constant / two * (a[0] - b[0]).powi(2);
        ke + pe
    };

    let initial_e = energy(&records_a[0].state, &records_b[0].state);
    let mut max_drift = FixedQ32::zero();
    let epsilon = FixedQ32::from_ratio(1, 1_000_000_000_000).unwrap_or(FixedQ32::one());

    for (ra, rb) in records_a.iter().zip(records_b.iter()) {
        let e = energy(&ra.state, &rb.state);
        let drift = (e - initial_e).abs() / initial_e.max(epsilon);
        max_drift = max_drift.max(drift);
    }

    // Tolerance accounts for communication-lag-induced drift in distributed
    // Hamiltonian simulations where roles exchange positions asynchronously.
    let drift_tolerance = FixedQ32::from_ratio(15, 100).expect("0.15 must be representable");
    if max_drift < drift_tolerance {
        CheckResult {
            name: "energy_conservation".into(),
            passed: true,
            message: format!("max relative energy drift: {max_drift:.6}"),
        }
    } else {
        CheckResult {
            name: "energy_conservation".into(),
            passed: false,
            message: format!("energy drift too large: {max_drift:.6}"),
        }
    }
}

/// Run all standard validation checks on a trace.
#[must_use]
pub fn validate(trace: &Trace, roles: &[&str], equilibrium: &[FixedQ32]) -> ValidationResult {
    let mut checks = vec![check_conservation(trace), check_simplex(trace)];

    for role in roles {
        checks.push(check_convergence(trace, role, equilibrium));
    }

    let passed = checks.iter().all(|c| c.passed);
    ValidationResult { passed, checks }
}

fn default_normalized_observability_schema_version() -> u32 {
    1
}

/// Version identifier for normalized observability payloads.
pub const NORMALIZED_OBSERVABILITY_SCHEMA_VERSION: u32 = 1;

/// Envelope-normalized observability class for one simulator run.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct NormalizedObservability {
    /// Schema version for normalized observability encoding.
    #[serde(default = "default_normalized_observability_schema_version")]
    pub schema_version: u32,
    /// Number of raw observable events that were normalized into this class.
    pub raw_observable_event_count: u64,
    /// Number of raw reconfiguration records that were normalized into this class.
    pub raw_reconfiguration_count: u64,
    /// Order-insensitive normalized observable-event class.
    pub normalized_event_class: Vec<String>,
    /// Order-insensitive normalized reconfiguration class.
    pub normalized_reconfiguration_class: Vec<String>,
}

/// Relationship between two runs after raw and normalized comparison.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ObservabilityRelation {
    /// Raw traces and reconfiguration records match exactly.
    ExactRawMatch,
    /// Raw traces differ, but the normalized classes match.
    EquivalentUnderNormalization,
    /// The runs diverge on safety-visible behavior even after normalization.
    SafetyVisibleDivergence,
}

/// Comparison report for two simulator observability surfaces.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ObservabilityComparison {
    /// Whether the raw observable and reconfiguration traces match exactly.
    pub raw_equal: bool,
    /// Whether the normalized observability classes match.
    pub normalized_equal: bool,
    /// High-level relation between the two runs.
    pub relation: ObservabilityRelation,
}

/// Build an envelope-normalized observability class from raw simulator artifacts.
#[must_use]
pub fn normalized_observability(
    obs_trace: &[ObsEvent],
    reconfiguration_trace: &[ReconfigurationRecord],
) -> NormalizedObservability {
    let mut normalized_event_class = normalize_trace(obs_trace)
        .into_iter()
        .map(|event| serde_json::to_string(&event).expect("observable events must serialize"))
        .collect::<Vec<_>>();
    normalized_event_class.sort();

    let mut normalized_reconfiguration_class = reconfiguration_trace
        .iter()
        .map(normalized_reconfiguration_token)
        .collect::<Vec<_>>();
    normalized_reconfiguration_class.sort();

    NormalizedObservability {
        schema_version: NORMALIZED_OBSERVABILITY_SCHEMA_VERSION,
        raw_observable_event_count: u64::try_from(obs_trace.len()).unwrap_or(u64::MAX),
        raw_reconfiguration_count: u64::try_from(reconfiguration_trace.len()).unwrap_or(u64::MAX),
        normalized_event_class,
        normalized_reconfiguration_class,
    }
}

/// Compare two runs by raw trace identity and envelope-normalized behavior class.
#[must_use]
pub fn compare_observability(
    left_obs: &[ObsEvent],
    left_reconfiguration: &[ReconfigurationRecord],
    left_normalized: &NormalizedObservability,
    right_obs: &[ObsEvent],
    right_reconfiguration: &[ReconfigurationRecord],
    right_normalized: &NormalizedObservability,
) -> ObservabilityComparison {
    let raw_equal = left_obs == right_obs && left_reconfiguration == right_reconfiguration;
    let normalized_equal = left_normalized == right_normalized;
    let relation = if raw_equal {
        ObservabilityRelation::ExactRawMatch
    } else if normalized_equal {
        ObservabilityRelation::EquivalentUnderNormalization
    } else {
        ObservabilityRelation::SafetyVisibleDivergence
    };
    ObservabilityComparison {
        raw_equal,
        normalized_equal,
        relation,
    }
}

fn normalized_reconfiguration_token(record: &ReconfigurationRecord) -> String {
    #[derive(Serialize)]
    struct Token<'a> {
        logical_step: u64,
        action: NormalizedAction<'a>,
        effect: &'a ReconfigurationEffect,
        footprint: &'a ReconfigurationFootprint,
    }

    #[derive(Serialize)]
    #[serde(tag = "type", rename_all = "snake_case")]
    enum NormalizedAction<'a> {
        Link {
            from: &'a str,
            to: &'a str,
            enabled: bool,
            base_latency_ms: Option<u64>,
            latency_variance: Option<FixedQ32>,
            loss_probability: Option<FixedQ32>,
        },
        Delegation {
            scope: &'a str,
            from_role: &'a str,
            to_role: &'a str,
        },
        Handoff {
            handoff_id: &'a str,
            from_role: &'a str,
            to_role: &'a str,
        },
        Federation {
            federation: &'a str,
            enabled: bool,
            groups: &'a [Vec<String>],
        },
        ModeTransition {
            roles: &'a [String],
            from_mode: &'a str,
            to_mode: &'a str,
        },
    }

    let action = match &record.action {
        ReconfigurationAction::Link {
            from,
            to,
            enabled,
            base_latency_ms,
            latency_variance,
            loss_probability,
        } => NormalizedAction::Link {
            from,
            to,
            enabled: *enabled,
            base_latency_ms: *base_latency_ms,
            latency_variance: *latency_variance,
            loss_probability: *loss_probability,
        },
        ReconfigurationAction::Delegation {
            scope,
            from_role,
            to_role,
        } => NormalizedAction::Delegation {
            scope,
            from_role,
            to_role,
        },
        ReconfigurationAction::Handoff {
            handoff_id,
            from_role,
            to_role,
        } => NormalizedAction::Handoff {
            handoff_id,
            from_role,
            to_role,
        },
        ReconfigurationAction::Federation {
            federation,
            enabled,
            groups,
        } => NormalizedAction::Federation {
            federation,
            enabled: *enabled,
            groups,
        },
        ReconfigurationAction::ModeTransition {
            roles,
            from_mode,
            to_mode,
        } => NormalizedAction::ModeTransition {
            roles,
            from_mode,
            to_mode,
        },
    };

    serde_json::to_string(&Token {
        logical_step: record.logical_step,
        action,
        effect: &record.effect,
        footprint: &record.footprint,
    })
    .expect("reconfiguration records must serialize")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn opened(tick: u64, session: usize, roles: &[&str]) -> ObsEvent {
        ObsEvent::Opened {
            tick,
            session,
            roles: roles.iter().map(|role| (*role).to_string()).collect(),
        }
    }

    #[test]
    fn normalization_reports_equivalence_for_order_only_differences() {
        let left = vec![opened(2, 0, &["A", "B"]), opened(1, 1, &["C", "D"])];
        let right = vec![opened(7, 1, &["C", "D"]), opened(9, 0, &["A", "B"])];
        let left_normalized = normalized_observability(&left, &[]);
        let right_normalized = normalized_observability(&right, &[]);

        let comparison =
            compare_observability(&left, &[], &left_normalized, &right, &[], &right_normalized);

        assert!(!comparison.raw_equal);
        assert!(comparison.normalized_equal);
        assert_eq!(
            comparison.relation,
            ObservabilityRelation::EquivalentUnderNormalization
        );
    }

    #[test]
    fn normalization_reports_safety_visible_divergence_for_different_footprints() {
        let base = vec![opened(1, 0, &["A", "B"])];
        let left_reconfiguration = vec![ReconfigurationRecord {
            operation_id: "reconfiguration:0".to_string(),
            tick: 1,
            logical_step: 1,
            action: ReconfigurationAction::Handoff {
                handoff_id: "h1".to_string(),
                from_role: "A".to_string(),
                to_role: "B".to_string(),
            },
            effect: ReconfigurationEffect::default(),
            footprint: ReconfigurationFootprint {
                roles: vec!["A".to_string(), "B".to_string()],
                links: Vec::new(),
            },
        }];
        let right_reconfiguration = vec![ReconfigurationRecord {
            operation_id: "reconfiguration:0".to_string(),
            tick: 1,
            logical_step: 1,
            action: ReconfigurationAction::Handoff {
                handoff_id: "h1".to_string(),
                from_role: "A".to_string(),
                to_role: "C".to_string(),
            },
            effect: ReconfigurationEffect::default(),
            footprint: ReconfigurationFootprint {
                roles: vec!["A".to_string(), "C".to_string()],
                links: Vec::new(),
            },
        }];

        let left_normalized = normalized_observability(&base, &left_reconfiguration);
        let right_normalized = normalized_observability(&base, &right_reconfiguration);
        let comparison = compare_observability(
            &base,
            &left_reconfiguration,
            &left_normalized,
            &base,
            &right_reconfiguration,
            &right_normalized,
        );

        assert!(!comparison.raw_equal);
        assert!(!comparison.normalized_equal);
        assert_eq!(
            comparison.relation,
            ObservabilityRelation::SafetyVisibleDivergence
        );
    }
}
