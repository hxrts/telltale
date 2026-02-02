//! Post-hoc validation checks for simulation traces.
//!
//! Checks conservation (probability sum = 1), convergence (distance to
//! equilibrium decreases), and simplex invariance (all non-negative).

use crate::trace::Trace;

/// Tolerance for floating-point comparisons.
const TOLERANCE: f64 = 1e-8;

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
    for record in &trace.records {
        let sum: f64 = record.state.iter().sum();
        if (sum - 1.0).abs() > TOLERANCE {
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
    for record in &trace.records {
        for (i, &x) in record.state.iter().enumerate() {
            if x < -TOLERANCE {
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
pub fn check_convergence(trace: &Trace, role: &str, equilibrium: &[f64]) -> CheckResult {
    let records = trace.records_for_role(role);
    if records.len() < 2 {
        return CheckResult {
            name: "convergence".into(),
            passed: true,
            message: "too few steps to check convergence".into(),
        };
    }

    let distance = |state: &[f64]| -> f64 {
        state
            .iter()
            .zip(equilibrium.iter())
            .map(|(a, b)| (a - b).powi(2))
            .sum::<f64>()
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
    mass: f64,
    spring_constant: f64,
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

    let energy = |a: &[f64], b: &[f64]| -> f64 {
        let ke = a[1].powi(2) / (2.0 * mass) + b[1].powi(2) / (2.0 * mass);
        let pe = spring_constant / 2.0 * (a[0] - b[0]).powi(2);
        ke + pe
    };

    let initial_e = energy(&records_a[0].state, &records_b[0].state);
    let mut max_drift: f64 = 0.0;

    for (ra, rb) in records_a.iter().zip(records_b.iter()) {
        let e = energy(&ra.state, &rb.state);
        let drift = (e - initial_e).abs() / initial_e.max(1e-15);
        max_drift = max_drift.max(drift);
    }

    // Tolerance accounts for communication-lag-induced drift in distributed
    // Hamiltonian simulations where roles exchange positions asynchronously.
    if max_drift < 0.15 {
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
pub fn validate(trace: &Trace, roles: &[&str], equilibrium: &[f64]) -> ValidationResult {
    let mut checks = vec![check_conservation(trace), check_simplex(trace)];

    for role in roles {
        checks.push(check_convergence(trace, role, equilibrium));
    }

    let passed = checks.iter().all(|c| c.passed);
    ValidationResult { passed, checks }
}
