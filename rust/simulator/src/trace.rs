//! Trace collection and output for simulation runs.
//!
//! Records per-role state snapshots at each simulation step.

use serde::{Deserialize, Serialize};

/// A single step record for one role.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StepRecord {
    /// Simulation step index.
    pub step: usize,
    /// Role name.
    pub role: String,
    /// State vector after this step.
    pub state: Vec<f64>,
}

/// Collected trace from a simulation run.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct Trace {
    /// All recorded step records.
    pub records: Vec<StepRecord>,
}

impl Trace {
    /// Create an empty trace.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Record a step.
    pub fn record(&mut self, record: StepRecord) {
        self.records.push(record);
    }

    /// Get all records for a specific role.
    #[must_use]
    pub fn records_for_role(&self, role: &str) -> Vec<&StepRecord> {
        self.records.iter().filter(|r| r.role == role).collect()
    }

    /// Get the final state for a role.
    #[must_use]
    pub fn final_state(&self, role: &str) -> Option<&[f64]> {
        self.records
            .iter()
            .rev()
            .find(|r| r.role == role)
            .map(|r| r.state.as_slice())
    }
}
