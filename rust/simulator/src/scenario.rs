//! TOML scenario format for simulation runs.
//!
//! A scenario specifies the roles, material layer, parameters, step count,
//! and output configuration for a simulation.

use serde::{Deserialize, Serialize};
use std::path::Path;

use crate::material::MaterialParams;

/// A simulation scenario loaded from TOML.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Scenario {
    /// Scenario metadata.
    pub name: String,
    /// Role names participating in the protocol.
    pub roles: Vec<String>,
    /// Number of simulation steps.
    pub steps: usize,
    /// Material parameters.
    pub material: MaterialParams,
    /// Output configuration.
    #[serde(default)]
    pub output: OutputConfig,
}

/// Output configuration for trace writing.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OutputConfig {
    /// Output file path (defaults to stdout if not set).
    pub file: Option<String>,
    /// Output format.
    #[serde(default)]
    pub format: OutputFormat,
}

impl Default for OutputConfig {
    fn default() -> Self {
        Self {
            file: None,
            format: OutputFormat::Json,
        }
    }
}

/// Trace output format.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum OutputFormat {
    /// JSON array of step records.
    #[default]
    Json,
    /// JSON lines (one record per line).
    Jsonl,
}

impl Scenario {
    /// Load a scenario from a TOML file.
    ///
    /// # Errors
    ///
    /// Returns an error if the file cannot be read or parsed.
    pub fn from_file(path: &Path) -> Result<Self, String> {
        let content =
            std::fs::read_to_string(path).map_err(|e| format!("read {}: {e}", path.display()))?;
        Self::parse(&content)
    }

    /// Parse a scenario from a TOML string.
    ///
    /// # Errors
    ///
    /// Returns an error if parsing fails.
    pub fn parse(s: &str) -> Result<Self, String> {
        toml::from_str(s).map_err(|e| format!("parse TOML: {e}"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_mean_field_scenario() {
        let toml = r#"
            name = "mean_field_ising"
            roles = ["A", "B"]
            steps = 1000

            [material]
            layer = "mean_field"

            [material.params]
            beta = 1.5
            species = ["up", "down"]
            initial_state = [0.6, 0.4]
            step_size = 0.01

            [output]
            format = "jsonl"
        "#;

        let scenario = Scenario::parse(toml).expect("parse scenario");
        assert_eq!(scenario.name, "mean_field_ising");
        assert_eq!(scenario.roles, vec!["A", "B"]);
        assert_eq!(scenario.steps, 1000);
        match &scenario.material {
            MaterialParams::MeanField(mf) => {
                assert!((mf.beta - 1.5).abs() < f64::EPSILON);
            }
            MaterialParams::Hamiltonian(_) => panic!("expected MeanField"),
        }
    }
}
