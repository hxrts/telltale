//! Material parameter definitions for physical simulation layers.
//!
//! Each material layer (mean-field, Hamiltonian, continuum field) has its own
//! parameter struct. The top-level [`MaterialParams`] enum dispatches to the
//! appropriate variant based on the `"layer"` field in JSON.

use serde::{Deserialize, Serialize};

/// Material parameters for all supported simulation layers.
///
/// JSON format:
/// ```json
/// {
///   "layer": "mean_field",
///   "params": { "beta": 1.5, "species": ["up", "down"], ... }
/// }
/// ```
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "layer", content = "params")]
pub enum MaterialParams {
    /// Mean-field Ising model parameters.
    #[serde(rename = "mean_field")]
    MeanField(MeanFieldParams),

    /// Hamiltonian 2-body dynamics parameters.
    #[serde(rename = "hamiltonian")]
    Hamiltonian(HamiltonianParams),

    /// Continuum field (two-site discretization) parameters.
    #[serde(rename = "continuum_field")]
    ContinuumField(ContinuumFieldParams),
}

/// Parameters for the mean-field Ising model.
///
/// The drift function is `tanh(beta * magnetization)` with Euler integration.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MeanFieldParams {
    /// Inverse temperature. Phase transition at `beta = 1`.
    pub beta: f64,
    /// Species labels (e.g., `["up", "down"]`).
    pub species: Vec<String>,
    /// Initial concentrations per species. Must sum to 1 and be non-negative.
    pub initial_state: Vec<f64>,
    /// Euler integration step size.
    pub step_size: f64,
}

/// Parameters for Hamiltonian 2-body dynamics with harmonic coupling.
///
/// Leapfrog (Störmer-Verlet) integration preserves the symplectic structure.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HamiltonianParams {
    /// Spring constant for harmonic coupling potential V = k/2 * (q_A - q_B)^2.
    pub spring_constant: f64,
    /// Particle mass.
    pub mass: f64,
    /// Number of spatial dimensions per particle (1 for this 2-body case).
    pub dimensions: u32,
    /// Initial positions for each role (length = number of roles).
    pub initial_positions: Vec<f64>,
    /// Initial momenta for each role (length = number of roles).
    pub initial_momenta: Vec<f64>,
    /// Leapfrog integration step size.
    pub step_size: f64,
}

/// Parameters for continuum field dynamics on a two-site discretization.
///
/// Two sites exchange field values through a diffusion kernel K.
/// The nonlocal operator at each site is:
///   drift_i = K * (field_peer - field_self)
/// where K is the coupling strength (kernel weight).
///
/// State vector per role: `[field_value]` (scalar field at each site).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ContinuumFieldParams {
    /// Kernel coupling strength K. Controls diffusion rate between sites.
    pub coupling: f64,
    /// Number of field components per site (1 for scalar field).
    pub components: u32,
    /// Initial field values per role (length = number of roles).
    pub initial_fields: Vec<f64>,
    /// Integration step size.
    pub step_size: f64,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mean_field_roundtrip() {
        let params = MaterialParams::MeanField(MeanFieldParams {
            beta: 1.5,
            species: vec!["up".into(), "down".into()],
            initial_state: vec![0.6, 0.4],
            step_size: 0.01,
        });

        let json = serde_json::to_string(&params).expect("serialize");
        let parsed: MaterialParams = serde_json::from_str(&json).expect("deserialize");

        match parsed {
            MaterialParams::MeanField(mf) => {
                assert!((mf.beta - 1.5).abs() < f64::EPSILON);
                assert_eq!(mf.species, vec!["up", "down"]);
                assert_eq!(mf.initial_state, vec![0.6, 0.4]);
                assert!((mf.step_size - 0.01).abs() < f64::EPSILON);
            }
            _ => panic!("expected MeanField"),
        }
    }

    #[test]
    fn test_mean_field_from_json() {
        let json = r#"{
            "layer": "mean_field",
            "params": {
                "beta": 1.5,
                "species": ["up", "down"],
                "initial_state": [0.6, 0.4],
                "step_size": 0.01
            }
        }"#;

        let params: MaterialParams = serde_json::from_str(json).expect("parse");
        match params {
            MaterialParams::MeanField(mf) => {
                assert!((mf.beta - 1.5).abs() < f64::EPSILON);
                assert_eq!(mf.species.len(), 2);
            }
            _ => panic!("expected MeanField"),
        }
    }
}
