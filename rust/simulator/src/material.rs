//! Material parameter definitions for physical simulation layers.
//!
//! Each material layer (mean-field, Hamiltonian, continuum field) has its own
//! parameter struct. The top-level [`MaterialParams`] enum dispatches to the
//! appropriate variant based on the `"layer"` field in JSON.

use serde::{Deserialize, Serialize};
use telltale_types::FixedQ32;

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
    pub beta: FixedQ32,
    /// Species labels (e.g., `["up", "down"]`).
    pub species: Vec<String>,
    /// Initial concentrations per species. Must sum to 1 and be non-negative.
    pub initial_state: Vec<FixedQ32>,
    /// Euler integration step size.
    pub step_size: FixedQ32,
}

/// Parameters for Hamiltonian 2-body dynamics with harmonic coupling.
///
/// Leapfrog (Störmer-Verlet) integration preserves the symplectic structure.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HamiltonianParams {
    /// Spring constant for harmonic coupling potential V = k/2 * (q_A - q_B)^2.
    pub spring_constant: FixedQ32,
    /// Particle mass.
    pub mass: FixedQ32,
    /// Number of spatial dimensions per particle (1 for this 2-body case).
    pub dimensions: u32,
    /// Initial positions for each role (length = number of roles).
    pub initial_positions: Vec<FixedQ32>,
    /// Initial momenta for each role (length = number of roles).
    pub initial_momenta: Vec<FixedQ32>,
    /// Leapfrog integration step size.
    pub step_size: FixedQ32,
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
    pub coupling: FixedQ32,
    /// Number of field components per site (1 for scalar field).
    pub components: u32,
    /// Initial field values per role (length = number of roles).
    pub initial_fields: Vec<FixedQ32>,
    /// Integration step size.
    pub step_size: FixedQ32,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn eps() -> FixedQ32 {
        FixedQ32::from_ratio(1, 1_000_000).expect("epsilon")
    }

    #[test]
    fn test_mean_field_roundtrip() {
        let beta = FixedQ32::from_ratio(3, 2).expect("1.5");
        let initial_0 = FixedQ32::from_ratio(6, 10).expect("0.6");
        let initial_1 = FixedQ32::from_ratio(4, 10).expect("0.4");
        let step = FixedQ32::from_ratio(1, 100).expect("0.01");

        let params = MaterialParams::MeanField(MeanFieldParams {
            beta,
            species: vec!["up".into(), "down".into()],
            initial_state: vec![initial_0, initial_1],
            step_size: step,
        });

        let json = serde_json::to_string(&params).expect("serialize");
        let parsed: MaterialParams = serde_json::from_str(&json).expect("deserialize");

        match parsed {
            MaterialParams::MeanField(mf) => {
                assert!((mf.beta - beta).abs() < eps());
                assert_eq!(mf.species, vec!["up", "down"]);
                assert_eq!(mf.initial_state.len(), 2);
                assert!((mf.step_size - step).abs() < eps());
            }
            _ => panic!("expected MeanField"),
        }
    }

    #[test]
    fn test_mean_field_from_json() {
        let json = r#"{
            "layer": "mean_field",
            "params": {
                "beta": 6442450944,
                "species": ["up", "down"],
                "initial_state": [2576980378, 1717986918],
                "step_size": 42949673
            }
        }"#;

        let params: MaterialParams = serde_json::from_str(json).expect("parse");
        match params {
            MaterialParams::MeanField(mf) => {
                let expected_beta = FixedQ32::from_ratio(3, 2).expect("1.5");
                assert!((mf.beta - expected_beta).abs() < eps());
                assert_eq!(mf.species.len(), 2);
            }
            _ => panic!("expected MeanField"),
        }
    }
}
