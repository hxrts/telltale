//! Field-model interfaces and built-in field/environment-dynamics parameters.
//!
//! [`FieldModel`] is the simulator-facing abstraction for deterministic
//! field/environment dynamics. [`FieldSpec`] is the built-in serde-tagged
//! catalog used by the base scenario schema.

use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use telltale_types::FixedQ32;

use crate::field_handlers::{ContinuumFieldHandler, HamiltonianHandler, IsingHandler};
use telltale_machine::model::effects::EffectHandler;

/// Simulator-facing abstraction for deterministic field/environment dynamics.
///
/// This layer is responsible for evolving shared fields, latent environment
/// state, or node-local physical state. It does not own the full topology,
/// medium, mobility, or admission stack by itself.
pub trait FieldModel: Send + Sync {
    /// Stable identifier for diagnostics and registry-style dispatch.
    fn field_name(&self) -> &'static str;

    /// Construct the effect handler for this field model.
    fn build_handler(&self) -> Box<dyn EffectHandler>;

    /// Derive initial per-role register state for a given role ordering.
    ///
    /// # Errors
    ///
    /// Returns an error when the model parameters are incompatible with the
    /// supplied role list.
    fn derive_initial_states(
        &self,
        roles: &[String],
    ) -> Result<BTreeMap<String, Vec<FixedQ32>>, String>;
}

/// Built-in field/environment-dynamics catalog.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "layer", content = "params")]
pub enum FieldSpec {
    /// Mean-field Ising model parameters.
    #[serde(rename = "mean_field")]
    MeanField(MeanFieldSpec),

    /// Hamiltonian 2-body dynamics parameters.
    #[serde(rename = "hamiltonian")]
    Hamiltonian(HamiltonianFieldSpec),

    /// Continuum field (two-site discretization) parameters.
    #[serde(rename = "continuum_field")]
    ContinuumField(ContinuumFieldSpec),
}

/// Parameters for the mean-field Ising model.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MeanFieldSpec {
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
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HamiltonianFieldSpec {
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
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ContinuumFieldSpec {
    /// Kernel coupling strength K. Controls diffusion rate between sites.
    pub coupling: FixedQ32,
    /// Number of field components per site (1 for scalar field).
    pub components: u32,
    /// Initial field values per role (length = number of roles).
    pub initial_fields: Vec<FixedQ32>,
    /// Integration step size.
    pub step_size: FixedQ32,
}

impl FieldModel for MeanFieldSpec {
    fn field_name(&self) -> &'static str {
        "mean_field"
    }

    fn build_handler(&self) -> Box<dyn EffectHandler> {
        Box::new(IsingHandler::new(self.clone()))
    }

    fn derive_initial_states(
        &self,
        roles: &[String],
    ) -> Result<BTreeMap<String, Vec<FixedQ32>>, String> {
        if self.initial_state.is_empty() {
            return Err("mean_field field layer requires at least one state component".into());
        }

        Ok(roles
            .iter()
            .cloned()
            .map(|role| (role, self.initial_state.clone()))
            .collect())
    }
}

impl FieldModel for HamiltonianFieldSpec {
    fn field_name(&self) -> &'static str {
        "hamiltonian"
    }

    fn build_handler(&self) -> Box<dyn EffectHandler> {
        Box::new(HamiltonianHandler::new(self.clone()))
    }

    fn derive_initial_states(
        &self,
        roles: &[String],
    ) -> Result<BTreeMap<String, Vec<FixedQ32>>, String> {
        let n = roles.len();
        if self.initial_positions.len() < n || self.initial_momenta.len() < n {
            return Err(format!(
                "hamiltonian field layer requires at least {n} positions and momenta"
            ));
        }

        Ok(roles
            .iter()
            .cloned()
            .enumerate()
            .map(|(idx, role)| {
                (
                    role,
                    vec![self.initial_positions[idx], self.initial_momenta[idx]],
                )
            })
            .collect())
    }
}

impl FieldModel for ContinuumFieldSpec {
    fn field_name(&self) -> &'static str {
        "continuum_field"
    }

    fn build_handler(&self) -> Box<dyn EffectHandler> {
        Box::new(ContinuumFieldHandler::new(self.clone()))
    }

    fn derive_initial_states(
        &self,
        roles: &[String],
    ) -> Result<BTreeMap<String, Vec<FixedQ32>>, String> {
        let n = roles.len();
        if self.initial_fields.len() < n {
            return Err(format!(
                "continuum_field field layer requires at least {n} initial field values"
            ));
        }

        Ok(roles
            .iter()
            .cloned()
            .enumerate()
            .map(|(idx, role)| (role, vec![self.initial_fields[idx]]))
            .collect())
    }
}

impl FieldModel for FieldSpec {
    fn field_name(&self) -> &'static str {
        match self {
            Self::MeanField(spec) => spec.field_name(),
            Self::Hamiltonian(spec) => spec.field_name(),
            Self::ContinuumField(spec) => spec.field_name(),
        }
    }

    fn build_handler(&self) -> Box<dyn EffectHandler> {
        match self {
            Self::MeanField(spec) => spec.build_handler(),
            Self::Hamiltonian(spec) => spec.build_handler(),
            Self::ContinuumField(spec) => spec.build_handler(),
        }
    }

    fn derive_initial_states(
        &self,
        roles: &[String],
    ) -> Result<BTreeMap<String, Vec<FixedQ32>>, String> {
        match self {
            Self::MeanField(spec) => spec.derive_initial_states(roles),
            Self::Hamiltonian(spec) => spec.derive_initial_states(roles),
            Self::ContinuumField(spec) => spec.derive_initial_states(roles),
        }
    }
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

        let spec = FieldSpec::MeanField(MeanFieldSpec {
            beta,
            species: vec!["up".into(), "down".into()],
            initial_state: vec![initial_0, initial_1],
            step_size: step,
        });

        let json = serde_json::to_string(&spec).expect("serialize");
        let parsed: FieldSpec = serde_json::from_str(&json).expect("deserialize");

        match parsed {
            FieldSpec::MeanField(mf) => {
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

        let spec: FieldSpec = serde_json::from_str(json).expect("parse");
        match spec {
            FieldSpec::MeanField(mf) => {
                let expected_beta = FixedQ32::from_ratio(3, 2).expect("1.5");
                assert!((mf.beta - expected_beta).abs() < eps());
                assert_eq!(mf.species.len(), 2);
            }
            _ => panic!("expected MeanField"),
        }
    }

    #[test]
    fn field_model_dispatch_derives_states_for_builtin_catalog() {
        let spec = FieldSpec::Hamiltonian(HamiltonianFieldSpec {
            spring_constant: FixedQ32::one(),
            mass: FixedQ32::one(),
            dimensions: 1,
            initial_positions: vec![FixedQ32::one(), FixedQ32::neg_one()],
            initial_momenta: vec![FixedQ32::zero(), FixedQ32::zero()],
            step_size: FixedQ32::from_ratio(1, 100).expect("0.01"),
        });

        let states = spec
            .derive_initial_states(&["A".into(), "B".into()])
            .expect("derive states");

        assert_eq!(spec.field_name(), "hamiltonian");
        assert_eq!(states["A"], vec![FixedQ32::one(), FixedQ32::zero()]);
        assert_eq!(states["B"], vec![FixedQ32::neg_one(), FixedQ32::zero()]);
    }
}
