//! Material-model effect handlers and constructor helpers.

pub mod continuum;
pub mod hamiltonian;
pub mod ising;

pub use continuum::ContinuumFieldHandler;
pub use hamiltonian::HamiltonianHandler;
pub use ising::IsingHandler;

use crate::material::{MaterialModel, MaterialParams};
use telltale_machine::model::effects::EffectHandler;

/// Build a handler from any material-model implementation.
#[must_use]
pub fn handler_from_model(material: &dyn MaterialModel) -> Box<dyn EffectHandler> {
    material.build_handler()
}

/// Build a material-specific handler from scenario material parameters.
#[must_use]
pub fn handler_from_material(material: &MaterialParams) -> Box<dyn EffectHandler> {
    handler_from_model(material)
}
