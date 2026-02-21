//! Material-model effect handlers and constructor helpers.

pub mod continuum;
pub mod hamiltonian;
pub mod ising;

pub use continuum::ContinuumFieldHandler;
pub use hamiltonian::HamiltonianHandler;
pub use ising::IsingHandler;

use crate::material::MaterialParams;
use telltale_vm::effect::EffectHandler;

/// Build a material-specific handler from scenario material parameters.
#[must_use]
pub fn handler_from_material(material: &MaterialParams) -> Box<dyn EffectHandler> {
    match material {
        MaterialParams::MeanField(params) => Box::new(IsingHandler::new(params.clone())),
        MaterialParams::Hamiltonian(params) => Box::new(HamiltonianHandler::new(params.clone())),
        MaterialParams::ContinuumField(params) => {
            Box::new(ContinuumFieldHandler::new(params.clone()))
        }
    }
}
