//! Field-model effect handlers and constructor helpers.

pub mod continuum;
pub mod hamiltonian;
pub mod ising;

pub use continuum::ContinuumFieldHandler;
pub use hamiltonian::HamiltonianHandler;
pub use ising::IsingHandler;

use crate::field::{FieldModel, FieldSpec};
use telltale_machine::model::effects::EffectHandler;

/// Build a handler from any field-model implementation.
#[must_use]
pub fn handler_from_field_model(field: &dyn FieldModel) -> Box<dyn EffectHandler> {
    field.build_handler()
}

/// Build a field-specific handler from scenario field parameters.
#[must_use]
pub fn handler_from_field(field: &FieldSpec) -> Box<dyn EffectHandler> {
    handler_from_field_model(field)
}
