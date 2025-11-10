// Choreography struct definition and validation

use super::{Role, Protocol, ValidationError};
use proc_macro2::Ident;
use std::collections::HashMap;

/// A complete choreographic protocol specification
#[derive(Debug, Clone)]
pub struct Choreography {
    /// Protocol name
    pub name: Ident,
    /// Participating roles
    pub roles: Vec<Role>,
    /// The protocol specification
    pub protocol: Protocol,
    /// Metadata and attributes
    pub attrs: HashMap<String, String>,
}

impl Choreography {
    /// Validate the choreography for correctness
    pub fn validate(&self) -> Result<(), ValidationError> {
        // Check all roles are used
        for role in &self.roles {
            if !self.protocol.mentions_role(role) {
                return Err(ValidationError::UnusedRole(role.name.to_string()));
            }
        }

        // Check protocol is well-formed
        self.protocol.validate(&self.roles)?;

        Ok(())
    }
}
