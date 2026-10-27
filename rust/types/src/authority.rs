//! Canonical typed readiness evidence data.
//!
//! This data is not a live ownership capability. Construction, cloning and
//! deserialization do not register a witness or authorize its consumption.
//! The original machine session registry validates issuance, exact payload,
//! live owner/generation/scope and single use at the actual commit boundary.

use serde::{Deserialize, Serialize};
use std::collections::BTreeSet;

/// Current authority carried by a live ownership capability.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum OwnershipScope {
    /// Full-session authority.
    Session,
    /// Fragment/boundary-scoped authority.
    Fragments(BTreeSet<String>),
}

impl OwnershipScope {
    /// Whether this scope grants no authority beyond the current scope.
    #[must_use]
    pub fn is_attenuation_of(&self, current: &Self) -> bool {
        match (self, current) {
            (_, Self::Session) => true,
            (Self::Fragments(next), Self::Fragments(previous)) => next.is_subset(previous),
            (Self::Session, Self::Fragments(_)) => false,
        }
    }

    /// Whether this scope authorizes full-session host mutation.
    #[must_use]
    pub fn allows_session_mutation(&self) -> bool {
        matches!(self, Self::Session)
    }
}

/// Witness proving a protocol-critical readiness check succeeded under the
/// current owner capability.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReadinessWitness {
    /// Unique witness identifier within one session.
    pub witness_id: u64,
    /// Session whose readiness was proven.
    pub session_id: usize,
    /// Owner label that requested the witness.
    pub owner_id: String,
    /// Owner generation that must still be live when the witness is consumed.
    pub generation: u64,
    /// Scope under which the witness was issued.
    pub scope: OwnershipScope,
    /// Predicate/check reference justified by this witness.
    pub predicate_ref: String,
}
