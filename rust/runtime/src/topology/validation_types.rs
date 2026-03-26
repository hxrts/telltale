use std::fmt;

use super::{RoleName, TopologyConstraint, TopologyParseError};

/// Errors that can occur when loading a topology file.
#[derive(Debug, Clone)]
pub enum TopologyLoadError {
    /// IO error reading the file.
    IoError(String),
    /// Parse error in the topology DSL.
    ParseError(TopologyParseError),
}

impl std::fmt::Display for TopologyLoadError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TopologyLoadError::IoError(e) => write!(f, "IO error: {}", e),
            TopologyLoadError::ParseError(e) => write!(f, "Parse error: {}", e),
        }
    }
}

impl std::error::Error for TopologyLoadError {}

/// Result of topology validation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TopologyValidation {
    /// Topology is valid.
    Valid,
    /// A role referenced in topology doesn't exist in choreography.
    UnknownRole(RoleName),
    /// A constraint is violated (with reason).
    ConstraintViolation(TopologyConstraint, String),
    /// Channel capacity is insufficient for a branching requirement.
    InsufficientCapacity {
        sender: RoleName,
        receiver: RoleName,
        required_bits: u32,
        available_bits: u32,
    },
}

/// Errors that can occur when querying topology data.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TopologyError {
    /// Requested role is not present in the topology.
    UnknownRole(RoleName),
}

impl fmt::Display for TopologyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TopologyError::UnknownRole(role) => write!(f, "unknown role: {}", role),
        }
    }
}

impl std::error::Error for TopologyError {}

impl TopologyValidation {
    /// Check if validation passed.
    pub fn is_valid(&self) -> bool {
        matches!(self, TopologyValidation::Valid)
    }
}
