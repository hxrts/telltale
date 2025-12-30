//! # Topology
//!
//! Location and topology types for deployment configuration.
//!
//! ## Overview
//!
//! This module defines types for specifying where protocol roles are deployed.
//! Topology is kept separate from choreography to enable:
//! - Same choreography, multiple deployment configs
//! - Version topologies independently
//! - Dev/staging/prod without touching protocol logic
//! - Projection correctness is location-independent
//!
//! ## Lean Correspondence
//!
//! This module corresponds to `lean/Rumpsteak/Protocol/Location.lean`:
//! - `Location` ↔ Lean's `Location`
//! - `TopologyConstraint` ↔ Lean's `TopologyConstraint`
//! - `Topology` ↔ Lean's `Topology`
//! - `TopologyMode` ↔ Lean's `TopologyMode`

mod handler;
mod parser;
mod transport;

pub use handler::{TopologyHandler, TopologyHandlerBuilder};
pub use parser::{parse_topology, ParsedTopology, TopologyParseError};
pub use transport::{
    ByteMessage, InMemoryChannelTransport, Transport, TransportError, TransportFactory,
    TransportMessage, TransportResult, TransportType,
};

use std::collections::BTreeMap;
use std::fmt;

/// Location specifies where a role is deployed.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Default)]
pub enum Location {
    /// In-process execution using channels
    #[default]
    Local,
    /// Remote endpoint (e.g., "localhost:8080", "service.internal:9000")
    Remote(String),
    /// Colocated with another role on the same node (shared memory)
    Colocated(String),
}

impl fmt::Display for Location {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Location::Local => write!(f, "local"),
            Location::Remote(endpoint) => write!(f, "{}", endpoint),
            Location::Colocated(peer) => write!(f, "colocated({})", peer),
        }
    }
}

/// Topology constraints specify requirements on role placement.
///
/// These are validated at deployment time, not projection time.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TopologyConstraint {
    /// Two roles must be on the same node
    Colocated(String, String),
    /// Two roles must be on different nodes
    Separated(String, String),
    /// A role must be at a specific location
    Pinned(String, Location),
    /// A role must be in a specific region/zone
    Region(String, String),
}

impl fmt::Display for TopologyConstraint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TopologyConstraint::Colocated(r1, r2) => write!(f, "colocated({}, {})", r1, r2),
            TopologyConstraint::Separated(r1, r2) => write!(f, "separated({}, {})", r1, r2),
            TopologyConstraint::Pinned(role, loc) => write!(f, "pinned({}, {})", role, loc),
            TopologyConstraint::Region(role, region) => write!(f, "region({}, {})", role, region),
        }
    }
}

/// Common deployment modes for quick configuration
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub enum TopologyMode {
    /// All roles in-process (testing)
    #[default]
    Local,
    /// Each role in separate process
    PerRole,
    /// Discover via Kubernetes services
    Kubernetes(String), // namespace
    /// Discover via Consul
    Consul(String), // datacenter
}

/// Topology maps roles to their deployment locations.
///
/// Uses BTreeMap for deterministic iteration order.
#[derive(Debug, Clone, Default)]
pub struct Topology {
    /// Optional mode for shorthand configuration
    pub mode: Option<TopologyMode>,
    /// Role → Location mapping
    pub locations: BTreeMap<String, Location>,
    /// Deployment constraints
    pub constraints: Vec<TopologyConstraint>,
}

impl Topology {
    /// Create an empty topology
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a local-only topology (all roles in-process)
    pub fn local_mode() -> Self {
        Topology {
            mode: Some(TopologyMode::Local),
            ..Default::default()
        }
    }

    /// Create a topology builder
    pub fn builder() -> TopologyBuilder {
        TopologyBuilder::new()
    }

    /// Add a role location to the topology
    pub fn with_role(mut self, role: impl Into<String>, location: Location) -> Self {
        self.locations.insert(role.into(), location);
        self
    }

    /// Add a constraint to the topology
    pub fn with_constraint(mut self, constraint: TopologyConstraint) -> Self {
        self.constraints.push(constraint);
        self
    }

    /// Get the location for a role (defaults to local)
    pub fn get_location(&self, role: &str) -> Location {
        match &self.mode {
            Some(TopologyMode::Local) => Location::Local,
            _ => self.locations.get(role).cloned().unwrap_or(Location::Local),
        }
    }

    /// Check if a role is local
    pub fn is_local(&self, role: &str) -> bool {
        match self.get_location(role) {
            Location::Local | Location::Colocated(_) => true,
            Location::Remote(_) => false,
        }
    }

    /// Get all roles defined in the topology
    pub fn roles(&self) -> Vec<&String> {
        self.locations.keys().collect()
    }

    /// Check if topology is valid for a set of choreography roles.
    /// All referenced roles must exist in the choreography.
    pub fn valid_for_roles(&self, choreo_roles: &[&str]) -> bool {
        // All topology roles must be in choreography
        let topo_roles_ok = self
            .locations
            .keys()
            .all(|r| choreo_roles.contains(&r.as_str()));

        // All constraint roles must be in choreography
        let constraints_ok = self.constraints.iter().all(|c| match c {
            TopologyConstraint::Colocated(r1, r2) | TopologyConstraint::Separated(r1, r2) => {
                choreo_roles.contains(&r1.as_str()) && choreo_roles.contains(&r2.as_str())
            }
            TopologyConstraint::Pinned(r, _) | TopologyConstraint::Region(r, _) => {
                choreo_roles.contains(&r.as_str())
            }
        });

        topo_roles_ok && constraints_ok
    }

    /// Validate a topology against choreography roles
    pub fn validate(&self, choreo_roles: &[&str]) -> TopologyValidation {
        // Check all topology roles exist
        for role in self.locations.keys() {
            if !choreo_roles.contains(&role.as_str()) {
                return TopologyValidation::UnknownRole(role.clone());
            }
        }

        // Check all constraint roles exist
        for c in &self.constraints {
            match c {
                TopologyConstraint::Colocated(r1, r2) | TopologyConstraint::Separated(r1, r2) => {
                    if !choreo_roles.contains(&r1.as_str()) {
                        return TopologyValidation::UnknownRole(r1.clone());
                    }
                    if !choreo_roles.contains(&r2.as_str()) {
                        return TopologyValidation::UnknownRole(r2.clone());
                    }
                }
                TopologyConstraint::Pinned(r, _) | TopologyConstraint::Region(r, _) => {
                    if !choreo_roles.contains(&r.as_str()) {
                        return TopologyValidation::UnknownRole(r.clone());
                    }
                }
            }
        }

        TopologyValidation::Valid
    }

    /// Load a topology from a DSL file.
    ///
    /// # Example
    ///
    /// ```ignore
    /// let topology = Topology::load("deploy/prod.topology")?;
    /// ```
    pub fn load(path: impl AsRef<std::path::Path>) -> Result<ParsedTopology, TopologyLoadError> {
        let content = std::fs::read_to_string(path.as_ref())
            .map_err(|e| TopologyLoadError::IoError(e.to_string()))?;
        parse_topology(&content).map_err(TopologyLoadError::ParseError)
    }

    /// Load a topology from a DSL string.
    pub fn parse(content: &str) -> Result<ParsedTopology, TopologyLoadError> {
        parse_topology(content).map_err(TopologyLoadError::ParseError)
    }
}

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

/// Result of topology validation
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TopologyValidation {
    /// Topology is valid
    Valid,
    /// A role referenced in topology doesn't exist in choreography
    UnknownRole(String),
    /// A constraint is violated (with reason)
    ConstraintViolation(TopologyConstraint, String),
}

impl TopologyValidation {
    /// Check if validation passed
    pub fn is_valid(&self) -> bool {
        matches!(self, TopologyValidation::Valid)
    }
}

/// Builder for constructing Topology instances
#[derive(Debug, Clone, Default)]
pub struct TopologyBuilder {
    topology: Topology,
}

impl TopologyBuilder {
    /// Create a new topology builder
    pub fn new() -> Self {
        Self::default()
    }

    /// Set the topology mode
    pub fn mode(mut self, mode: TopologyMode) -> Self {
        self.topology.mode = Some(mode);
        self
    }

    /// Add a local role
    pub fn local_role(mut self, role: impl Into<String>) -> Self {
        self.topology.locations.insert(role.into(), Location::Local);
        self
    }

    /// Add a remote role
    pub fn remote_role(mut self, role: impl Into<String>, endpoint: impl Into<String>) -> Self {
        self.topology
            .locations
            .insert(role.into(), Location::Remote(endpoint.into()));
        self
    }

    /// Add a colocated role
    pub fn colocated_role(mut self, role: impl Into<String>, peer: impl Into<String>) -> Self {
        self.topology
            .locations
            .insert(role.into(), Location::Colocated(peer.into()));
        self
    }

    /// Add a role at a specific location
    pub fn role(mut self, role: impl Into<String>, location: Location) -> Self {
        self.topology.locations.insert(role.into(), location);
        self
    }

    /// Add a colocation constraint
    pub fn colocated(mut self, r1: impl Into<String>, r2: impl Into<String>) -> Self {
        self.topology
            .constraints
            .push(TopologyConstraint::Colocated(r1.into(), r2.into()));
        self
    }

    /// Add a separation constraint
    pub fn separated(mut self, r1: impl Into<String>, r2: impl Into<String>) -> Self {
        self.topology
            .constraints
            .push(TopologyConstraint::Separated(r1.into(), r2.into()));
        self
    }

    /// Add a pinned location constraint
    pub fn pinned(mut self, role: impl Into<String>, location: Location) -> Self {
        self.topology
            .constraints
            .push(TopologyConstraint::Pinned(role.into(), location));
        self
    }

    /// Add a region constraint
    pub fn region(mut self, role: impl Into<String>, region: impl Into<String>) -> Self {
        self.topology
            .constraints
            .push(TopologyConstraint::Region(role.into(), region.into()));
        self
    }

    /// Build the topology
    pub fn build(self) -> Topology {
        self.topology
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_location_display() {
        assert_eq!(Location::Local.to_string(), "local");
        assert_eq!(
            Location::Remote("localhost:8080".into()).to_string(),
            "localhost:8080"
        );
        assert_eq!(
            Location::Colocated("Alice".into()).to_string(),
            "colocated(Alice)"
        );
    }

    #[test]
    fn test_topology_builder() {
        let topology = Topology::builder()
            .mode(TopologyMode::Local)
            .local_role("Alice")
            .remote_role("Bob", "localhost:8080")
            .colocated("Alice", "Carol")
            .build();

        assert_eq!(topology.mode, Some(TopologyMode::Local));
        assert_eq!(topology.locations.len(), 2);
        assert!(topology.is_local("Alice"));
    }

    #[test]
    fn test_topology_validation() {
        let topology = Topology::builder()
            .local_role("Alice")
            .local_role("Bob")
            .build();

        let roles = vec!["Alice", "Bob", "Carol"];
        assert!(topology.validate(&roles).is_valid());

        let limited_roles = vec!["Alice"];
        assert!(!topology.validate(&limited_roles).is_valid());
    }

    #[test]
    fn test_local_mode() {
        let topology = Topology::local_mode();
        assert_eq!(topology.get_location("AnyRole"), Location::Local);
    }

    #[test]
    fn test_constraint_validation() {
        let topology = Topology::builder().colocated("Alice", "Unknown").build();

        let roles = vec!["Alice", "Bob"];
        match topology.validate(&roles) {
            TopologyValidation::UnknownRole(role) => assert_eq!(role, "Unknown"),
            _ => panic!("Expected UnknownRole"),
        }
    }

    #[test]
    fn test_topology_from_str() {
        let input = r#"
            topology Dev for PingPong {
                Alice: localhost:8080
                Bob: localhost:8081
            }
        "#;

        let parsed = Topology::parse(input).unwrap();
        assert_eq!(parsed.name, "Dev");
        assert_eq!(parsed.for_choreography, "PingPong");
        assert_eq!(
            parsed.topology.get_location("Alice"),
            Location::Remote("localhost:8080".to_string())
        );
    }

    #[test]
    fn test_topology_from_str_local_mode() {
        let input = r#"
            topology Test for MyProtocol {
                mode: local
            }
        "#;

        let parsed = Topology::parse(input).unwrap();
        assert_eq!(parsed.topology.mode, Some(TopologyMode::Local));
        // In local mode, all roles are local
        assert_eq!(parsed.topology.get_location("AnyRole"), Location::Local);
    }

    #[test]
    fn test_topology_load_error() {
        let result = Topology::load("nonexistent/file.topology");
        assert!(result.is_err());
        match result {
            Err(TopologyLoadError::IoError(_)) => {}
            _ => panic!("Expected IoError"),
        }
    }
}
