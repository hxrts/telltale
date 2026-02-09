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
//! This module corresponds to `lean/Telltale/Protocol/Location.lean`:
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

use crate::identifiers::{Datacenter, Endpoint as TopologyEndpoint, Namespace, Region, RoleName};
use crate::ChannelCapacity;

/// Location specifies where a role is deployed.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Default)]
pub enum Location {
    /// In-process execution using channels
    #[default]
    Local,
    /// Remote endpoint (e.g., "localhost:8080", "service.internal:9000")
    Remote(TopologyEndpoint),
    /// Colocated with another role on the same node (shared memory)
    Colocated(RoleName),
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
    Colocated(RoleName, RoleName),
    /// Two roles must be on different nodes
    Separated(RoleName, RoleName),
    /// A role must be at a specific location
    Pinned(RoleName, Location),
    /// A role must be in a specific region/zone
    Region(RoleName, Region),
}

/// Branching requirement for capacity checks.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BranchRequirement {
    /// Role that selects the branch.
    pub sender: RoleName,
    /// Role that must distinguish the branch.
    pub receiver: RoleName,
    /// Number of branch labels.
    pub label_count: u32,
}

impl BranchRequirement {
    /// Create a new branching requirement.
    pub fn new(sender: RoleName, receiver: RoleName, label_count: u32) -> Self {
        Self {
            sender,
            receiver,
            label_count,
        }
    }

    /// Minimum capacity (in bits) required to distinguish `label_count` labels.
    #[must_use]
    pub fn required_capacity_bits(&self) -> u32 {
        min_capacity_bits(self.label_count)
    }
}

fn min_capacity_bits(label_count: u32) -> u32 {
    if label_count <= 1 {
        return 0;
    }
    32 - (label_count - 1).leading_zeros()
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
    Kubernetes(Namespace), // namespace
    /// Discover via Consul
    Consul(Datacenter), // datacenter
}

/// Constraints on the number of instances for a role family.
///
/// Used to validate that wildcard/range role resolutions
/// meet minimum and maximum requirements.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct RoleFamilyConstraint {
    /// Minimum number of instances required (default: 0)
    pub min: u32,
    /// Maximum number of instances allowed (default: unlimited)
    pub max: Option<u32>,
}

impl RoleFamilyConstraint {
    /// Create a new constraint with minimum only.
    pub fn min_only(min: u32) -> Self {
        Self { min, max: None }
    }

    /// Create a new constraint with both min and max.
    pub fn bounded(min: u32, max: u32) -> Self {
        Self {
            min,
            max: Some(max),
        }
    }

    /// Validate a count against this constraint.
    pub fn validate(&self, count: usize) -> Result<(), RoleFamilyConstraintError> {
        let count = count as u32;
        if count < self.min {
            return Err(RoleFamilyConstraintError::BelowMinimum {
                actual: count,
                min: self.min,
            });
        }
        if let Some(max) = self.max {
            if count > max {
                return Err(RoleFamilyConstraintError::AboveMaximum { actual: count, max });
            }
        }
        Ok(())
    }
}

/// Errors from role family constraint validation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RoleFamilyConstraintError {
    /// Actual count is below minimum.
    BelowMinimum { actual: u32, min: u32 },
    /// Actual count is above maximum.
    AboveMaximum { actual: u32, max: u32 },
}

impl fmt::Display for RoleFamilyConstraintError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RoleFamilyConstraintError::BelowMinimum { actual, min } => {
                write!(
                    f,
                    "role family has {} instances, minimum required is {}",
                    actual, min
                )
            }
            RoleFamilyConstraintError::AboveMaximum { actual, max } => {
                write!(
                    f,
                    "role family has {} instances, maximum allowed is {}",
                    actual, max
                )
            }
        }
    }
}

impl std::error::Error for RoleFamilyConstraintError {}

/// Topology maps roles to their deployment locations.
///
/// Uses BTreeMap for deterministic iteration order.
#[derive(Debug, Clone, Default)]
pub struct Topology {
    /// Optional mode for shorthand configuration
    pub mode: Option<TopologyMode>,
    /// Role → Location mapping
    pub locations: BTreeMap<RoleName, Location>,
    /// Directed edge capacities (sender, receiver) → capacity (bits)
    pub channel_capacities: BTreeMap<(RoleName, RoleName), ChannelCapacity>,
    /// Deployment constraints
    pub constraints: Vec<TopologyConstraint>,
    /// Role family instance count constraints
    pub role_constraints: BTreeMap<String, RoleFamilyConstraint>,
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
    pub fn with_role(mut self, role: RoleName, location: Location) -> Self {
        self.locations.insert(role, location);
        self
    }

    /// Add a constraint to the topology
    pub fn with_constraint(mut self, constraint: TopologyConstraint) -> Self {
        self.constraints.push(constraint);
        self
    }

    /// Add a channel capacity to the topology.
    pub fn with_channel_capacity(
        mut self,
        sender: RoleName,
        receiver: RoleName,
        capacity: ChannelCapacity,
    ) -> Self {
        self.channel_capacities.insert((sender, receiver), capacity);
        self
    }

    /// Get the location for a role.
    pub fn get_location(&self, role: &RoleName) -> Result<Location, TopologyError> {
        match &self.mode {
            Some(TopologyMode::Local) => Ok(Location::Local),
            _ => self
                .locations
                .get(role)
                .cloned()
                .ok_or_else(|| TopologyError::UnknownRole(role.clone())),
        }
    }

    /// Check if a role is local
    pub fn is_local(&self, role: &RoleName) -> Result<bool, TopologyError> {
        match self.get_location(role)? {
            Location::Local | Location::Colocated(_) => Ok(true),
            Location::Remote(_) => Ok(false),
        }
    }

    /// Get all roles defined in the topology
    pub fn roles(&self) -> Vec<&RoleName> {
        self.locations.keys().collect()
    }

    /// Look up channel capacity between two roles.
    pub fn channel_capacity(
        &self,
        sender: &RoleName,
        receiver: &RoleName,
    ) -> Option<ChannelCapacity> {
        self.channel_capacities
            .get(&(sender.clone(), receiver.clone()))
            .copied()
    }

    /// Check if topology is valid for a set of choreography roles.
    /// All referenced roles must exist in the choreography.
    pub fn valid_for_roles(&self, choreo_roles: &[RoleName]) -> bool {
        // All topology roles must be in choreography
        let topo_roles_ok = self.locations.keys().all(|r| choreo_roles.contains(r));

        // All capacity roles must be in choreography
        let capacity_roles_ok = self
            .channel_capacities
            .keys()
            .all(|(s, r)| choreo_roles.contains(s) && choreo_roles.contains(r));

        // All constraint roles must be in choreography
        let constraints_ok = self.constraints.iter().all(|c| match c {
            TopologyConstraint::Colocated(r1, r2) | TopologyConstraint::Separated(r1, r2) => {
                choreo_roles.contains(r1) && choreo_roles.contains(r2)
            }
            TopologyConstraint::Pinned(r, _) | TopologyConstraint::Region(r, _) => {
                choreo_roles.contains(r)
            }
        });

        topo_roles_ok && capacity_roles_ok && constraints_ok
    }

    /// Validate a topology against choreography roles
    pub fn validate(&self, choreo_roles: &[RoleName]) -> TopologyValidation {
        // Check all topology roles exist
        for role in self.locations.keys() {
            if !choreo_roles.contains(role) {
                return TopologyValidation::UnknownRole(role.clone());
            }
        }

        // Check all capacity roles exist
        for (sender, receiver) in self.channel_capacities.keys() {
            if !choreo_roles.contains(sender) {
                return TopologyValidation::UnknownRole(sender.clone());
            }
            if !choreo_roles.contains(receiver) {
                return TopologyValidation::UnknownRole(receiver.clone());
            }
        }

        // Check all constraint roles exist
        for c in &self.constraints {
            match c {
                TopologyConstraint::Colocated(r1, r2) | TopologyConstraint::Separated(r1, r2) => {
                    if !choreo_roles.contains(r1) {
                        return TopologyValidation::UnknownRole(r1.clone());
                    }
                    if !choreo_roles.contains(r2) {
                        return TopologyValidation::UnknownRole(r2.clone());
                    }
                }
                TopologyConstraint::Pinned(r, _) | TopologyConstraint::Region(r, _) => {
                    if !choreo_roles.contains(r) {
                        return TopologyValidation::UnknownRole(r.clone());
                    }
                }
            }
        }

        TopologyValidation::Valid
    }

    /// Validate topology and channel capacities against branching requirements.
    ///
    /// Capacity checks are only enforced for edges explicitly configured with
    /// a channel capacity. Missing capacities are treated as unconstrained.
    pub fn validate_with_branches(
        &self,
        choreo_roles: &[RoleName],
        branches: &[BranchRequirement],
    ) -> TopologyValidation {
        let base = self.validate(choreo_roles);
        if !base.is_valid() {
            return base;
        }

        for branch in branches {
            let required_bits = branch.required_capacity_bits();
            if required_bits == 0 {
                continue;
            }
            if let Some(available) = self.channel_capacity(&branch.sender, &branch.receiver) {
                let available_bits = available.get();
                if available_bits < required_bits {
                    return TopologyValidation::InsufficientCapacity {
                        sender: branch.sender.clone(),
                        receiver: branch.receiver.clone(),
                        required_bits,
                        available_bits,
                    };
                }
            }
        }

        TopologyValidation::Valid
    }

    /// Validate a resolved role family against configured constraints.
    ///
    /// # Arguments
    ///
    /// * `family` - The name of the role family (e.g., "Witness")
    /// * `count` - The number of resolved instances
    ///
    /// # Returns
    ///
    /// `Ok(())` if the count satisfies constraints, or an error if not.
    /// Returns `Ok(())` if no constraint is configured for this family.
    pub fn validate_family(
        &self,
        family: &str,
        count: usize,
    ) -> Result<(), RoleFamilyConstraintError> {
        if let Some(constraint) = self.role_constraints.get(family) {
            constraint.validate(count)
        } else {
            Ok(())
        }
    }

    /// Get the constraint for a role family, if configured.
    pub fn get_family_constraint(&self, family: &str) -> Option<&RoleFamilyConstraint> {
        self.role_constraints.get(family)
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
    UnknownRole(RoleName),
    /// A constraint is violated (with reason)
    ConstraintViolation(TopologyConstraint, String),
    /// Channel capacity is insufficient for a branching requirement
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
    pub fn local_role(mut self, role: RoleName) -> Self {
        self.topology.locations.insert(role, Location::Local);
        self
    }

    /// Add a remote role
    pub fn remote_role(mut self, role: RoleName, endpoint: TopologyEndpoint) -> Self {
        self.topology
            .locations
            .insert(role, Location::Remote(endpoint));
        self
    }

    /// Add a colocated role
    pub fn colocated_role(mut self, role: RoleName, peer: RoleName) -> Self {
        self.topology
            .locations
            .insert(role, Location::Colocated(peer));
        self
    }

    /// Add a role at a specific location
    pub fn role(mut self, role: RoleName, location: Location) -> Self {
        self.topology.locations.insert(role, location);
        self
    }

    /// Add a directed channel capacity between two roles.
    pub fn channel_capacity(
        mut self,
        sender: RoleName,
        receiver: RoleName,
        capacity: ChannelCapacity,
    ) -> Self {
        self.topology
            .channel_capacities
            .insert((sender, receiver), capacity);
        self
    }

    /// Add a colocation constraint
    pub fn colocated(mut self, r1: RoleName, r2: RoleName) -> Self {
        self.topology
            .constraints
            .push(TopologyConstraint::Colocated(r1, r2));
        self
    }

    /// Add a separation constraint
    pub fn separated(mut self, r1: RoleName, r2: RoleName) -> Self {
        self.topology
            .constraints
            .push(TopologyConstraint::Separated(r1, r2));
        self
    }

    /// Add a pinned location constraint
    pub fn pinned(mut self, role: RoleName, location: Location) -> Self {
        self.topology
            .constraints
            .push(TopologyConstraint::Pinned(role, location));
        self
    }

    /// Add a region constraint
    pub fn region(mut self, role: RoleName, region: Region) -> Self {
        self.topology
            .constraints
            .push(TopologyConstraint::Region(role, region));
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
            Location::Remote(TopologyEndpoint::new("localhost:8080").unwrap()).to_string(),
            "localhost:8080"
        );
        assert_eq!(
            Location::Colocated(RoleName::from_static("Alice")).to_string(),
            "colocated(Alice)"
        );
    }

    #[test]
    fn test_topology_builder() {
        let topology = Topology::builder()
            .mode(TopologyMode::Local)
            .local_role(RoleName::from_static("Alice"))
            .remote_role(
                RoleName::from_static("Bob"),
                TopologyEndpoint::new("localhost:8080").unwrap(),
            )
            .colocated(
                RoleName::from_static("Alice"),
                RoleName::from_static("Carol"),
            )
            .build();

        assert_eq!(topology.mode, Some(TopologyMode::Local));
        assert_eq!(topology.locations.len(), 2);
        assert!(topology.is_local(&RoleName::from_static("Alice")).unwrap());
    }

    #[test]
    fn test_topology_validation() {
        let topology = Topology::builder()
            .local_role(RoleName::from_static("Alice"))
            .local_role(RoleName::from_static("Bob"))
            .build();

        let roles = vec![
            RoleName::from_static("Alice"),
            RoleName::from_static("Bob"),
            RoleName::from_static("Carol"),
        ];
        assert!(topology.validate(&roles).is_valid());

        let limited_roles = vec![RoleName::from_static("Alice")];
        assert!(!topology.validate(&limited_roles).is_valid());
    }

    #[test]
    fn test_topology_capacity_validation() {
        let topology = Topology::builder()
            .local_role(RoleName::from_static("Alice"))
            .local_role(RoleName::from_static("Bob"))
            .channel_capacity(
                RoleName::from_static("Alice"),
                RoleName::from_static("Bob"),
                ChannelCapacity::new(1),
            )
            .build();

        let roles = vec![RoleName::from_static("Alice"), RoleName::from_static("Bob")];
        let branches = vec![BranchRequirement::new(
            RoleName::from_static("Alice"),
            RoleName::from_static("Bob"),
            3,
        )];

        match topology.validate_with_branches(&roles, &branches) {
            TopologyValidation::InsufficientCapacity {
                sender,
                receiver,
                required_bits,
                available_bits,
            } => {
                assert_eq!(sender, RoleName::from_static("Alice"));
                assert_eq!(receiver, RoleName::from_static("Bob"));
                assert_eq!(required_bits, 2);
                assert_eq!(available_bits, 1);
            }
            _ => panic!("Expected InsufficientCapacity"),
        }
    }

    #[test]
    fn test_topology_capacity_unconstrained() {
        let topology = Topology::builder()
            .local_role(RoleName::from_static("Alice"))
            .local_role(RoleName::from_static("Bob"))
            .build();

        let roles = vec![RoleName::from_static("Alice"), RoleName::from_static("Bob")];
        let branches = vec![BranchRequirement::new(
            RoleName::from_static("Alice"),
            RoleName::from_static("Bob"),
            4,
        )];

        assert!(topology
            .validate_with_branches(&roles, &branches)
            .is_valid());
    }

    #[test]
    fn test_local_mode() {
        let topology = Topology::local_mode();
        assert_eq!(
            topology
                .get_location(&RoleName::from_static("AnyRole"))
                .unwrap(),
            Location::Local
        );
    }

    #[test]
    fn test_constraint_validation() {
        let topology = Topology::builder()
            .colocated(
                RoleName::from_static("Alice"),
                RoleName::from_static("Unknown"),
            )
            .build();

        let roles = vec![RoleName::from_static("Alice"), RoleName::from_static("Bob")];
        match topology.validate(&roles) {
            TopologyValidation::UnknownRole(role) => {
                assert_eq!(role, RoleName::from_static("Unknown"))
            }
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
            parsed
                .topology
                .get_location(&RoleName::from_static("Alice"))
                .unwrap(),
            Location::Remote(TopologyEndpoint::new("localhost:8080").unwrap())
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
        assert_eq!(
            parsed
                .topology
                .get_location(&RoleName::from_static("AnyRole"))
                .unwrap(),
            Location::Local
        );
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

    #[test]
    fn test_role_family_constraint_min_only() {
        let constraint = RoleFamilyConstraint::min_only(3);
        assert!(constraint.validate(3).is_ok());
        assert!(constraint.validate(5).is_ok());
        assert!(constraint.validate(100).is_ok());
        assert!(constraint.validate(2).is_err());
        assert!(constraint.validate(0).is_err());
    }

    #[test]
    fn test_role_family_constraint_bounded() {
        let constraint = RoleFamilyConstraint::bounded(2, 5);
        assert!(constraint.validate(2).is_ok());
        assert!(constraint.validate(3).is_ok());
        assert!(constraint.validate(5).is_ok());
        assert!(constraint.validate(1).is_err());
        assert!(constraint.validate(6).is_err());
    }

    #[test]
    fn test_role_family_constraint_error_messages() {
        let constraint = RoleFamilyConstraint::bounded(3, 10);
        let err = constraint.validate(2).unwrap_err();
        assert!(err.to_string().contains("minimum required is 3"));

        let err = constraint.validate(11).unwrap_err();
        assert!(err.to_string().contains("maximum allowed is 10"));
    }

    #[test]
    fn test_topology_validate_family() {
        let input = r#"
            topology Test for Protocol {
                role_constraints {
                    Witness: min = 3, max = 10
                }
            }
        "#;
        let parsed = Topology::parse(input).unwrap();
        let topology = parsed.topology;

        // Valid counts
        assert!(topology.validate_family("Witness", 3).is_ok());
        assert!(topology.validate_family("Witness", 5).is_ok());
        assert!(topology.validate_family("Witness", 10).is_ok());

        // Invalid counts
        assert!(topology.validate_family("Witness", 2).is_err());
        assert!(topology.validate_family("Witness", 11).is_err());

        // Unknown family - no constraint, so any count is valid
        assert!(topology.validate_family("Unknown", 0).is_ok());
        assert!(topology.validate_family("Unknown", 100).is_ok());
    }

    #[test]
    fn test_topology_get_family_constraint() {
        let input = r#"
            topology Test for Protocol {
                role_constraints {
                    Witness: min = 3
                }
            }
        "#;
        let parsed = Topology::parse(input).unwrap();
        let topology = parsed.topology;

        let constraint = topology.get_family_constraint("Witness");
        assert!(constraint.is_some());
        assert_eq!(constraint.unwrap().min, 3);

        let unknown = topology.get_family_constraint("Unknown");
        assert!(unknown.is_none());
    }
}
