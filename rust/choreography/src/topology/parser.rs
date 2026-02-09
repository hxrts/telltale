//! Topology DSL parser.
//!
//! Parses topology definitions from DSL source code.

use super::{Location, RoleFamilyConstraint, Topology, TopologyConstraint, TopologyMode};
use crate::identifiers::{
    Datacenter, Endpoint as TopologyEndpoint, IdentifierError, Namespace, Region, RoleName,
};
use crate::ChannelCapacity;
use pest::Parser;
use pest_derive::Parser;
use thiserror::Error;

#[derive(Parser)]
#[grammar = "compiler/topology.pest"]
struct TopologyParser;

/// Errors that can occur during topology parsing.
#[derive(Debug, Clone, Error)]
pub enum TopologyParseError {
    #[error("Parse error: {0}")]
    ParseError(String),

    #[error("Unknown mode: {0}")]
    UnknownMode(String),

    #[error("Invalid location: {0}")]
    InvalidLocation(String),

    #[error("Invalid constraint: {0}")]
    InvalidConstraint(String),

    #[error("Invalid capacity: {0}")]
    InvalidCapacity(String),

    #[error("Invalid identifier: {0}")]
    InvalidIdentifier(IdentifierError),
}

impl From<pest::error::Error<Rule>> for TopologyParseError {
    fn from(e: pest::error::Error<Rule>) -> Self {
        TopologyParseError::ParseError(e.to_string())
    }
}

impl From<IdentifierError> for TopologyParseError {
    fn from(err: IdentifierError) -> Self {
        TopologyParseError::InvalidIdentifier(err)
    }
}

/// Parsed topology with metadata.
#[derive(Debug, Clone)]
pub struct ParsedTopology {
    /// Name of this topology configuration.
    pub name: String,
    /// Name of the choreography this topology is for.
    pub for_choreography: String,
    /// The topology configuration.
    pub topology: Topology,
}

/// Parse a topology definition from DSL source.
pub fn parse_topology(input: &str) -> Result<ParsedTopology, TopologyParseError> {
    let pairs = TopologyParser::parse(Rule::topology, input)?;
    let mut name = String::new();
    let mut for_choreography = String::new();
    let mut topology = Topology::new();

    for pair in pairs {
        if pair.as_rule() == Rule::topology {
            let mut inner = pair.into_inner();

            // Get topology name
            if let Some(name_pair) = inner.next() {
                name = name_pair.as_str().to_string();
            }

            // Get choreography name (after "for")
            if let Some(for_pair) = inner.next() {
                for_choreography = for_pair.as_str().to_string();
            }

            // Parse topology body
            if let Some(body_pair) = inner.next() {
                topology = parse_topology_body(body_pair)?;
            }
        }
    }

    Ok(ParsedTopology {
        name,
        for_choreography,
        topology,
    })
}

fn parse_topology_body(pair: pest::iterators::Pair<Rule>) -> Result<Topology, TopologyParseError> {
    let mut topology = Topology::new();

    for inner in pair.into_inner() {
        match inner.as_rule() {
            Rule::topology_mode => {
                topology.mode = Some(parse_topology_mode(inner)?);
            }
            Rule::topology_mappings => {
                for mapping in inner.into_inner() {
                    let (role, location) = parse_topology_mapping(mapping)?;
                    topology.locations.insert(role, location);
                }
            }
            Rule::topology_constraints => {
                for constraint in inner.into_inner() {
                    if constraint.as_rule() == Rule::constraint_decl {
                        topology.constraints.push(parse_constraint(constraint)?);
                    }
                }
            }
            Rule::channel_capacities_block => {
                for decl in inner.into_inner() {
                    if decl.as_rule() == Rule::channel_capacity_decl {
                        let (sender, receiver, capacity) = parse_channel_capacity_decl(decl)?;
                        topology
                            .channel_capacities
                            .insert((sender, receiver), capacity);
                    }
                }
            }
            Rule::role_constraints_block => {
                for decl in inner.into_inner() {
                    if decl.as_rule() == Rule::role_constraint_decl {
                        let (family, constraint) = parse_role_constraint_decl(decl)?;
                        topology.role_constraints.insert(family, constraint);
                    }
                }
            }
            _ => {}
        }
    }

    Ok(topology)
}

fn parse_topology_mode(
    pair: pest::iterators::Pair<Rule>,
) -> Result<TopologyMode, TopologyParseError> {
    for inner in pair.into_inner() {
        if inner.as_rule() == Rule::topology_mode_value {
            return parse_mode_value(inner);
        }
    }
    Err(TopologyParseError::UnknownMode("empty mode".to_string()))
}

fn parse_mode_value(pair: pest::iterators::Pair<Rule>) -> Result<TopologyMode, TopologyParseError> {
    let inner = pair.into_inner().next();
    match inner {
        Some(p) => match p.as_rule() {
            Rule::kubernetes_mode => {
                let namespace = p.into_inner().next().map(|i| i.as_str()).ok_or_else(|| {
                    TopologyParseError::InvalidConstraint(
                        "kubernetes mode requires a namespace".to_string(),
                    )
                })?;
                Ok(TopologyMode::Kubernetes(Namespace::new(namespace)?))
            }
            Rule::consul_mode => {
                let datacenter = p.into_inner().next().map(|i| i.as_str()).ok_or_else(|| {
                    TopologyParseError::InvalidConstraint(
                        "consul mode requires a datacenter".to_string(),
                    )
                })?;
                Ok(TopologyMode::Consul(Datacenter::new(datacenter)?))
            }
            _ => {
                let s = p.as_str();
                match s {
                    "local" => Ok(TopologyMode::Local),
                    "per_role" => Ok(TopologyMode::PerRole),
                    _ => Err(TopologyParseError::UnknownMode(s.to_string())),
                }
            }
        },
        None => Ok(TopologyMode::Local),
    }
}

fn parse_topology_mapping(
    pair: pest::iterators::Pair<Rule>,
) -> Result<(RoleName, Location), TopologyParseError> {
    let mut inner = pair.into_inner();
    let role = inner
        .next()
        .map(|p| RoleName::new(p.as_str()))
        .transpose()?
        .ok_or_else(|| TopologyParseError::InvalidConstraint("missing role".to_string()))?;
    let location = inner
        .next()
        .map(|p| parse_location(p))
        .transpose()?
        .unwrap_or(Location::Local);

    Ok((role, location))
}

fn parse_location(pair: pest::iterators::Pair<Rule>) -> Result<Location, TopologyParseError> {
    let inner = pair.into_inner().next();
    match inner {
        Some(p) => match p.as_rule() {
            Rule::local_location => Ok(Location::Local),
            Rule::colocated_location => {
                let peer = p
                    .into_inner()
                    .next()
                    .map(|i| RoleName::new(i.as_str()))
                    .transpose()?
                    .ok_or_else(|| {
                        TopologyParseError::InvalidLocation("colocated requires a role".to_string())
                    })?;
                Ok(Location::Colocated(peer))
            }
            Rule::endpoint => Ok(Location::Remote(TopologyEndpoint::new(p.as_str())?)),
            _ => {
                let s = p.as_str();
                if s == "local" {
                    Ok(Location::Local)
                } else {
                    Ok(Location::Remote(TopologyEndpoint::new(s)?))
                }
            }
        },
        None => Ok(Location::Local),
    }
}

fn parse_constraint(
    pair: pest::iterators::Pair<Rule>,
) -> Result<TopologyConstraint, TopologyParseError> {
    let inner = pair
        .into_inner()
        .next()
        .ok_or_else(|| TopologyParseError::InvalidConstraint("empty constraint".to_string()))?;

    match inner.as_rule() {
        Rule::colocated_constraint => {
            let mut idents = inner.into_inner();
            let r1 = idents
                .next()
                .map(|p| RoleName::new(p.as_str()))
                .transpose()?
                .ok_or_else(|| {
                    TopologyParseError::InvalidConstraint(
                        "colocated requires two roles".to_string(),
                    )
                })?;
            let r2 = idents
                .next()
                .map(|p| RoleName::new(p.as_str()))
                .transpose()?
                .ok_or_else(|| {
                    TopologyParseError::InvalidConstraint(
                        "colocated requires two roles".to_string(),
                    )
                })?;
            Ok(TopologyConstraint::Colocated(r1, r2))
        }
        Rule::separated_constraint => {
            let roles: Vec<RoleName> = inner
                .into_inner()
                .flat_map(|p| p.into_inner())
                .map(|p| RoleName::new(p.as_str()))
                .collect::<Result<Vec<_>, _>>()?;
            // For now, create pairwise separation constraints
            if roles.len() >= 2 {
                Ok(TopologyConstraint::Separated(
                    roles[0].clone(),
                    roles[1].clone(),
                ))
            } else {
                Err(TopologyParseError::InvalidConstraint(
                    "separated requires at least 2 roles".to_string(),
                ))
            }
        }
        Rule::pinned_constraint => {
            let mut inner_iter = inner.into_inner();
            let role = inner_iter
                .next()
                .map(|p| RoleName::new(p.as_str()))
                .transpose()?
                .ok_or_else(|| {
                    TopologyParseError::InvalidConstraint("pinned requires a role".to_string())
                })?;
            let location = inner_iter
                .next()
                .map(|p| parse_location(p))
                .transpose()?
                .unwrap_or(Location::Local);
            Ok(TopologyConstraint::Pinned(role, location))
        }
        Rule::region_constraint => {
            let mut idents = inner.into_inner();
            let role = idents
                .next()
                .map(|p| RoleName::new(p.as_str()))
                .transpose()?
                .ok_or_else(|| {
                    TopologyParseError::InvalidConstraint("region requires a role".to_string())
                })?;
            let region = idents
                .next()
                .map(|p| Region::new(p.as_str()))
                .transpose()?
                .ok_or_else(|| {
                    TopologyParseError::InvalidConstraint("region requires a value".to_string())
                })?;
            Ok(TopologyConstraint::Region(role, region))
        }
        _ => Err(TopologyParseError::InvalidConstraint(format!(
            "unknown constraint type: {:?}",
            inner.as_rule()
        ))),
    }
}

fn parse_channel_capacity_decl(
    pair: pest::iterators::Pair<Rule>,
) -> Result<(RoleName, RoleName, ChannelCapacity), TopologyParseError> {
    let mut inner = pair.into_inner();
    let sender = inner
        .next()
        .map(|p| RoleName::new(p.as_str()))
        .transpose()?
        .ok_or_else(|| TopologyParseError::InvalidConstraint("missing sender".to_string()))?;
    let receiver = inner
        .next()
        .map(|p| RoleName::new(p.as_str()))
        .transpose()?
        .ok_or_else(|| TopologyParseError::InvalidConstraint("missing receiver".to_string()))?;
    let capacity = inner
        .next()
        .ok_or_else(|| TopologyParseError::InvalidConstraint("missing capacity".to_string()))?
        .as_str()
        .parse::<u32>()
        .map_err(|e| TopologyParseError::InvalidCapacity(e.to_string()))?;
    let capacity = ChannelCapacity::try_new(capacity)
        .map_err(|e| TopologyParseError::InvalidCapacity(e.to_string()))?;

    Ok((sender, receiver, capacity))
}

fn parse_role_constraint_decl(
    pair: pest::iterators::Pair<Rule>,
) -> Result<(String, RoleFamilyConstraint), TopologyParseError> {
    let mut inner = pair.into_inner();

    // Get family name
    let family = inner
        .next()
        .map(|p| p.as_str().to_string())
        .ok_or_else(|| {
            TopologyParseError::InvalidConstraint("role constraint missing family name".to_string())
        })?;

    // Get constraint spec
    let spec = inner.next().ok_or_else(|| {
        TopologyParseError::InvalidConstraint("role constraint missing specification".to_string())
    })?;

    let constraint = parse_role_constraint_spec(spec)?;
    Ok((family, constraint))
}

fn parse_role_constraint_spec(
    pair: pest::iterators::Pair<Rule>,
) -> Result<RoleFamilyConstraint, TopologyParseError> {
    let mut min: Option<u32> = None;
    let mut max: Option<u32> = None;

    for inner in pair.into_inner() {
        match inner.as_rule() {
            Rule::min_constraint => {
                let value = inner
                    .into_inner()
                    .next()
                    .and_then(|p| p.as_str().parse::<u32>().ok())
                    .ok_or_else(|| {
                        TopologyParseError::InvalidConstraint(
                            "min constraint requires integer value".to_string(),
                        )
                    })?;
                min = Some(value);
            }
            Rule::max_constraint => {
                let value = inner
                    .into_inner()
                    .next()
                    .and_then(|p| p.as_str().parse::<u32>().ok())
                    .ok_or_else(|| {
                        TopologyParseError::InvalidConstraint(
                            "max constraint requires integer value".to_string(),
                        )
                    })?;
                max = Some(value);
            }
            _ => {}
        }
    }

    Ok(RoleFamilyConstraint {
        min: min.unwrap_or(0),
        max,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_local_mode_topology() {
        let input = r#"
            topology TestLocal for PingPong {
                mode: local
            }
        "#;

        let result = parse_topology(input).unwrap();
        assert_eq!(result.name, "TestLocal");
        assert_eq!(result.for_choreography, "PingPong");
        assert_eq!(result.topology.mode, Some(TopologyMode::Local));
    }

    #[test]
    fn test_parse_topology_with_mappings() {
        let input = r#"
            topology Dev for PingPong {
                Alice: localhost:8080
                Bob: localhost:8081
            }
        "#;

        let result = parse_topology(input).unwrap();
        assert_eq!(result.name, "Dev");
        assert_eq!(
            result
                .topology
                .get_location(&RoleName::from_static("Alice"))
                .unwrap(),
            Location::Remote(TopologyEndpoint::new("localhost:8080").unwrap())
        );
        assert_eq!(
            result
                .topology
                .get_location(&RoleName::from_static("Bob"))
                .unwrap(),
            Location::Remote(TopologyEndpoint::new("localhost:8081").unwrap())
        );
    }

    #[test]
    fn test_parse_topology_with_constraints() {
        let input = r#"
            topology Prod for TwoPhaseCommit {
                Coordinator: coordinator.internal:9000
                ParticipantA: participant-a.internal:9000
                ParticipantB: participant-b.internal:9000

                constraints {
                    separated: Coordinator, ParticipantA
                    region: Coordinator -> us_east_1
                }
            }
        "#;

        let result = parse_topology(input).unwrap();
        assert_eq!(result.name, "Prod");
        assert_eq!(result.topology.constraints.len(), 2);
    }

    #[test]
    fn test_parse_channel_capacities() {
        let input = r#"
            topology Capacity for Protocol {
                Alice: local
                Bob: local

                channel_capacities {
                    Alice -> Bob: 4
                }
            }
        "#;

        let result = parse_topology(input).unwrap();
        let key = (RoleName::from_static("Alice"), RoleName::from_static("Bob"));
        let capacity = result.topology.channel_capacities.get(&key).copied();
        assert_eq!(capacity, Some(ChannelCapacity::new(4)));
    }

    #[test]
    fn test_parse_kubernetes_mode() {
        let input = r#"
            topology K8s for MyProtocol {
                mode: kubernetes(myapp)
            }
        "#;

        let result = parse_topology(input).unwrap();
        assert_eq!(
            result.topology.mode,
            Some(TopologyMode::Kubernetes(Namespace::new("myapp").unwrap()))
        );
    }

    #[test]
    fn test_parse_colocated_location() {
        let input = r#"
            topology Mixed for Protocol {
                Alice: local
                Bob: colocated(Alice)
                Carol: remote.host:8080
            }
        "#;

        let result = parse_topology(input).unwrap();
        assert_eq!(
            result
                .topology
                .get_location(&RoleName::from_static("Alice"))
                .unwrap(),
            Location::Local
        );
        assert_eq!(
            result
                .topology
                .get_location(&RoleName::from_static("Bob"))
                .unwrap(),
            Location::Colocated(RoleName::from_static("Alice"))
        );
    }

    #[test]
    fn test_parse_role_constraints_min_only() {
        let input = r#"
            topology ThresholdSig for Protocol {
                Coordinator: localhost:8000

                role_constraints {
                    Witness: min = 3
                }
            }
        "#;

        let result = parse_topology(input).unwrap();
        let constraint = result.topology.role_constraints.get("Witness").unwrap();
        assert_eq!(constraint.min, 3);
        assert_eq!(constraint.max, None);
    }

    #[test]
    fn test_parse_role_constraints_min_and_max() {
        let input = r#"
            topology ThresholdSig for Protocol {
                role_constraints {
                    Witness: min = 3, max = 10
                }
            }
        "#;

        let result = parse_topology(input).unwrap();
        let constraint = result.topology.role_constraints.get("Witness").unwrap();
        assert_eq!(constraint.min, 3);
        assert_eq!(constraint.max, Some(10));
    }

    #[test]
    fn test_parse_role_constraints_max_first() {
        let input = r#"
            topology ThresholdSig for Protocol {
                role_constraints {
                    Worker: max = 5, min = 1
                }
            }
        "#;

        let result = parse_topology(input).unwrap();
        let constraint = result.topology.role_constraints.get("Worker").unwrap();
        assert_eq!(constraint.min, 1);
        assert_eq!(constraint.max, Some(5));
    }

    #[test]
    fn test_parse_role_constraints_multiple_families() {
        let input = r#"
            topology ThresholdSig for Protocol {
                role_constraints {
                    Witness: min = 3
                    Worker: min = 1, max = 10
                    Validator: max = 5
                }
            }
        "#;

        let result = parse_topology(input).unwrap();
        assert_eq!(result.topology.role_constraints.len(), 3);

        let witness = result.topology.role_constraints.get("Witness").unwrap();
        assert_eq!(witness.min, 3);
        assert_eq!(witness.max, None);

        let worker = result.topology.role_constraints.get("Worker").unwrap();
        assert_eq!(worker.min, 1);
        assert_eq!(worker.max, Some(10));

        let validator = result.topology.role_constraints.get("Validator").unwrap();
        assert_eq!(validator.min, 0); // default min
        assert_eq!(validator.max, Some(5));
    }

    #[test]
    fn test_parse_role_constraints_with_mappings_and_constraints() {
        let input = r#"
            topology Prod for TwoPhaseCommit {
                Coordinator: coordinator.internal:9000

                role_constraints {
                    Participant: min = 2, max = 100
                }

                constraints {
                    region: Coordinator -> us_east_1
                }
            }
        "#;

        let result = parse_topology(input).unwrap();
        assert_eq!(result.topology.role_constraints.len(), 1);
        assert_eq!(result.topology.constraints.len(), 1);

        let participant = result.topology.role_constraints.get("Participant").unwrap();
        assert_eq!(participant.min, 2);
        assert_eq!(participant.max, Some(100));
    }
}
