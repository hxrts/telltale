//! Topology DSL parser.
//!
//! Parses topology definitions from DSL source code.

use super::{Location, Topology, TopologyConstraint, TopologyMode};
use crate::identifiers::{
    Datacenter, Endpoint as TopologyEndpoint, IdentifierError, Namespace, Region, RoleName,
};
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
}
