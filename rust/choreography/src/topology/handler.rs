//! TopologyHandler: Topology-aware protocol handler.
//!
//! This module provides a handler that automatically selects and manages
//! transports based on the topology configuration.

use super::{
    Location, Topology, TopologyError, Transport, TransportError, TransportFactory, TransportResult,
};
use crate::identifiers::RoleName;
use crate::runtime::sync::RwLock;
use crate::{read_lock, write_lock};
use std::collections::HashMap;
use std::sync::Arc;
use thiserror::Error;

/// A topology-aware protocol handler.
///
/// `TopologyHandler` wraps transport selection and routing based on the
/// topology configuration. It automatically creates appropriate transports
/// for each peer role based on their locations (local, remote, colocated).
///
/// # Example
///
/// ```ignore
/// let topology = Topology::builder()
///     .local_role(RoleName::from_static("Alice"))
///     .remote_role(
///         RoleName::from_static("Bob"),
///         TopologyEndpoint::new("localhost:8080").unwrap(),
///     )
///     .build();
///
/// let handler = TopologyHandler::new(topology, RoleName::from_static("Alice"));
///
/// // Send to Bob - automatically uses TCP
/// handler
///     .send(&RoleName::from_static("Bob"), b"Hello".to_vec())
///     .await?;
/// ```
pub struct TopologyHandler {
    /// The topology configuration.
    topology: Topology,
    /// The role this handler represents.
    role: RoleName,
    /// Transports for each peer role.
    transports: Arc<RwLock<HashMap<RoleName, Box<dyn Transport>>>>,
    /// Whether the handler is initialized.
    initialized: Arc<RwLock<bool>>,
}

impl TopologyHandler {
    /// Create a new topology handler.
    pub fn new(topology: Topology, role: RoleName) -> Self {
        Self {
            topology,
            role,
            transports: Arc::new(RwLock::new(HashMap::new())),
            initialized: Arc::new(RwLock::new(false)),
        }
    }

    /// Create a handler from a parsed topology.
    pub fn from_parsed(parsed: super::ParsedTopology, role: RoleName) -> Self {
        Self::new(parsed.topology, role)
    }

    /// Get the role this handler represents.
    pub fn role(&self) -> &RoleName {
        &self.role
    }

    /// Get the topology configuration.
    pub fn topology(&self) -> &Topology {
        &self.topology
    }

    /// Initialize transports for all roles.
    pub async fn initialize(&self) -> TransportResult<()> {
        let mut transports = write_lock!(self.transports);
        let mut initialized = write_lock!(self.initialized);

        if *initialized {
            return Ok(());
        }

        // Create transports for each role in the topology
        for role in self.topology.locations.keys() {
            if role != &self.role {
                let transport = TransportFactory::create(&self.topology, role);
                transports.insert(role.clone(), transport);
            }
        }

        *initialized = true;
        Ok(())
    }

    /// Send a message to a role.
    pub async fn send(&self, to_role: &RoleName, message: Vec<u8>) -> TransportResult<()> {
        let transports = read_lock!(self.transports);

        // If we don't have a transport, create one on-demand
        if let Some(transport) = transports.get(to_role) {
            transport.send(to_role, message).await
        } else {
            drop(transports);

            // Create transport on-demand
            let mut transports = write_lock!(self.transports);
            let transport = TransportFactory::create(&self.topology, to_role);
            transports.insert(to_role.clone(), transport);

            transports
                .get(to_role)
                .ok_or_else(|| TransportError::UnknownRole(to_role.clone()))?
                .send(to_role, message)
                .await
        }
    }

    /// Receive a message from a role.
    pub async fn recv(&self, from_role: &RoleName) -> TransportResult<Vec<u8>> {
        let transports = read_lock!(self.transports);

        if let Some(transport) = transports.get(from_role) {
            transport.recv(from_role).await
        } else {
            Err(TransportError::UnknownRole(from_role.clone()))
        }
    }

    /// Check if connected to a role.
    pub async fn is_connected(&self, role: &RoleName) -> Result<bool, TopologyError> {
        if self.topology.is_local(role)? {
            return Ok(true);
        }

        let transports = read_lock!(self.transports);
        if let Some(transport) = transports.get(role) {
            Ok(transport.is_connected(role))
        } else {
            Ok(false)
        }
    }

    /// Get the location of a role.
    pub fn get_location(&self, role: &RoleName) -> Result<Location, TopologyError> {
        self.topology.get_location(role)
    }

    /// Close all transports.
    pub async fn close(&self) -> TransportResult<()> {
        let mut transports = write_lock!(self.transports);

        for (_, transport) in transports.iter() {
            transport.close().await?;
        }

        transports.clear();
        *write_lock!(self.initialized) = false;

        Ok(())
    }
}

/// Builder for TopologyHandler with fluent API.
pub struct TopologyHandlerBuilder {
    topology: Topology,
    role: Option<RoleName>,
}

/// Errors that can occur while building a TopologyHandler.
#[derive(Debug, Error)]
pub enum TopologyHandlerBuildError {
    #[error("role not specified for topology handler")]
    MissingRole,
}

impl TopologyHandlerBuilder {
    /// Create a new builder with a topology.
    pub fn new(topology: Topology) -> Self {
        Self {
            topology,
            role: None,
        }
    }

    /// Set the role for this handler.
    pub fn with_role(mut self, role: RoleName) -> Self {
        self.role = Some(role);
        self
    }

    /// Build the handler.
    pub fn build(self) -> Result<TopologyHandler, TopologyHandlerBuildError> {
        let role = self.role.ok_or(TopologyHandlerBuildError::MissingRole)?;
        Ok(TopologyHandler::new(self.topology, role))
    }
}

/// Quick constructor for common cases.
impl TopologyHandler {
    /// Create a handler for local-only mode.
    ///
    /// All roles run in-process using channels.
    pub fn local(role: RoleName) -> Self {
        Self::new(Topology::local_mode(), role)
    }

    /// Create a handler builder.
    pub fn builder(topology: Topology) -> TopologyHandlerBuilder {
        TopologyHandlerBuilder::new(topology)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_topology_handler_creation() {
        let topology = Topology::builder()
            .local_role(RoleName::from_static("Alice"))
            .local_role(RoleName::from_static("Bob"))
            .build();

        let handler = TopologyHandler::new(topology, RoleName::from_static("Alice"));
        assert_eq!(handler.role(), &RoleName::from_static("Alice"));
    }

    #[test]
    fn test_local_handler() {
        let handler = TopologyHandler::local(RoleName::from_static("Alice"));
        assert_eq!(handler.role(), &RoleName::from_static("Alice"));
        assert!(handler.topology().mode.is_some());
    }

    #[test]
    fn test_handler_builder() {
        let topology = Topology::builder()
            .remote_role(
                RoleName::from_static("Alice"),
                crate::identifiers::Endpoint::new("localhost:8080").unwrap(),
            )
            .remote_role(
                RoleName::from_static("Bob"),
                crate::identifiers::Endpoint::new("localhost:8081").unwrap(),
            )
            .build();

        let handler = TopologyHandler::builder(topology)
            .with_role(RoleName::from_static("Alice"))
            .build()
            .unwrap();

        assert_eq!(handler.role(), &RoleName::from_static("Alice"));
    }

    #[test]
    fn test_get_location() {
        let topology = Topology::builder()
            .local_role(RoleName::from_static("Alice"))
            .remote_role(
                RoleName::from_static("Bob"),
                crate::identifiers::Endpoint::new("localhost:8080").unwrap(),
            )
            .build();

        let handler = TopologyHandler::new(topology, RoleName::from_static("Alice"));

        assert_eq!(
            handler
                .get_location(&RoleName::from_static("Alice"))
                .unwrap(),
            Location::Local
        );
        assert_eq!(
            handler
                .get_location(&RoleName::from_static("Bob"))
                .unwrap(),
            Location::Remote(crate::identifiers::Endpoint::new("localhost:8080").unwrap())
        );
    }
}
