//! TopologyHandler: Topology-aware protocol handler.
//!
//! This module provides a handler that automatically selects and manages
//! transports based on the topology configuration.

use super::{Location, Topology, Transport, TransportError, TransportFactory, TransportResult};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;

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
///     .local_role("Alice")
///     .remote_role("Bob", "localhost:8080")
///     .build();
///
/// let handler = TopologyHandler::new(topology, "Alice");
///
/// // Send to Bob - automatically uses TCP
/// handler.send("Bob", b"Hello".to_vec()).await?;
/// ```
pub struct TopologyHandler {
    /// The topology configuration.
    topology: Topology,
    /// The role this handler represents.
    role: String,
    /// Transports for each peer role.
    transports: Arc<RwLock<HashMap<String, Box<dyn Transport>>>>,
    /// Whether the handler is initialized.
    initialized: Arc<RwLock<bool>>,
}

impl TopologyHandler {
    /// Create a new topology handler.
    pub fn new(topology: Topology, role: impl Into<String>) -> Self {
        Self {
            topology,
            role: role.into(),
            transports: Arc::new(RwLock::new(HashMap::new())),
            initialized: Arc::new(RwLock::new(false)),
        }
    }

    /// Create a handler from a parsed topology.
    pub fn from_parsed(parsed: super::ParsedTopology, role: impl Into<String>) -> Self {
        Self::new(parsed.topology, role)
    }

    /// Get the role this handler represents.
    pub fn role(&self) -> &str {
        &self.role
    }

    /// Get the topology configuration.
    pub fn topology(&self) -> &Topology {
        &self.topology
    }

    /// Initialize transports for all roles.
    pub async fn initialize(&self) -> TransportResult<()> {
        let mut transports = self.transports.write().await;
        let mut initialized = self.initialized.write().await;

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
    pub async fn send(&self, to_role: &str, message: Vec<u8>) -> TransportResult<()> {
        let transports = self.transports.read().await;

        // If we don't have a transport, create one on-demand
        if let Some(transport) = transports.get(to_role) {
            transport.send(to_role, message).await
        } else {
            drop(transports);

            // Create transport on-demand
            let mut transports = self.transports.write().await;
            let transport = TransportFactory::create(&self.topology, to_role);
            transports.insert(to_role.to_string(), transport);

            transports
                .get(to_role)
                .ok_or_else(|| TransportError::UnknownRole(to_role.to_string()))?
                .send(to_role, message)
                .await
        }
    }

    /// Receive a message from a role.
    pub async fn recv(&self, from_role: &str) -> TransportResult<Vec<u8>> {
        let transports = self.transports.read().await;

        if let Some(transport) = transports.get(from_role) {
            transport.recv(from_role).await
        } else {
            Err(TransportError::UnknownRole(from_role.to_string()))
        }
    }

    /// Check if connected to a role.
    pub fn is_connected(&self, role: &str) -> bool {
        // For now, always return true for local mode
        self.topology.is_local(role) || {
            // Could check transport connection status
            true
        }
    }

    /// Get the location of a role.
    pub fn get_location(&self, role: &str) -> Location {
        self.topology.get_location(role)
    }

    /// Close all transports.
    pub async fn close(&self) -> TransportResult<()> {
        let mut transports = self.transports.write().await;

        for (_, transport) in transports.iter() {
            transport.close().await?;
        }

        transports.clear();
        *self.initialized.write().await = false;

        Ok(())
    }
}

/// Builder for TopologyHandler with fluent API.
pub struct TopologyHandlerBuilder {
    topology: Topology,
    role: Option<String>,
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
    pub fn with_role(mut self, role: impl Into<String>) -> Self {
        self.role = Some(role.into());
        self
    }

    /// Build the handler.
    pub fn build(self) -> Result<TopologyHandler, String> {
        let role = self.role.ok_or_else(|| "Role not specified".to_string())?;
        Ok(TopologyHandler::new(self.topology, role))
    }
}

/// Quick constructor for common cases.
impl TopologyHandler {
    /// Create a handler for local-only mode.
    ///
    /// All roles run in-process using channels.
    pub fn local(role: impl Into<String>) -> Self {
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
            .local_role("Alice")
            .local_role("Bob")
            .build();

        let handler = TopologyHandler::new(topology, "Alice");
        assert_eq!(handler.role(), "Alice");
    }

    #[test]
    fn test_local_handler() {
        let handler = TopologyHandler::local("Alice");
        assert_eq!(handler.role(), "Alice");
        assert!(handler.topology().mode.is_some());
    }

    #[test]
    fn test_handler_builder() {
        let topology = Topology::builder()
            .remote_role("Alice", "localhost:8080")
            .remote_role("Bob", "localhost:8081")
            .build();

        let handler = TopologyHandler::builder(topology)
            .with_role("Alice")
            .build()
            .unwrap();

        assert_eq!(handler.role(), "Alice");
    }

    #[test]
    fn test_get_location() {
        let topology = Topology::builder()
            .local_role("Alice")
            .remote_role("Bob", "localhost:8080")
            .build();

        let handler = TopologyHandler::new(topology, "Alice");

        assert_eq!(handler.get_location("Alice"), Location::Local);
        assert_eq!(
            handler.get_location("Bob"),
            Location::Remote("localhost:8080".to_string())
        );
    }
}
