//! Effect Handler Architecture for Choreographic Programming
//!
//! This module provides a clean effect boundary between pure choreographic logic
//! and runtime transport implementations. It allows for testable, composable,
//! and runtime-agnostic protocol implementations.
//!
//! # Architecture
//!
//! The effect handler system separates concerns:
//! - **Choreographic Logic**: Pure protocol specification (what to do)
//! - **Effect Handlers**: Runtime implementation (how to do it)
//! - **Interpreters**: Execute choreographic programs using handlers
//!
//! # Example
//!
//! ```text
//! use rumpsteak_aura_choreography::{ChoreoHandler, Label};
//!
//! #[async_trait]
//! impl ChoreoHandler for MyHandler {
//!     type Role = MyRole;
//!     type Endpoint = MyEndpoint;
//!
//!     async fn send<M>(&mut self, ep: &mut Self::Endpoint, to: Self::Role, msg: &M) -> Result<()> {
//!         // Implementation
//!     }
//!     // ... other methods
//! }
//! ```

use async_trait::async_trait;
use serde::{de::DeserializeOwned, Serialize};
use std::fmt::Debug;
use std::time::Duration;
use thiserror::Error;

use crate::effects::registry::{ExtensibleHandler, ExtensionRegistry};

/// Trait for role identifiers in choreographies
///
/// Roles are typically generated as enums per choreography, but any type
/// implementing the required traits can serve as a role identifier.
pub trait RoleId: Copy + Eq + std::hash::Hash + Debug + Send + Sync + 'static {}
impl<T: Copy + Eq + std::hash::Hash + Debug + Send + Sync + 'static> RoleId for T {}

/// Labels identify branches in internal/external choice
///
/// Used to distinguish between different paths in choice protocols.
/// The label is typically a static string matching a protocol branch name.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Default)]
pub struct Label(pub &'static str);

/// Session endpoint trait
///
/// Represents the runtime-specific connection state (e.g., Rumpsteak channel bundle).
/// The generated code will be generic over the endpoint type.
pub trait Endpoint: Send {}
impl<T: Send> Endpoint for T {}

/// Errors that can occur during choreographic execution
#[derive(Debug, Error)]
pub enum ChoreographyError {
    /// Transport-layer error (network, channel failure, etc.)
    #[error("Transport error: {0}")]
    Transport(String),

    /// Message serialization/deserialization error
    #[error("Serialization error: {0}")]
    Serialization(String),

    /// Operation exceeded the specified timeout
    #[error("Timeout after {0:?}")]
    Timeout(Duration),

    /// Protocol specification was violated at runtime
    #[error("Protocol violation: {0}")]
    ProtocolViolation(String),

    /// Referenced role not found in the choreography
    #[error("Role {0:?} not found in this choreography")]
    UnknownRole(String),

    /// Error with protocol execution context
    ///
    /// Wraps an inner error with information about where in the protocol
    /// the error occurred (protocol name, role, phase).
    #[error("{protocol}::{role} at phase '{phase}': {inner}")]
    ProtocolContext {
        /// Name of the protocol being executed
        protocol: &'static str,
        /// Name of the role executing when error occurred
        role: &'static str,
        /// Current phase/step in the protocol
        phase: &'static str,
        /// The underlying error
        #[source]
        inner: Box<ChoreographyError>,
    },

    /// Error with role-specific context
    #[error("[{role}] {inner}")]
    RoleContext {
        /// Name of the role where error occurred
        role: &'static str,
        /// Optional role index for parameterized roles
        index: Option<u32>,
        /// The underlying error
        #[source]
        inner: Box<ChoreographyError>,
    },

    /// Error during message exchange with another role
    #[error("{operation} {message_type} {direction} {other_role}: {inner}")]
    MessageContext {
        /// The operation being performed (send/recv)
        operation: &'static str,
        /// The type of message involved
        message_type: &'static str,
        /// Direction (to/from)
        direction: &'static str,
        /// The other role involved in the exchange
        other_role: &'static str,
        /// The underlying error
        #[source]
        inner: Box<ChoreographyError>,
    },

    /// Error during choice/branch operation
    #[error("Choice error at {role}: {details}")]
    ChoiceError {
        /// The role making or receiving the choice
        role: &'static str,
        /// Details about the choice error
        details: String,
    },

    /// Generic wrapped error with context string
    #[error("{context}: {inner}")]
    WithContext {
        /// Additional context about the error
        context: String,
        /// The underlying error
        #[source]
        inner: Box<ChoreographyError>,
    },

    /// Invalid choice: the chosen branch was not among expected options
    #[error("Invalid choice: expected one of {expected:?}, got {actual}")]
    InvalidChoice {
        /// Expected branch labels
        expected: Vec<String>,
        /// Actual branch label provided
        actual: String,
    },

    /// General execution error
    #[error("Execution error: {0}")]
    ExecutionError(String),
}

impl ChoreographyError {
    /// Wrap this error with protocol context.
    #[must_use]
    pub fn with_protocol_context(
        self,
        protocol: &'static str,
        role: &'static str,
        phase: &'static str,
    ) -> Self {
        ChoreographyError::ProtocolContext {
            protocol,
            role,
            phase,
            inner: Box::new(self),
        }
    }

    /// Wrap this error with role context.
    #[must_use]
    pub fn with_role_context(self, role: &'static str, index: Option<u32>) -> Self {
        ChoreographyError::RoleContext {
            role,
            index,
            inner: Box::new(self),
        }
    }

    /// Wrap this error with message exchange context.
    #[must_use]
    pub fn with_message_context(
        self,
        operation: &'static str,
        message_type: &'static str,
        direction: &'static str,
        other_role: &'static str,
    ) -> Self {
        ChoreographyError::MessageContext {
            operation,
            message_type,
            direction,
            other_role,
            inner: Box::new(self),
        }
    }

    /// Wrap this error with a generic context string.
    #[must_use]
    pub fn with_context(self, context: impl Into<String>) -> Self {
        ChoreographyError::WithContext {
            context: context.into(),
            inner: Box::new(self),
        }
    }

    /// Get the root cause of the error (unwrapping all context layers).
    #[must_use]
    pub fn root_cause(&self) -> &ChoreographyError {
        match self {
            ChoreographyError::ProtocolContext { inner, .. }
            | ChoreographyError::RoleContext { inner, .. }
            | ChoreographyError::MessageContext { inner, .. }
            | ChoreographyError::WithContext { inner, .. } => inner.root_cause(),
            _ => self,
        }
    }

    /// Check if this error is a timeout.
    #[must_use]
    pub fn is_timeout(&self) -> bool {
        matches!(self.root_cause(), ChoreographyError::Timeout(_))
    }

    /// Check if this error is a transport error.
    #[must_use]
    pub fn is_transport(&self) -> bool {
        matches!(self.root_cause(), ChoreographyError::Transport(_))
    }

    /// Check if this error is a protocol violation.
    #[must_use]
    pub fn is_protocol_violation(&self) -> bool {
        matches!(self.root_cause(), ChoreographyError::ProtocolViolation(_))
    }
}

/// Result type for choreography operations
pub type Result<T> = std::result::Result<T, ChoreographyError>;

/// Extension trait for adding context to Results.
///
/// This trait provides ergonomic methods for wrapping errors with
/// protocol/role/phase context.
pub trait ContextExt<T> {
    /// Add protocol context to an error.
    fn with_protocol_context(
        self,
        protocol: &'static str,
        role: &'static str,
        phase: &'static str,
    ) -> Result<T>;

    /// Add role context to an error.
    fn with_role_context(self, role: &'static str, index: Option<u32>) -> Result<T>;

    /// Add message context to an error.
    fn with_message_context(
        self,
        operation: &'static str,
        message_type: &'static str,
        direction: &'static str,
        other_role: &'static str,
    ) -> Result<T>;

    /// Add generic context to an error.
    fn with_context(self, context: impl Into<String>) -> Result<T>;
}

impl<T> ContextExt<T> for Result<T> {
    fn with_protocol_context(
        self,
        protocol: &'static str,
        role: &'static str,
        phase: &'static str,
    ) -> Result<T> {
        self.map_err(|e| e.with_protocol_context(protocol, role, phase))
    }

    fn with_role_context(self, role: &'static str, index: Option<u32>) -> Result<T> {
        self.map_err(|e| e.with_role_context(role, index))
    }

    fn with_message_context(
        self,
        operation: &'static str,
        message_type: &'static str,
        direction: &'static str,
        other_role: &'static str,
    ) -> Result<T> {
        self.map_err(|e| e.with_message_context(operation, message_type, direction, other_role))
    }

    fn with_context(self, context: impl Into<String>) -> Result<T> {
        self.map_err(|e| e.with_context(context))
    }
}

/// The core effect handler trait that abstracts all communication effects
///
/// This trait defines the primitive operations for choreographic protocols:
/// sending, receiving, choosing, offering, and timeouts. Implement this trait
/// to provide custom transport mechanisms (in-memory, network, etc.).
///
/// # Type Parameters
///
/// - `Role`: The type representing protocol participants
/// - `Endpoint`: The connection state for this protocol execution
///
/// # Async implementation notes
///
/// We deliberately use the `async_trait` macro here so the trait stays object-safe,
/// which lets middleware stacks (e.g. `Trace<Retry<H>>`) erase handlers behind trait
/// objects. The macro also enforces `Send` on all returned futures, so the bounds on
/// methods like [`with_timeout`](ChoreoHandler::with_timeout) apply equally to native
/// multithreaded runtimes and single-threaded WASM builds.
#[async_trait]
pub trait ChoreoHandler: Send {
    /// The role type for this choreography
    type Role: RoleId;
    /// The endpoint type maintaining connection state
    type Endpoint: Endpoint;

    /// Send a message to a specific role
    ///
    /// # Arguments
    ///
    /// * `ep` - The session endpoint
    /// * `to` - The recipient role
    /// * `msg` - The message to send (must be serializable)
    async fn send<M: Serialize + Send + Sync>(
        &mut self,
        ep: &mut Self::Endpoint,
        to: Self::Role,
        msg: &M,
    ) -> Result<()>;

    /// Receive a strongly-typed message from a specific role
    ///
    /// # Arguments
    ///
    /// * `ep` - The session endpoint
    /// * `from` - The sender role
    ///
    /// # Returns
    ///
    /// The received message of type `M`
    async fn recv<M: DeserializeOwned + Send>(
        &mut self,
        ep: &mut Self::Endpoint,
        from: Self::Role,
    ) -> Result<M>;

    /// Internal choice: broadcast a label selection
    ///
    /// Used by the choosing role to inform others of the selected branch.
    ///
    /// # Arguments
    ///
    /// * `ep` - The session endpoint
    /// * `who` - The role making the choice (usually the current role)
    /// * `label` - The selected branch label
    async fn choose(
        &mut self,
        ep: &mut Self::Endpoint,
        who: Self::Role,
        label: Label,
    ) -> Result<()>;

    /// External choice: receive a label selection
    ///
    /// Used by non-choosing roles to receive the branch selection from another role.
    ///
    /// # Arguments
    ///
    /// * `ep` - The session endpoint
    /// * `from` - The role that made the choice
    ///
    /// # Returns
    ///
    /// The label selected by the choosing role
    async fn offer(&mut self, ep: &mut Self::Endpoint, from: Self::Role) -> Result<Label>;

    /// Execute a future with a timeout
    ///
    /// # Arguments
    ///
    /// * `ep` - The session endpoint
    /// * `at` - The role where timeout is enforced
    /// * `dur` - Maximum duration to wait
    /// * `body` - The future to execute
    ///
    /// # Returns
    ///
    /// Result of the future, or timeout error if duration exceeded
    async fn with_timeout<F, T>(
        &mut self,
        ep: &mut Self::Endpoint,
        at: Self::Role,
        dur: Duration,
        body: F,
    ) -> Result<T>
    where
        F: std::future::Future<Output = Result<T>> + Send;

    /// Broadcast a message to multiple recipients
    ///
    /// Default implementation sends sequentially. Override for optimized broadcasting.
    async fn broadcast<M: Serialize + Send + Sync>(
        &mut self,
        ep: &mut Self::Endpoint,
        recipients: &[Self::Role],
        msg: &M,
    ) -> Result<()> {
        for &recipient in recipients {
            self.send(ep, recipient, msg).await?;
        }
        Ok(())
    }

    /// Send messages to multiple recipients in parallel
    ///
    /// Default implementation sends sequentially. Override for true parallelism.
    async fn parallel_send<M: Serialize + Send + Sync>(
        &mut self,
        ep: &mut Self::Endpoint,
        sends: &[(Self::Role, M)],
    ) -> Result<()> {
        // Default implementation: sequential sends
        for (recipient, msg) in sends {
            self.send(ep, *recipient, msg).await?;
        }
        Ok(())
    }
}

/// Extension trait for handler lifecycle management
///
/// Provides setup and teardown methods for managing handler state and connections.
#[async_trait]
pub trait ChoreoHandlerExt: ChoreoHandler {
    /// Setup phase - establish connections, initialize state
    ///
    /// Called before protocol execution begins.
    async fn setup(&mut self, role: Self::Role) -> Result<Self::Endpoint>;

    /// Teardown phase - close connections, cleanup
    ///
    /// Called after protocol execution completes.
    async fn teardown(&mut self, ep: Self::Endpoint) -> Result<()>;
}

/// A no-op handler for testing pure choreographic logic
///
/// This handler performs no actual communication, making it useful for
/// testing protocol logic without network overhead.
pub struct NoOpHandler<R: RoleId> {
    _phantom: std::marker::PhantomData<R>,
    registry: ExtensionRegistry<()>,
}

impl<R: RoleId> NoOpHandler<R> {
    /// Create a new no-op handler
    #[must_use]
    pub fn new() -> Self {
        Self {
            _phantom: std::marker::PhantomData,
            registry: ExtensionRegistry::new(),
        }
    }
}

impl<R: RoleId> Default for NoOpHandler<R> {
    fn default() -> Self {
        Self::new()
    }
}

#[async_trait]
impl<R: RoleId + 'static> ExtensibleHandler for NoOpHandler<R> {
    type Endpoint = ();

    fn extension_registry(&self) -> &ExtensionRegistry<Self::Endpoint> {
        &self.registry
    }
}

#[async_trait]
impl<R: RoleId + 'static> ChoreoHandler for NoOpHandler<R> {
    type Role = R;
    type Endpoint = ();

    async fn send<M: Serialize + Send + Sync>(
        &mut self,
        _ep: &mut Self::Endpoint,
        _to: Self::Role,
        _msg: &M,
    ) -> Result<()> {
        Ok(())
    }

    async fn recv<M: DeserializeOwned + Send>(
        &mut self,
        _ep: &mut Self::Endpoint,
        _from: Self::Role,
    ) -> Result<M> {
        Err(ChoreographyError::Transport(
            "NoOpHandler cannot receive".into(),
        ))
    }

    async fn choose(
        &mut self,
        _ep: &mut Self::Endpoint,
        _who: Self::Role,
        _label: Label,
    ) -> Result<()> {
        Ok(())
    }

    async fn offer(&mut self, _ep: &mut Self::Endpoint, _from: Self::Role) -> Result<Label> {
        Err(ChoreographyError::Transport(
            "NoOpHandler cannot offer".into(),
        ))
    }

    async fn with_timeout<F, T>(
        &mut self,
        _ep: &mut Self::Endpoint,
        _at: Self::Role,
        _dur: Duration,
        body: F,
    ) -> Result<T>
    where
        F: std::future::Future<Output = Result<T>> + Send,
    {
        body.await
    }
}
