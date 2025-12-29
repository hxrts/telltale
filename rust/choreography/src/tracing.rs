//! Tracing support for choreographic protocols
//!
//! This module provides tracing instrumentation for protocol execution,
//! including span creation, event logging, and a tracing adapter wrapper.
//!
//! # Standard Span Fields
//!
//! All protocol spans include these fields:
//! - `protocol`: Name of the protocol being executed
//! - `role`: Name of the role executing
//! - `role_index`: Optional index for parameterized roles
//!
//! # Event Types
//!
//! Standard events emitted during protocol execution:
//! - `protocol.send`: Message sent to another role
//! - `protocol.recv`: Message received from another role
//! - `protocol.choose`: Choice made (internal choice)
//! - `protocol.offer`: Choice received (external choice)
//! - `protocol.phase.start`: Phase started
//! - `protocol.phase.end`: Phase completed
//! - `protocol.error`: Error occurred
//!
//! # Example
//!
//! ```ignore
//! use rumpsteak_aura_choreography::tracing::{TracingAdapter, ProtocolSpan};
//!
//! // Wrap an adapter with tracing
//! let traced = TracingAdapter::new(my_adapter, "MyProtocol", "Client");
//!
//! // Use the traced adapter - all operations are automatically traced
//! traced.send(RoleId::new("Server"), message).await?;
//! ```

use async_trait::async_trait;
use tracing::{debug, error, info, info_span, instrument, Instrument, Span};

use crate::runtime::adapter::{ChoreographicAdapter, Message, RoleId};

/// Standard span field names for protocol execution.
pub mod fields {
    /// Protocol name field
    pub const PROTOCOL: &str = "protocol";
    /// Role name field
    pub const ROLE: &str = "role";
    /// Role index field (for parameterized roles)
    pub const ROLE_INDEX: &str = "role_index";
    /// Phase name field
    pub const PHASE: &str = "phase";
    /// Message type field
    pub const MESSAGE_TYPE: &str = "message_type";
    /// Message size field
    pub const MESSAGE_SIZE: &str = "message_size";
    /// Target role field (for send operations)
    pub const TARGET_ROLE: &str = "target_role";
    /// Source role field (for receive operations)
    pub const SOURCE_ROLE: &str = "source_role";
    /// Choice label field
    pub const CHOICE_LABEL: &str = "choice_label";
    /// Duration field (in milliseconds)
    pub const DURATION_MS: &str = "duration_ms";
    /// Error message field
    pub const ERROR: &str = "error";
}

/// Event names for protocol operations.
pub mod events {
    /// Message send event
    pub const SEND: &str = "protocol.send";
    /// Message receive event
    pub const RECV: &str = "protocol.recv";
    /// Choice made event (internal choice)
    pub const CHOOSE: &str = "protocol.choose";
    /// Choice received event (external choice)
    pub const OFFER: &str = "protocol.offer";
    /// Phase start event
    pub const PHASE_START: &str = "protocol.phase.start";
    /// Phase end event
    pub const PHASE_END: &str = "protocol.phase.end";
    /// Error event
    pub const ERROR: &str = "protocol.error";
}

/// Create a protocol execution span.
///
/// This creates a new span with standard protocol fields that can be used
/// as the root span for protocol execution.
pub fn protocol_span(protocol: &str, role: &str, role_index: Option<u32>) -> Span {
    match role_index {
        Some(idx) => info_span!(
            "protocol.execute",
            protocol = protocol,
            role = role,
            role_index = idx
        ),
        None => info_span!("protocol.execute", protocol = protocol, role = role),
    }
}

/// Create a phase span for tracking phase execution.
pub fn phase_span(protocol: &str, role: &str, phase: &str) -> Span {
    info_span!(
        "protocol.phase",
        protocol = protocol,
        role = role,
        phase = phase
    )
}

/// Log a send event.
pub fn trace_send(target_role: &str, message_type: &str, message_size: usize) {
    info!(
        target: "protocol.send",
        target_role = target_role,
        message_type = message_type,
        message_size = message_size,
        "sending message"
    );
}

/// Log a receive event.
pub fn trace_recv(source_role: &str, message_type: &str, message_size: usize) {
    info!(
        target: "protocol.recv",
        source_role = source_role,
        message_type = message_type,
        message_size = message_size,
        "received message"
    );
}

/// Log a choice event (internal choice).
pub fn trace_choose(target_role: &str, label: &str) {
    info!(
        target: "protocol.choose",
        target_role = target_role,
        choice_label = label,
        "made choice"
    );
}

/// Log an offer event (external choice).
pub fn trace_offer(source_role: &str, label: &str) {
    info!(
        target: "protocol.offer",
        source_role = source_role,
        choice_label = label,
        "received choice"
    );
}

/// Log a phase start event.
pub fn trace_phase_start(phase: &str) {
    debug!(target: "protocol.phase.start", phase = phase, "phase started");
}

/// Log a phase end event.
pub fn trace_phase_end(phase: &str, duration_ms: u64) {
    debug!(
        target: "protocol.phase.end",
        phase = phase,
        duration_ms = duration_ms,
        "phase completed"
    );
}

/// Log an error event.
pub fn trace_error(error: &str) {
    error!(target: "protocol.error", error = error, "protocol error");
}

/// A tracing wrapper for choreographic adapters.
///
/// Wraps any `ChoreographicAdapter` to automatically add tracing instrumentation
/// to all operations.
pub struct TracingAdapter<A> {
    inner: A,
    protocol: &'static str,
    role: &'static str,
    role_index: Option<u32>,
    span: Span,
}

impl<A> TracingAdapter<A> {
    /// Create a new tracing adapter.
    pub fn new(inner: A, protocol: &'static str, role: &'static str) -> Self {
        let span = protocol_span(protocol, role, None);
        Self {
            inner,
            protocol,
            role,
            role_index: None,
            span,
        }
    }

    /// Create a new tracing adapter for an indexed role.
    pub fn indexed(inner: A, protocol: &'static str, role: &'static str, index: u32) -> Self {
        let span = protocol_span(protocol, role, Some(index));
        Self {
            inner,
            protocol,
            role,
            role_index: Some(index),
            span,
        }
    }

    /// Get the protocol name.
    pub fn protocol(&self) -> &'static str {
        self.protocol
    }

    /// Get the role name.
    pub fn role(&self) -> &'static str {
        self.role
    }

    /// Get the role index (if any).
    pub fn role_index(&self) -> Option<u32> {
        self.role_index
    }

    /// Get a reference to the inner adapter.
    pub fn inner(&self) -> &A {
        &self.inner
    }

    /// Get a mutable reference to the inner adapter.
    pub fn inner_mut(&mut self) -> &mut A {
        &mut self.inner
    }

    /// Unwrap and return the inner adapter.
    pub fn into_inner(self) -> A {
        self.inner
    }
}

#[async_trait]
impl<A: ChoreographicAdapter> ChoreographicAdapter for TracingAdapter<A> {
    type Error = A::Error;

    #[instrument(
        skip(self, msg),
        fields(
            protocol = self.protocol,
            role = self.role,
            target_role = %to,
            message_type = std::any::type_name::<M>()
        )
    )]
    async fn send<M: Message>(&mut self, to: RoleId, msg: M) -> Result<(), Self::Error> {
        trace_send(&to.to_string(), std::any::type_name::<M>(), 0);
        self.inner.send(to, msg).instrument(self.span.clone()).await
    }

    #[instrument(
        skip(self),
        fields(
            protocol = self.protocol,
            role = self.role,
            source_role = %from,
            message_type = std::any::type_name::<M>()
        )
    )]
    async fn recv<M: Message>(&mut self, from: RoleId) -> Result<M, Self::Error> {
        let result = self
            .inner
            .recv::<M>(from.clone())
            .instrument(self.span.clone())
            .await;
        if result.is_ok() {
            trace_recv(&from.to_string(), std::any::type_name::<M>(), 0);
        }
        result
    }

    #[instrument(
        skip(self, msg),
        fields(
            protocol = self.protocol,
            role = self.role,
            targets = ?to
        )
    )]
    async fn broadcast<M: Message + Clone>(
        &mut self,
        to: &[RoleId],
        msg: M,
    ) -> Result<(), Self::Error> {
        for target in to {
            trace_send(&target.to_string(), std::any::type_name::<M>(), 0);
        }
        self.inner
            .broadcast(to, msg)
            .instrument(self.span.clone())
            .await
    }

    #[instrument(
        skip(self),
        fields(
            protocol = self.protocol,
            role = self.role,
            sources = ?from
        )
    )]
    async fn collect<M: Message>(&mut self, from: &[RoleId]) -> Result<Vec<M>, Self::Error> {
        let result = self
            .inner
            .collect::<M>(from)
            .instrument(self.span.clone())
            .await;
        if result.is_ok() {
            for source in from {
                trace_recv(&source.to_string(), std::any::type_name::<M>(), 0);
            }
        }
        result
    }

    #[instrument(
        skip(self),
        fields(
            protocol = self.protocol,
            role = self.role,
            target_role = %to,
            choice_label = label
        )
    )]
    async fn choose(&mut self, to: RoleId, label: &str) -> Result<(), Self::Error> {
        trace_choose(&to.to_string(), label);
        self.inner
            .choose(to, label)
            .instrument(self.span.clone())
            .await
    }

    #[instrument(
        skip(self),
        fields(
            protocol = self.protocol,
            role = self.role,
            source_role = %from
        )
    )]
    async fn offer(&mut self, from: RoleId) -> Result<String, Self::Error> {
        let result = self
            .inner
            .offer(from.clone())
            .instrument(self.span.clone())
            .await;
        if let Ok(ref label) = result {
            trace_offer(&from.to_string(), label);
        }
        result
    }
}

/// Phase guard for automatically tracking phase duration.
///
/// When dropped, logs the phase end event with duration.
pub struct PhaseGuard {
    phase: &'static str,
    start: std::time::Instant,
    span: Span,
}

impl PhaseGuard {
    /// Create a new phase guard.
    pub fn new(protocol: &'static str, role: &'static str, phase: &'static str) -> Self {
        let span = phase_span(protocol, role, phase);
        // Log phase start within the span
        {
            let _enter = span.enter();
            trace_phase_start(phase);
        }

        Self {
            phase,
            start: std::time::Instant::now(),
            span,
        }
    }

    /// Get the span for this phase.
    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl Drop for PhaseGuard {
    fn drop(&mut self) {
        let _enter = self.span.enter();
        let duration_ms = self.start.elapsed().as_millis() as u64;
        trace_phase_end(self.phase, duration_ms);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_protocol_span() {
        let span = protocol_span("TestProtocol", "Client", None);
        assert!(span.is_disabled() || !span.is_disabled()); // Just check it doesn't panic
    }

    #[test]
    fn test_protocol_span_indexed() {
        let span = protocol_span("TestProtocol", "Worker", Some(3));
        assert!(span.is_disabled() || !span.is_disabled());
    }

    #[test]
    fn test_phase_span() {
        let span = phase_span("TestProtocol", "Client", "handshake");
        assert!(span.is_disabled() || !span.is_disabled());
    }
}
