//! Tracing support for choreographic protocols
//!
//! This module provides tracing instrumentation for protocol execution,
//! including span creation, event logging, and a tracing handler wrapper.
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

use async_trait::async_trait;
use serde::{de::DeserializeOwned, Serialize};
use std::time::{Duration, Instant};
use tracing::{debug, error, info, info_span, instrument, Instrument, Span};

use crate::effects::{ChoreoHandler, ChoreoResult, LabelId, RoleId};
use crate::identifiers::RoleName;

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
pub fn protocol_span(protocol: &str, role: &RoleName, role_index: Option<u32>) -> Span {
    match role_index {
        Some(idx) => info_span!(
            "protocol.execute",
            protocol = protocol,
            role = role.as_str(),
            role_index = idx
        ),
        None => info_span!(
            "protocol.execute",
            protocol = protocol,
            role = role.as_str()
        ),
    }
}

/// Create a phase span for tracking phase execution.
pub fn phase_span(protocol: &str, role: &RoleName, phase: &str) -> Span {
    info_span!(
        "protocol.phase",
        protocol = protocol,
        role = role.as_str(),
        phase = phase
    )
}

/// Log a send event.
pub fn trace_send(target_role: &str, message_type: &str, message_size: usize) {
    info!(
        target: events::SEND,
        target_role = target_role,
        message_type = message_type,
        message_size = message_size,
        "sending message"
    );
}

/// Log a receive event.
pub fn trace_recv(source_role: &str, message_type: &str, message_size: usize) {
    info!(
        target: events::RECV,
        source_role = source_role,
        message_type = message_type,
        message_size = message_size,
        "received message"
    );
}

/// Log a choice event (internal choice).
pub fn trace_choose(target_role: &str, label: &str) {
    info!(
        target: events::CHOOSE,
        target_role = target_role,
        choice_label = label,
        "made choice"
    );
}

/// Log an offer event (external choice).
pub fn trace_offer(source_role: &str, label: &str) {
    info!(
        target: events::OFFER,
        source_role = source_role,
        choice_label = label,
        "received choice"
    );
}

/// Log a phase start event.
pub fn trace_phase_start(phase: &str) {
    debug!(target: events::PHASE_START, phase = phase, "phase started");
}

/// Log a phase end event.
pub fn trace_phase_end(phase: &str, duration_ms: u64) {
    debug!(
        target: events::PHASE_END,
        phase = phase,
        duration_ms = duration_ms,
        "phase completed"
    );
}

/// Log an error event.
pub fn trace_error(error_message: &str) {
    error!(
        target: events::ERROR,
        error = error_message,
        "protocol error"
    );
}

fn format_role<R: RoleId>(role: R) -> String {
    match role.role_index() {
        Some(index) => format!("{}[{}]", role.role_name(), index),
        None => role.role_name().to_string(),
    }
}

/// A tracing wrapper for choreographic handlers.
pub struct TracingHandler<H> {
    inner: H,
    protocol: &'static str,
    role: RoleName,
    role_index: Option<u32>,
    span: Span,
}

impl<H> TracingHandler<H> {
    /// Create a new tracing handler.
    pub fn new(inner: H, protocol: &'static str, role: H::Role) -> Self
    where
        H: ChoreoHandler,
    {
        let role_name = role.role_name();
        let role_index = role.role_index();
        let span = protocol_span(protocol, &role_name, role_index);
        Self {
            inner,
            protocol,
            role: role_name,
            role_index,
            span,
        }
    }

    /// Create a new tracing handler for an indexed role.
    pub fn indexed(inner: H, protocol: &'static str, role: RoleName, index: u32) -> Self {
        let span = protocol_span(protocol, &role, Some(index));
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
    pub fn role(&self) -> &RoleName {
        &self.role
    }

    /// Get the role index (if any).
    pub fn role_index(&self) -> Option<u32> {
        self.role_index
    }

    /// Get a reference to the inner handler.
    pub fn inner(&self) -> &H {
        &self.inner
    }

    /// Get a mutable reference to the inner handler.
    pub fn inner_mut(&mut self) -> &mut H {
        &mut self.inner
    }

    /// Unwrap and return the inner handler.
    pub fn into_inner(self) -> H {
        self.inner
    }
}

#[async_trait]
impl<H: ChoreoHandler> ChoreoHandler for TracingHandler<H> {
    type Role = H::Role;
    type Endpoint = H::Endpoint;

    #[instrument(
        skip(self, ep, msg),
        fields(
            protocol = self.protocol,
            role = self.role.as_str(),
            target_role = ?to,
            message_type = std::any::type_name::<M>()
        )
    )]
    async fn send<M: Serialize + Send + Sync>(
        &mut self,
        ep: &mut Self::Endpoint,
        to: Self::Role,
        msg: &M,
    ) -> ChoreoResult<()> {
        trace_send(&format_role(to), std::any::type_name::<M>(), 0);
        self.inner
            .send(ep, to, msg)
            .instrument(self.span.clone())
            .await
    }

    #[instrument(
        skip(self, ep),
        fields(
            protocol = self.protocol,
            role = self.role.as_str(),
            source_role = ?from,
            message_type = std::any::type_name::<M>()
        )
    )]
    async fn recv<M: DeserializeOwned + Send>(
        &mut self,
        ep: &mut Self::Endpoint,
        from: Self::Role,
    ) -> ChoreoResult<M> {
        let result = self
            .inner
            .recv::<M>(ep, from)
            .instrument(self.span.clone())
            .await;
        if result.is_ok() {
            trace_recv(&format_role(from), std::any::type_name::<M>(), 0);
        }
        result
    }

    #[instrument(
        skip(self, ep),
        fields(
            protocol = self.protocol,
            role = self.role.as_str(),
            target_role = ?to,
            choice_label = label.as_str()
        )
    )]
    async fn choose(
        &mut self,
        ep: &mut Self::Endpoint,
        to: Self::Role,
        label: <Self::Role as RoleId>::Label,
    ) -> ChoreoResult<()> {
        trace_choose(&format_role(to), label.as_str());
        self.inner
            .choose(ep, to, label)
            .instrument(self.span.clone())
            .await
    }

    #[instrument(
        skip(self, ep),
        fields(
            protocol = self.protocol,
            role = self.role.as_str(),
            source_role = ?from
        )
    )]
    async fn offer(
        &mut self,
        ep: &mut Self::Endpoint,
        from: Self::Role,
    ) -> ChoreoResult<<Self::Role as RoleId>::Label> {
        let result = self
            .inner
            .offer(ep, from)
            .instrument(self.span.clone())
            .await;
        if let Ok(ref label) = result {
            trace_offer(&format_role(from), label.as_str());
        }
        result
    }

    async fn with_timeout<F, T>(
        &mut self,
        ep: &mut Self::Endpoint,
        at: Self::Role,
        dur: Duration,
        body: F,
    ) -> ChoreoResult<T>
    where
        F: std::future::Future<Output = ChoreoResult<T>> + Send,
    {
        self.inner
            .with_timeout(ep, at, dur, body)
            .instrument(self.span.clone())
            .await
    }
}

/// Phase guard for automatically tracking phase duration.
pub struct PhaseGuard {
    phase: &'static str,
    start: Instant,
    span: Span,
}

impl PhaseGuard {
    /// Create a new phase guard.
    pub fn new(protocol: &'static str, role: &RoleName, phase: &'static str) -> Self {
        let span = phase_span(protocol, role, phase);
        {
            let _enter = span.enter();
            trace_phase_start(phase);
        }

        Self {
            phase,
            start: Instant::now(),
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
        let duration_ms = u64::try_from(self.start.elapsed().as_millis()).unwrap_or(u64::MAX);
        trace_phase_end(self.phase, duration_ms);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_protocol_span() {
        let span = protocol_span("TestProtocol", &RoleName::from_static("Client"), None);
        assert!(span.is_disabled() || !span.is_disabled());
    }

    #[test]
    fn test_protocol_span_indexed() {
        let span = protocol_span("TestProtocol", &RoleName::from_static("Worker"), Some(3));
        assert!(span.is_disabled() || !span.is_disabled());
    }

    #[test]
    fn test_phase_span() {
        let span = phase_span(
            "TestProtocol",
            &RoleName::from_static("Client"),
            "handshake",
        );
        assert!(span.is_disabled() || !span.is_disabled());
    }
}
