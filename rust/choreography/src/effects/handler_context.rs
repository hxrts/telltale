use super::{ChoreoResult, ChoreographyError};

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
        matches!(
            self.root_cause(),
            ChoreographyError::Transport(_)
                | ChoreographyError::ChannelSendFailed { .. }
                | ChoreographyError::ChannelClosed { .. }
                | ChoreographyError::NoPeerChannel { .. }
        )
    }

    /// Check if this error is a protocol violation.
    #[must_use]
    pub fn is_protocol_violation(&self) -> bool {
        matches!(self.root_cause(), ChoreographyError::ProtocolViolation(_))
    }

    /// Check if this error is a serialization error.
    #[must_use]
    pub fn is_serialization(&self) -> bool {
        matches!(
            self.root_cause(),
            ChoreographyError::Serialization(_)
                | ChoreographyError::LabelSerializationFailed { .. }
                | ChoreographyError::MessageSerializationFailed { .. }
        )
    }
}

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
    ) -> ChoreoResult<T>;

    /// Add role context to an error.
    fn with_role_context(self, role: &'static str, index: Option<u32>) -> ChoreoResult<T>;

    /// Add message context to an error.
    fn with_message_context(
        self,
        operation: &'static str,
        message_type: &'static str,
        direction: &'static str,
        other_role: &'static str,
    ) -> ChoreoResult<T>;

    /// Add generic context to an error.
    fn with_context(self, context: impl Into<String>) -> ChoreoResult<T>;
}

impl<T> ContextExt<T> for ChoreoResult<T> {
    fn with_protocol_context(
        self,
        protocol: &'static str,
        role: &'static str,
        phase: &'static str,
    ) -> ChoreoResult<T> {
        self.map_err(|e| e.with_protocol_context(protocol, role, phase))
    }

    fn with_role_context(self, role: &'static str, index: Option<u32>) -> ChoreoResult<T> {
        self.map_err(|e| e.with_role_context(role, index))
    }

    fn with_message_context(
        self,
        operation: &'static str,
        message_type: &'static str,
        direction: &'static str,
        other_role: &'static str,
    ) -> ChoreoResult<T> {
        self.map_err(|e| e.with_message_context(operation, message_type, direction, other_role))
    }

    fn with_context(self, context: impl Into<String>) -> ChoreoResult<T> {
        self.map_err(|e| e.with_context(context))
    }
}
