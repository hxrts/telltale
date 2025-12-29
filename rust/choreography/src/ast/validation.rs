// Validation error types

/// Choreography validation errors
#[derive(Debug, Clone, thiserror::Error)]
pub enum ValidationError {
    #[error("Role {0} not declared in choreography")]
    UndefinedRole(String),

    #[error("Recursive variable {0} not bound")]
    UnboundVariable(String),

    #[error("Choice role {0} must be sender in all branches")]
    InvalidChoice(String),

    #[error("Deadlock detected in protocol")]
    Deadlock,

    #[error("Role {0} is not used in protocol")]
    UnusedRole(String),

    #[error("Extension error: {0}")]
    ExtensionError(String),
}
