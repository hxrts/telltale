//! Errors surfaced by the viewer model and service layer.

use std::fmt;

/// Errors surfaced by the pure model/service layer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ViewerModelError {
    Io { path: String, message: String },
    InvalidArtifactFile { message: String },
    UnsupportedSchemaVersion { supported: u32, found: u32 },
    NotFound { kind: String, id: String },
    Serialization { message: String },
    UnexpectedQueryShape { expected: String },
}

impl fmt::Display for ViewerModelError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io { path, message } => write!(f, "io error for {path}: {message}"),
            Self::InvalidArtifactFile { message } => write!(f, "{message}"),
            Self::UnsupportedSchemaVersion { supported, found } => write!(
                f,
                "unsupported artifact schema version {found}; expected {supported}"
            ),
            Self::NotFound { kind, id } => write!(f, "missing {kind} `{id}`"),
            Self::Serialization { message } => write!(f, "serialization error: {message}"),
            Self::UnexpectedQueryShape { expected } => {
                write!(
                    f,
                    "application service returned an unexpected query result; expected {expected}"
                )
            }
        }
    }
}

impl std::error::Error for ViewerModelError {}
