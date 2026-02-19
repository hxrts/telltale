//! Internal AST types for parsing.
//!
//! These types represent the intermediate parse tree before conversion
//! to the final Protocol AST.

use crate::ast::Role;
use proc_macro2::{Ident, TokenStream};
use std::collections::HashMap;

use super::error::ErrorSpan;

/// Choreography statement types
#[derive(Debug, Clone)]
#[allow(clippy::large_enum_variant)] // Statement enum is internal to parser; performance impact is minimal
pub(crate) enum Statement {
    Send {
        from: Role,
        to: Role,
        message: MessageSpec,
        annotations: HashMap<String, String>,
        from_annotations: HashMap<String, String>,
        to_annotations: HashMap<String, String>,
    },
    Broadcast {
        from: Role,
        message: MessageSpec,
        annotations: HashMap<String, String>,
        from_annotations: HashMap<String, String>,
    },
    Choice {
        role: Role,
        branches: Vec<ChoiceBranch>,
        annotations: HashMap<String, String>,
    },
    /// Timed choice: actor makes a choice based on wall clock timeout.
    /// Desugars to standard Choice with timeout annotation for code generation.
    TimedChoice {
        role: Role,
        duration_ms: u64,
        branches: Vec<ChoiceBranch>,
    },
    /// Heartbeat: sender sends periodic heartbeats, receiver detects absence.
    /// Desugars to recursive choice with liveness detection.
    Heartbeat {
        sender: Role,
        receiver: Role,
        interval_ms: u64,
        on_missing_count: u32,
        on_missing_body: Vec<Statement>,
        body: Vec<Statement>,
    },
    Loop {
        condition: Option<crate::ast::Condition>,
        body: Vec<Statement>,
    },
    Branch {
        body: Vec<Statement>,
        span: ErrorSpan,
    },
    Parallel {
        branches: Vec<Vec<Statement>>,
    },
    Rec {
        label: Ident,
        body: Vec<Statement>,
    },
    /// Recursive back-reference (continue to a rec label)
    Continue {
        label: Ident,
    },
    Call {
        name: Ident,
    },
    VmCoreOp {
        op: VmCoreOp,
    },
}

/// VM-core statement op parsed from DSL.
#[derive(Debug, Clone)]
pub(crate) enum VmCoreOp {
    Acquire {
        layer: String,
        dst: String,
    },
    Release {
        layer: String,
        evidence: String,
    },
    Fork {
        ghost: String,
    },
    Join,
    Abort,
    Transfer {
        endpoint: String,
        target: String,
        bundle: Option<String>,
    },
    Tag {
        fact: String,
        dst: String,
    },
    Check {
        knowledge: String,
        target_role: String,
        dst: String,
    },
}

impl VmCoreOp {
    pub(crate) fn op_name(&self) -> &'static str {
        match self {
            Self::Acquire { .. } => "acquire",
            Self::Release { .. } => "release",
            Self::Fork { .. } => "fork",
            Self::Join => "join",
            Self::Abort => "abort",
            Self::Transfer { .. } => "transfer",
            Self::Tag { .. } => "tag",
            Self::Check { .. } => "check",
        }
    }

    pub(crate) fn required_capability(&self) -> &'static str {
        match self {
            Self::Acquire { .. } | Self::Release { .. } => "guard_tokens",
            Self::Fork { .. } | Self::Join | Self::Abort => "speculation",
            Self::Transfer { .. } => "delegation",
            Self::Tag { .. } | Self::Check { .. } => "knowledge_flow",
        }
    }
}

/// Choice branch in choreography
#[derive(Debug, Clone)]
pub(crate) struct ChoiceBranch {
    pub label: Ident,
    pub guard: Option<TokenStream>,
    pub statements: Vec<Statement>,
}

/// Message specification with optional payload
#[derive(Debug, Clone)]
pub(crate) struct MessageSpec {
    pub name: Ident,
    pub type_annotation: Option<TokenStream>,
    pub payload: Option<TokenStream>,
}

/// Parsed protocol body result
pub(crate) struct ParsedBody {
    pub roles: Option<Vec<Role>>,
    pub statements: Vec<Statement>,
}
