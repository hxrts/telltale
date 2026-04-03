//! Integration-oriented helpers built on top of the shared choreography frontend.
//!
//! These APIs are intended for downstream crates that need validated ASTs,
//! projected local types, theory-facing artifacts, or ordered annotation
//! extraction without reimplementing Telltale's frontend pipeline.

use crate::ast::{
    choreography_to_global, local_to_local_r, Choreography, ConversionError, DslAnnotationEntry,
    LocalType, Protocol, Role,
};
use crate::compiler::parser::{parse_choreography_str, ParseError};
use crate::compiler::projection::{project, ProjectionError};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

/// Scope for one collected annotation record.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum AnnotationScope {
    /// Annotation attached to the statement itself.
    Statement,
    /// Annotation attached to the sender side of a statement.
    Sender,
    /// Annotation attached to the receiver side of a statement.
    Receiver,
}

/// One ordered annotation record collected from the AST.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProtocolAnnotationRecord {
    /// Structural path to the protocol node.
    pub path: String,
    /// Protocol node kind such as `send`, `choice`, or `broadcast`.
    pub node_kind: String,
    /// Whether the annotation came from statement, sender, or receiver metadata.
    pub scope: AnnotationScope,
    /// Role most directly associated with the annotation.
    pub role: Option<String>,
    /// Peer roles associated with the protocol node.
    #[serde(default)]
    pub peer_roles: Vec<String>,
    /// Raw annotation key.
    pub key: String,
    /// Raw annotation value.
    pub value: String,
}

/// Parsed choreography plus projected locals for integration work.
#[derive(Debug)]
pub struct CompiledChoreography {
    /// Validated authoritative choreography AST.
    pub choreography: Choreography,
    /// Per-role projected local types in choreography role order.
    pub local_types: Vec<(Role, LocalType)>,
}

impl CompiledChoreography {
    /// Return role names in choreography source order.
    #[must_use]
    pub fn role_names(&self) -> Vec<String> {
        self.choreography
            .roles
            .iter()
            .map(|role| role.name().to_string())
            .collect()
    }

    /// Look up one projected local type by role name.
    #[must_use]
    pub fn local_type(&self, role_name: &str) -> Option<&LocalType> {
        self.local_types.iter().find_map(|(role, local_type)| {
            (role.name().to_string() == role_name).then_some(local_type)
        })
    }

    /// Convert the authoritative choreography to a theory-level global type.
    ///
    /// This only succeeds for the subset of the DSL that has a direct theory
    /// correspondence.
    pub fn try_global_type(&self) -> Result<crate::ast::GlobalTypeCore, ConversionError> {
        choreography_to_global(&self.choreography)
    }

    /// Convert projected locals to theory-level local types keyed by role name.
    pub fn try_local_type_r_map(
        &self,
    ) -> Result<BTreeMap<String, crate::ast::LocalTypeR>, ConversionError> {
        let mut out = BTreeMap::new();
        for (role, local_type) in &self.local_types {
            out.insert(role.name().to_string(), local_to_local_r(local_type)?);
        }
        Ok(out)
    }

    /// Serialize the theory-level global type as JSON.
    pub fn global_type_json(&self) -> Result<String, CompileArtifactsError> {
        let global = self
            .try_global_type()
            .map_err(CompileArtifactsError::Conversion)?;
        serde_json::to_string(&global).map_err(CompileArtifactsError::Serialization)
    }

    /// Serialize theory-level local types as JSON.
    pub fn local_type_r_json(&self) -> Result<String, CompileArtifactsError> {
        let locals = self
            .try_local_type_r_map()
            .map_err(CompileArtifactsError::Conversion)?;
        serde_json::to_string(&locals).map_err(CompileArtifactsError::Serialization)
    }

    /// Collect ordered annotation records from the authoritative choreography AST.
    #[must_use]
    pub fn annotation_records(&self) -> Vec<ProtocolAnnotationRecord> {
        collect_choreography_annotation_records(&self.choreography)
    }
}

/// Errors produced by the integration helpers.
#[derive(Debug, thiserror::Error)]
pub enum CompileArtifactsError {
    #[error("parse error: {0}")]
    Parse(#[from] ParseError),

    #[error("validation error: {0}")]
    Validation(String),

    #[error("projection failed for role {role}: {source}")]
    Projection {
        role: String,
        #[source]
        source: ProjectionError,
    },

    #[error("theory conversion failed: {0}")]
    Conversion(#[from] ConversionError),

    #[error("serialization failed: {0}")]
    Serialization(#[from] serde_json::Error),
}

/// Parse, validate, and project a choreography from DSL source text.
pub fn compile_choreography(input: &str) -> Result<CompiledChoreography, CompileArtifactsError> {
    let choreography = parse_choreography_str(input)?;
    compile_choreography_ast(choreography)
}

/// Validate and project an already-parsed choreography.
pub fn compile_choreography_ast(
    choreography: Choreography,
) -> Result<CompiledChoreography, CompileArtifactsError> {
    choreography
        .validate()
        .map_err(|err| CompileArtifactsError::Validation(err.to_string()))?;

    let mut local_types = Vec::new();
    for role in &choreography.roles {
        let local_type =
            project(&choreography, role).map_err(|source| CompileArtifactsError::Projection {
                role: role.name().to_string(),
                source,
            })?;
        local_types.push((role.clone(), local_type));
    }

    Ok(CompiledChoreography {
        choreography,
        local_types,
    })
}

/// Collect every ordered annotation record from a choreography.
#[must_use]
pub fn collect_choreography_annotation_records(
    choreography: &Choreography,
) -> Vec<ProtocolAnnotationRecord> {
    collect_protocol_annotation_records(&choreography.protocol)
}

/// Collect every ordered annotation record from a protocol tree.
#[must_use]
pub fn collect_protocol_annotation_records(protocol: &Protocol) -> Vec<ProtocolAnnotationRecord> {
    let mut records = Vec::new();
    collect_protocol_annotation_records_inner(protocol, "root", &mut records);
    records
}

fn collect_protocol_annotation_records_inner(
    protocol: &Protocol,
    path: &str,
    records: &mut Vec<ProtocolAnnotationRecord>,
) {
    match protocol {
        Protocol::Send {
            from,
            to,
            continuation,
            ..
        } => {
            push_annotation_records(
                records,
                path,
                "send",
                AnnotationScope::Statement,
                Some(from),
                &[to.clone()],
                protocol.get_annotations().dsl_entries(),
            );
            if let Some(from_annotations) = protocol.get_from_annotations() {
                push_annotation_records(
                    records,
                    path,
                    "send",
                    AnnotationScope::Sender,
                    Some(from),
                    &[to.clone()],
                    from_annotations.dsl_entries(),
                );
            }
            if let Some(to_annotations) = protocol.get_to_annotations() {
                push_annotation_records(
                    records,
                    path,
                    "send",
                    AnnotationScope::Receiver,
                    Some(to),
                    &[from.clone()],
                    to_annotations.dsl_entries(),
                );
            }
            collect_protocol_annotation_records_inner(
                continuation,
                &format!("{path}.continuation"),
                records,
            );
        }
        Protocol::Broadcast {
            from,
            to_all,
            continuation,
            ..
        } => {
            let peers = to_all.iter().cloned().collect::<Vec<_>>();
            push_annotation_records(
                records,
                path,
                "broadcast",
                AnnotationScope::Statement,
                Some(from),
                &peers,
                protocol.get_annotations().dsl_entries(),
            );
            if let Some(from_annotations) = protocol.get_from_annotations() {
                push_annotation_records(
                    records,
                    path,
                    "broadcast",
                    AnnotationScope::Sender,
                    Some(from),
                    &peers,
                    from_annotations.dsl_entries(),
                );
            }
            collect_protocol_annotation_records_inner(
                continuation,
                &format!("{path}.continuation"),
                records,
            );
        }
        Protocol::Choice { role, branches, .. } => {
            push_annotation_records(
                records,
                path,
                "choice",
                AnnotationScope::Statement,
                Some(role),
                &[],
                protocol.get_annotations().dsl_entries(),
            );
            for branch in branches {
                collect_protocol_annotation_records_inner(
                    &branch.protocol,
                    &format!("{path}.branch[{}]", branch.label),
                    records,
                );
            }
        }
        Protocol::Loop { body, .. } => {
            collect_protocol_annotation_records_inner(body, &format!("{path}.body"), records);
        }
        Protocol::Parallel { protocols } => {
            for (idx, branch) in protocols.iter().enumerate() {
                collect_protocol_annotation_records_inner(
                    branch,
                    &format!("{path}.parallel[{idx}]"),
                    records,
                );
            }
        }
        Protocol::Rec { label, body } => {
            collect_protocol_annotation_records_inner(
                body,
                &format!("{path}.rec[{label}]"),
                records,
            );
        }
        Protocol::Timeout {
            body,
            on_timeout,
            on_cancel,
            ..
        } => {
            collect_protocol_annotation_records_inner(
                body,
                &format!("{path}.timeout.body"),
                records,
            );
            collect_protocol_annotation_records_inner(
                on_timeout,
                &format!("{path}.timeout.on_timeout"),
                records,
            );
            if let Some(on_cancel) = on_cancel {
                collect_protocol_annotation_records_inner(
                    on_cancel,
                    &format!("{path}.timeout.on_cancel"),
                    records,
                );
            }
        }
        Protocol::Case { branches, .. } => {
            for branch in branches {
                collect_protocol_annotation_records_inner(
                    &branch.protocol,
                    &format!("{path}.case[{}]", branch.pattern.constructor),
                    records,
                );
            }
        }
        Protocol::Extension { continuation, .. } => {
            push_annotation_records(
                records,
                path,
                "extension",
                AnnotationScope::Statement,
                None,
                &[],
                protocol.get_annotations().dsl_entries(),
            );
            collect_protocol_annotation_records_inner(
                continuation,
                &format!("{path}.continuation"),
                records,
            );
        }
        Protocol::Begin { continuation, .. }
        | Protocol::Await { continuation, .. }
        | Protocol::Resolve { continuation, .. }
        | Protocol::Invalidate { continuation, .. }
        | Protocol::Let { continuation, .. }
        | Protocol::Publish { continuation, .. }
        | Protocol::PublishAuthority { continuation, .. }
        | Protocol::Materialize { continuation, .. }
        | Protocol::Handoff { continuation, .. }
        | Protocol::DependentWork { continuation, .. } => {
            collect_protocol_annotation_records_inner(
                continuation,
                &format!("{path}.continuation"),
                records,
            );
        }
        Protocol::Var(_) | Protocol::End => {}
    }
}

fn push_annotation_records(
    records: &mut Vec<ProtocolAnnotationRecord>,
    path: &str,
    node_kind: &str,
    scope: AnnotationScope,
    role: Option<&Role>,
    peer_roles: &[Role],
    entries: Vec<DslAnnotationEntry>,
) {
    let role = role.map(|role| role.name().to_string());
    let peer_roles = peer_roles
        .iter()
        .map(|role| role.name().to_string())
        .collect::<Vec<_>>();

    for entry in entries {
        records.push(ProtocolAnnotationRecord {
            path: path.to_string(),
            node_kind: node_kind.to_string(),
            scope,
            role: role.clone(),
            peer_roles: peer_roles.clone(),
            key: entry.key,
            value: entry.value,
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ordered_annotation_records_preserve_sender_order() {
        let compiled = compile_choreography(
            r#"
protocol Demo =
  roles Alice, Bob
  Alice { guard_capability : "chat:send", flow_cost : 10, leak : external } -> Bob : Msg
"#,
        )
        .expect("compile choreography");

        let records = compiled
            .annotation_records()
            .into_iter()
            .filter(|record| {
                record.path == "root"
                    && record.scope == AnnotationScope::Sender
                    && record.role.as_deref() == Some("Alice")
            })
            .collect::<Vec<_>>();

        assert_eq!(
            records
                .iter()
                .map(|record| record.key.as_str())
                .collect::<Vec<_>>(),
            vec!["guard_capability", "flow_cost", "leak"]
        );
    }
}
