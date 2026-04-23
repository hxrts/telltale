#![allow(
    clippy::missing_errors_doc,
    clippy::missing_panics_doc,
    clippy::must_use_candidate
)]
#![cfg_attr(not(test), deny(clippy::unwrap_used, clippy::expect_used))]

//! Public language and compiler-facing APIs.
//!
//! These parser, lowering, projection, and code-generation entry points are
//! supported and covered by strict operational verification gates, but they are
//! intentionally outside the current formal-verification claim. The current
//! claim is scoped to the Lean models/theorems plus the theorem-defined Rust↔Lean
//! runtime correspondence surface, not to Rust compiler-pipeline correctness.

pub mod ast;
pub mod compiler;
pub mod effect_spec;
pub mod extensions;
pub mod integration;
mod module_codegen;

pub use ast::{
    AgreementProfileDeclaration, Choreography, Condition, DslAnnotationEntry,
    EffectInterfaceDeclaration, ExecutionProfileDeclaration, GuestRuntimeDeclaration, LanguageTier,
    LanguageTierStatus, LocalType, MessageType, OperationAgreementAttachment, OperationDeclaration,
    Protocol, RegionDeclaration, Role, RoleSetDeclaration, TheoremPackDeclaration,
    TopologyDeclaration, TypeDeclaration,
};
pub use compiler::codegen::{
    generate_choreography_code, generate_choreography_code_with_annotations,
    generate_choreography_code_with_dynamic_roles, generate_choreography_code_with_extensions,
    generate_choreography_code_with_namespacing, generate_helpers, generate_role_implementations,
    generate_session_type,
};
pub use compiler::parser::{
    choreography_macro, collect_dsl_lints, explain_lowering, parse_choreography,
    parse_choreography_file, parse_choreography_str, parse_choreography_str_with_extensions,
    parse_dsl, render_lsp_lint_diagnostics, ErrorSpan, LintDiagnostic, LintLevel, ParseError,
    DEFAULT_SOURCE_EXTENSION,
};
pub use compiler::projection::{project, ProjectionError};
pub use effect_spec::{
    generate_effect_interface_scaffold, generated_effect_families, GeneratedEffectBehavior,
    GeneratedEffectFamily, GeneratedEffectOperation, GeneratedSimulationMetadata,
    GeneratedSimulationMode,
};
pub use extensions::{
    CodegenContext, ExtensionRegistry, ExtensionValidationError, GrammarExtension, ParseContext,
    ParseError as ExtensionParseError, ProjectionContext, ProtocolExtension, StatementParser,
};
pub use integration::{
    collect_choreography_annotation_records, collect_protocol_annotation_records,
    compile_choreography, compile_choreography_ast, AnnotationScope, CompileArtifactsError,
    CompiledChoreography, ProtocolAnnotationRecord,
};
pub use module_codegen::generate_protocol_module;
