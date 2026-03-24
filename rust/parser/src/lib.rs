#![allow(
    clippy::missing_errors_doc,
    clippy::missing_panics_doc,
    clippy::must_use_candidate
)]

pub mod ast;
pub mod compiler;
pub mod effect_spec;
pub mod extensions;

pub use ast::{
    Choreography, Condition, EffectDecl, FragmentDecl, GuestRuntimeDecl, LocalType, MessageType,
    OperationDecl, ProofBundleDecl, Protocol, Role, RoleSetDecl, TopologyDecl, TypeDecl,
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
