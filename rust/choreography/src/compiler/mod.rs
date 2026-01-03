//! Choreography compilation pipeline
//!
//! This module contains the compilation pipeline that transforms choreographic
//! specifications into executable code.

pub mod analysis;
pub mod choice_analysis;
pub mod codegen;
pub mod concurrency;
pub mod diagnostics;
pub mod effects_codegen;
pub mod extension_parser;
pub mod grammar;
pub mod layout;
pub mod merge;
pub mod parser;
pub mod pretty;
pub mod projection;
pub mod runner;
pub mod typed_runner;

// Re-export compiler pipeline components explicitly
pub use analysis::{
    analyze, generate_dot_graph, AnalysisResult, AnalysisWarning, CommunicationGraph,
    ParticipationInfo,
};
pub use choice_analysis::{
    analyze_choreography_choices, messages_are_distinguishing, ChoiceAnalysisResult,
    ChoiceAnalyzer, ChoiceId, ChoiceKnowledge, KnowledgeSource,
};
pub use codegen::{
    generate_choreography_code, generate_choreography_code_with_namespacing,
    generate_choreography_code_with_topology, generate_helpers, generate_role_implementations,
    generate_session_type, generate_topology_integration, InlineTopology,
};
pub use concurrency::{
    generate_batch_recv, generate_batch_send, generate_broadcast, generate_collection,
    generate_ordered_collection, generate_parallel_broadcast, generate_sequential_broadcast,
    generate_unordered_collection, BatchConfig, BroadcastMode, CollectionMode,
    ProtocolConcurrencyConfig, StatementConcurrencyConfig,
};
pub use diagnostics::{
    check_self_communication, validate_roles, Diagnostic, DiagnosticCode, DiagnosticCollector,
    Severity, SourceLocation,
};
pub use effects_codegen::generate_effects_protocol;
pub use extension_parser::{
    create_standard_extension_parser, ExtensionParseError, ExtensionParser, ExtensionParserBuilder,
    ExtensionStats,
};
pub use grammar::{GrammarComposer, GrammarComposerBuilder, GrammarCompositionError};
pub use merge::{can_merge, merge, merge_all, MergeError};
pub use parser::{
    choreography_macro, parse_choreography, parse_choreography_file, parse_choreography_str,
    parse_dsl, ErrorSpan, ParseError,
};
pub use pretty::{
    format_choreography, format_choreography_str, format_choreography_with_config, PrettyConfig,
};
pub use projection::{project, ProjectionError};
pub use runner::{generate_all_runners, generate_execute_as, generate_runner_fn};
pub use typed_runner::{
    extract_role_messages, generate_all_typed_runners, generate_typed_runner, MessageDirection,
    RoleMessageInfo, SerializationConfig, SerializationFormat,
};
