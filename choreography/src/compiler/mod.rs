//! Choreography compilation pipeline
//!
//! This module contains the compilation pipeline that transforms choreographic
//! specifications into executable code.

pub mod analysis;
pub mod codegen;
pub mod effects_codegen;
pub mod parser;
pub mod projection;

// Re-export compiler pipeline components explicitly
pub use analysis::{
    analyze, generate_dot_graph, AnalysisResult, AnalysisWarning, CommunicationGraph,
    ParticipationInfo,
};
pub use codegen::{
    generate_choreography_code, generate_choreography_code_with_namespacing, generate_helpers, generate_role_implementations,
    generate_session_type,
};
pub use effects_codegen::generate_effects_protocol;
pub use parser::{choreography_macro, parse_choreography, parse_choreography_file, parse_choreography_str, parse_dsl};
pub use projection::{project, ProjectionError};
