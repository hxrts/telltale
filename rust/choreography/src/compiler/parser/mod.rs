//! Parser for choreographic protocol syntax.
//!
//! This module provides a full implementation using Pest grammar for parsing
//! choreographic DSL specifications into the Protocol AST.
//!
//! # Module Structure
//!
//! - `error`: Error types and span information for diagnostics
//! - `types`: Internal AST types for parsing (Statement, ChoiceBranch, etc.)
//! - `role`: Role parsing (declarations, references, indices, ranges)
//! - `statement`: Statement parsing (send, choice, loop, etc.)
//! - `conversion`: Protocol conversion and call inlining

mod conversion;
mod declarations;
mod error;
mod linear;
mod lints;
mod role;
mod statement;
mod stmt_parsers;
#[cfg(test)]
mod tests {
    use super::*;

    mod core_syntax_and_decide_loops {
        include!("../../../tests/unit/compiler/parser/core_syntax_and_decide_loops.rs");
    }

    mod annotations_and_parallel {
        include!("../../../tests/unit/compiler/parser/annotations_and_parallel.rs");
    }

    mod proof_bundles_and_predicates {
        include!("../../../tests/unit/compiler/parser/proof_bundles_and_predicates.rs");
    }
}
mod types;

// Re-export public API
pub use error::{ErrorSpan, ParseError};
pub use lints::{
    collect_dsl_lints, explain_lowering, render_lsp_lint_diagnostics, LintDiagnostic, LintLevel,
};

use crate::ast::{Choreography, ProofBundleDecl, RoleSetDecl, TopologyDecl};
use crate::compiler::layout::preprocess_layout;
use crate::extensions::{ExtensionRegistry, ProtocolExtension};
use pest::Parser;
use pest_derive::Parser;
use proc_macro2::{Span, TokenStream};
use quote::format_ident;
use std::collections::{HashMap, HashSet};

use conversion::{convert_statements_to_protocol, inline_calls};
use declarations::{
    parse_module_decl, parse_proof_bundle_decl, parse_protocol_requires, parse_role_set_decl,
    parse_topology_decl,
};
use linear::{infer_required_proof_bundles, validate_linear_vm_assets};
use role::parse_roles_from_pair;
use statement::{parse_local_protocol_decl, parse_protocol_body};
use types::Statement;

#[derive(Parser)]
#[grammar = "compiler/choreography.pest"]
struct ChoreographyParser;

/// Parse a choreographic protocol from a string
pub fn parse_choreography_str(input: &str) -> std::result::Result<Choreography, ParseError> {
    parse_choreography_str_with_extensions(input, &ExtensionRegistry::new())
        .map(|(choreo, _)| choreo)
}

/// Parse a choreographic protocol from a string with extension support
#[allow(clippy::too_many_lines)]
pub fn parse_choreography_str_with_extensions(
    input: &str,
    registry: &ExtensionRegistry,
) -> std::result::Result<(Choreography, Vec<Box<dyn ProtocolExtension>>), ParseError> {
    let dedented = strip_common_indent(input);
    let layout = preprocess_layout(&dedented).map_err(|e| ParseError::Layout {
        span: ErrorSpan::from_line_col(e.line, e.column, &dedented),
        message: e.message,
    })?;

    let preprocessed = preprocess_extension_syntax(&layout, registry)?;

    let pairs = ChoreographyParser::parse(Rule::choreography, &preprocessed).map_err(Box::new)?;

    let mut name = format_ident!("Unnamed");
    let mut namespace: Option<String> = None;
    let mut roles: Vec<crate::ast::Role> = Vec::new();
    let mut declared_roles: HashSet<String> = HashSet::new();
    let mut protocol_defs: HashMap<String, Vec<Statement>> = HashMap::new();
    let mut statements: Vec<Statement> = Vec::new();
    let mut proof_bundles: Vec<ProofBundleDecl> = Vec::new();
    let mut required_bundles: Vec<String> = Vec::new();
    let mut role_sets: Vec<RoleSetDecl> = Vec::new();
    let mut topologies: Vec<TopologyDecl> = Vec::new();

    for pair in pairs {
        if pair.as_rule() == Rule::choreography {
            for inner in pair.into_inner() {
                match inner.as_rule() {
                    Rule::module_decl => {
                        namespace = Some(parse_module_decl(inner, &preprocessed)?);
                    }
                    Rule::import_decl => {
                        // Imports are parsed but not processed (reserved syntax)
                    }
                    Rule::proof_bundle_decl => {
                        proof_bundles.push(parse_proof_bundle_decl(inner, &preprocessed)?);
                    }
                    Rule::role_set_decl => {
                        role_sets.push(parse_role_set_decl(inner, &preprocessed)?);
                    }
                    Rule::topology_decl => {
                        topologies.push(parse_topology_decl(inner, &preprocessed)?);
                    }
                    Rule::protocol_decl => {
                        let protocol_span = inner.as_span();
                        let mut proto_inner = inner.into_inner();
                        let name_pair = proto_inner.next().ok_or_else(|| ParseError::Syntax {
                            span: ErrorSpan::from_pest_span(protocol_span, &preprocessed),
                            message: "protocol declaration is missing a name".to_string(),
                        })?;
                        name = format_ident!("{}", name_pair.as_str());

                        let mut header_roles: Option<Vec<crate::ast::Role>> = None;
                        let mut body_pair: Option<pest::iterators::Pair<Rule>> = None;
                        let mut where_pair: Option<pest::iterators::Pair<Rule>> = None;

                        for item in proto_inner {
                            match item.as_rule() {
                                Rule::header_roles => {
                                    header_roles =
                                        Some(parse_roles_from_pair(item, &preprocessed)?);
                                }
                                Rule::protocol_requires => {
                                    required_bundles = parse_protocol_requires(item);
                                }
                                Rule::protocol_body => {
                                    body_pair = Some(item);
                                }
                                Rule::where_block => {
                                    where_pair = Some(item);
                                }
                                _ => {}
                            }
                        }

                        let allow_roles_decl = header_roles.is_none();
                        let body_pair = body_pair.ok_or_else(|| ParseError::Syntax {
                            span: ErrorSpan::from_pest_span(protocol_span, &preprocessed),
                            message: "protocol declaration is missing a body".to_string(),
                        })?;
                        let body_span = body_pair.as_span();
                        let types::ParsedBody {
                            roles: body_roles,
                            statements: body_statements,
                        } = parse_protocol_body(
                            body_pair,
                            &declared_roles,
                            &preprocessed,
                            &protocol_defs,
                            allow_roles_decl,
                        )?;

                        if header_roles.is_some() && body_roles.is_some() {
                            return Err(ParseError::Syntax {
                                span: ErrorSpan::from_pest_span(body_span, &preprocessed),
                                message: "roles cannot be declared both in the header and body"
                                    .to_string(),
                            });
                        }

                        if let Some(r) = header_roles {
                            roles = r;
                            declared_roles = roles.iter().map(|r| r.name().to_string()).collect();
                        } else if let Some(r) = body_roles {
                            roles = r;
                            declared_roles = roles.iter().map(|r| r.name().to_string()).collect();
                        }

                        if let Some(where_block) = where_pair {
                            for local in where_block.into_inner().flat_map(|p| p.into_inner()) {
                                if local.as_rule() == Rule::local_protocol_decl {
                                    parse_local_protocol_decl(
                                        local,
                                        &declared_roles,
                                        &preprocessed,
                                        &mut protocol_defs,
                                    )?;
                                }
                            }
                        }

                        statements = inline_calls(&body_statements, &protocol_defs, &preprocessed)?;
                        validate_linear_vm_assets(&statements, &preprocessed)?;
                    }
                    _ => {}
                }
            }
        }
    }

    if roles.is_empty() {
        return Err(ParseError::EmptyChoreography);
    }

    let protocol = convert_statements_to_protocol(&statements, &roles);

    let mut choreography = Choreography {
        name,
        namespace,
        roles,
        protocol,
        attrs: HashMap::new(),
    };

    choreography
        .set_proof_bundles(&proof_bundles)
        .map_err(|message| ParseError::Syntax {
            span: ErrorSpan::from_line_col(1, 1, &preprocessed),
            message,
        })?;
    let inferred_required_bundles =
        infer_required_proof_bundles(&required_bundles, &proof_bundles, &statements);
    let resolved_required_bundles = if required_bundles.is_empty() {
        inferred_required_bundles.clone()
    } else {
        required_bundles.clone()
    };

    choreography
        .set_required_proof_bundles(&resolved_required_bundles)
        .map_err(|message| ParseError::Syntax {
            span: ErrorSpan::from_line_col(1, 1, &preprocessed),
            message,
        })?;
    choreography
        .set_inferred_required_proof_bundles(&inferred_required_bundles)
        .map_err(|message| ParseError::Syntax {
            span: ErrorSpan::from_line_col(1, 1, &preprocessed),
            message,
        })?;
    choreography
        .set_role_sets(&role_sets)
        .map_err(|message| ParseError::Syntax {
            span: ErrorSpan::from_line_col(1, 1, &preprocessed),
            message,
        })?;
    choreography
        .set_topologies(&topologies)
        .map_err(|message| ParseError::Syntax {
            span: ErrorSpan::from_line_col(1, 1, &preprocessed),
            message,
        })?;

    Ok((choreography, Vec::new()))
}

/// Preprocess extension syntax to transform it into standard DSL syntax.
///
/// Returns input unchanged - extension surface syntax is not used in the
/// current DSL. This function maintains API stability.
fn preprocess_extension_syntax(
    input: &str,
    _registry: &ExtensionRegistry,
) -> std::result::Result<String, ParseError> {
    Ok(input.to_string())
}

fn strip_common_indent(input: &str) -> String {
    let lines: Vec<&str> = input.lines().collect();
    let mut min_indent: Option<usize> = None;

    for line in &lines {
        if line.trim().is_empty() {
            continue;
        }
        let indent = line.chars().take_while(|c| *c == ' ').count();
        min_indent = Some(match min_indent {
            Some(current) => current.min(indent),
            None => indent,
        });
    }

    let min_indent = min_indent.unwrap_or(0);
    if min_indent == 0 {
        return input.to_string();
    }

    let mut out = String::new();
    for (idx, line) in lines.iter().enumerate() {
        let stripped = line.get(min_indent..).unwrap_or(line);
        out.push_str(stripped);
        if idx + 1 < lines.len() {
            out.push('\n');
        }
    }

    if input.ends_with('\n') {
        out.push('\n');
    }

    out
}

/// Parse a choreographic protocol from a token stream (for macro use)
/// This is a compatibility function that wraps the string parser
pub fn parse_choreography(input: TokenStream) -> syn::Result<Choreography> {
    use syn::LitStr;

    // Try to parse as a string literal (for DSL syntax)
    if let Ok(lit_str) = syn::parse2::<LitStr>(input.clone()) {
        // Parse the DSL string
        let dsl_content = lit_str.value();
        return parse_choreography_str(&dsl_content).map_err(|e| {
            syn::Error::new(lit_str.span(), format!("Choreography parse error: {e}"))
        });
    }

    let normalized = normalize_macro_token_input(&input);
    parse_choreography_str(&normalized).map_err(|e| {
        syn::Error::new(
            proc_macro2::Span::call_site(),
            format!(
                "Choreography parse error: {e}\n\
                 Macro token input is parsed as DSL text after normalization.\n\
                 You can use either string-literal DSL or token-stream DSL forms."
            ),
        )
    })
}

fn normalize_macro_token_input(input: &TokenStream) -> String {
    fn strip_outer_delimiters(s: &str) -> &str {
        let trimmed = s.trim();
        if trimmed.len() < 2 {
            return trimmed;
        }
        let first = trimmed.chars().next().unwrap_or_default();
        let last = trimmed.chars().last().unwrap_or_default();
        let is_pair = (first == '{' && last == '}') || (first == '(' && last == ')');
        if is_pair {
            &trimmed[1..trimmed.len() - 1]
        } else {
            trimmed
        }
    }

    fn normalize_composite_ops(mut s: String) -> String {
        let patterns = [
            ("-> *", "->*"),
            ("->  *", "->*"),
            ("<- >", "<->"),
            ("< - >", "<->"),
            ("<  - >", "<->"),
            ("< -  >", "<->"),
        ];

        loop {
            // bounded: converges as patterns reduce spacing
            let mut changed = false;
            for (from, to) in patterns {
                if s.contains(from) {
                    s = s.replace(from, to);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        s
    }

    let raw = input.to_string();
    let stripped = strip_outer_delimiters(&raw);
    let mut normalized = normalize_composite_ops(stripped.to_string());
    normalized = normalized.replace(';', "\n");
    normalized
}

/// Parse a choreography from a file
pub fn parse_choreography_file(
    path: &std::path::Path,
) -> std::result::Result<Choreography, ParseError> {
    let content = std::fs::read_to_string(path).map_err(|e| ParseError::Syntax {
        span: ErrorSpan {
            line: 1,
            column: 1,
            line_end: 1,
            column_end: 1,
            snippet: format!("Failed to read file: {}", path.display()),
        },
        message: e.to_string(),
    })?;

    parse_choreography_str(&content)
}

/// Parse choreography DSL
pub fn parse_dsl(input: &str) -> std::result::Result<Choreography, ParseError> {
    parse_choreography_str(input)
}

/// Example of how the macro entry point works.
#[must_use]
pub fn choreography_macro(input: TokenStream) -> TokenStream {
    let choreography = match parse_choreography(input) {
        Ok(c) => c,
        Err(e) => return e.to_compile_error(),
    };

    // Validate the choreography
    if let Err(e) = choreography.validate() {
        return syn::Error::new(Span::call_site(), e.to_string()).to_compile_error();
    }

    // Project to local types
    let mut local_types = Vec::new();
    for role in &choreography.roles {
        match super::projection::project(&choreography, role) {
            Ok(local_type) => local_types.push((role.clone(), local_type)),
            Err(e) => return syn::Error::new(Span::call_site(), e.to_string()).to_compile_error(),
        }
    }

    // Generate code with namespace support
    super::codegen::generate_choreography_code_with_namespacing(&choreography, &local_types)
}
