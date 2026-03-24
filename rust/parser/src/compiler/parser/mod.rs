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
mod types;

// Re-export public API
pub use error::{ErrorSpan, ParseError};
pub use lints::{
    collect_dsl_lints, explain_lowering, render_lsp_lint_diagnostics, LintDiagnostic, LintLevel,
};

use crate::ast::{
    Choreography, EffectDecl, FragmentDecl, GuestRuntimeDecl, OperationDecl, ProofBundleDecl,
    RoleSetDecl, TopologyDecl, TypeDecl,
};
use crate::compiler::layout::preprocess_layout;
use crate::extensions::{ExtensionRegistry, ProtocolExtension};
use pest::Parser;
use pest_derive::Parser;
use proc_macro2::{Span, TokenStream};
use quote::format_ident;
use std::collections::{HashMap, HashSet};

use conversion::{convert_statements_to_protocol, inline_calls};
use declarations::{
    enforce_same_line_equals, parse_effect_decl, parse_fragment_decl, parse_guest_runtime_decl,
    parse_module_decl, parse_operation_decl, parse_proof_bundle_decl, parse_protocol_requires,
    parse_protocol_uses, parse_role_set_decl, parse_topology_decl, parse_type_decl,
};
use linear::{infer_required_proof_bundles, validate_authority_surface, validate_linear_vm_assets};
use role::parse_roles_from_pair;
use statement::{parse_local_protocol_decl, parse_protocol_body};
use types::Statement;

#[derive(Parser)]
#[grammar = "compiler/choreography.pest"]
struct ChoreographyParser;

/// Canonical source-file extension for Telltale choreography files.
pub const DEFAULT_SOURCE_EXTENSION: &str = "tell";

/// Parse a choreographic protocol from a string
pub fn parse_choreography_str(input: &str) -> std::result::Result<Choreography, ParseError> {
    parse_choreography_str_with_extensions(input, &ExtensionRegistry::new())
        .map(|(choreo, _)| choreo)
}

/// Parse a choreographic protocol from a string with extension support
#[allow(clippy::too_many_lines)]
pub fn parse_choreography_str_with_extensions(
    input: &str,
    _registry: &ExtensionRegistry,
) -> std::result::Result<(Choreography, Vec<Box<dyn ProtocolExtension>>), ParseError> {
    let dedented = strip_common_indent(input);
    let layout = preprocess_layout(&dedented).map_err(|e| ParseError::Layout {
        span: ErrorSpan::from_line_col(e.line, e.column, &dedented),
        message: e.message,
    })?;
    let pairs = ChoreographyParser::parse(Rule::choreography, &layout).map_err(Box::new)?;

    let mut name = format_ident!("Unnamed");
    let mut namespace: Option<String> = None;
    let mut roles: Vec<crate::ast::Role> = Vec::new();
    let mut declared_roles: HashSet<String> = HashSet::new();
    let mut protocol_defs: HashMap<String, Vec<Statement>> = HashMap::new();
    let mut statements: Vec<Statement> = Vec::new();
    let mut proof_bundles: Vec<ProofBundleDecl> = Vec::new();
    let mut required_bundles: Vec<String> = Vec::new();
    let mut protocol_uses: Vec<String> = Vec::new();
    let mut role_sets: Vec<RoleSetDecl> = Vec::new();
    let mut topologies: Vec<TopologyDecl> = Vec::new();
    let mut type_decls: Vec<TypeDecl> = Vec::new();
    let mut effect_decls: Vec<EffectDecl> = Vec::new();
    let mut fragment_decls: Vec<FragmentDecl> = Vec::new();
    let mut operation_decls: Vec<OperationDecl> = Vec::new();
    let mut guest_runtime_decls: Vec<GuestRuntimeDecl> = Vec::new();

    for pair in pairs {
        if pair.as_rule() == Rule::choreography {
            for inner in pair.into_inner() {
                match inner.as_rule() {
                    Rule::module_decl => {
                        namespace = Some(parse_module_decl(inner, &layout)?);
                    }
                    Rule::import_decl => {
                        // Imports are parsed but not processed (reserved syntax)
                    }
                    Rule::proof_bundle_decl => {
                        proof_bundles.push(parse_proof_bundle_decl(inner, &layout)?);
                    }
                    Rule::role_set_decl => {
                        role_sets.push(parse_role_set_decl(inner, &layout)?);
                    }
                    Rule::topology_decl => {
                        topologies.push(parse_topology_decl(inner, &layout)?);
                    }
                    Rule::type_decl => {
                        type_decls.push(parse_type_decl(inner, &layout)?);
                    }
                    Rule::effect_decl => {
                        effect_decls.push(parse_effect_decl(inner, &layout)?);
                    }
                    Rule::fragment_decl => {
                        fragment_decls.push(parse_fragment_decl(inner, &layout)?);
                    }
                    Rule::operation_decl => {
                        operation_decls.push(parse_operation_decl(inner, &layout)?);
                    }
                    Rule::guest_runtime_decl => {
                        guest_runtime_decls.push(parse_guest_runtime_decl(inner, &layout)?);
                    }
                    Rule::protocol_decl => {
                        let protocol_span = inner.as_span();
                        enforce_same_line_equals(
                            inner.as_str(),
                            protocol_span,
                            &layout,
                            "protocol declaration",
                        )?;
                        let mut proto_inner = inner.into_inner();
                        let name_pair = proto_inner.next().ok_or_else(|| ParseError::Syntax {
                            span: ErrorSpan::from_pest_span(protocol_span, &layout),
                            message: "protocol declaration is missing a name".to_string(),
                        })?;
                        name = format_ident!("{}", name_pair.as_str());

                        let mut header_roles: Option<Vec<crate::ast::Role>> = None;
                        let mut body_pair: Option<pest::iterators::Pair<Rule>> = None;
                        let mut where_pair: Option<pest::iterators::Pair<Rule>> = None;

                        for item in proto_inner {
                            match item.as_rule() {
                                Rule::header_roles => {
                                    header_roles = Some(parse_roles_from_pair(item, &layout)?);
                                }
                                Rule::protocol_requires => {
                                    required_bundles = parse_protocol_requires(item);
                                }
                                Rule::protocol_uses => {
                                    protocol_uses = parse_protocol_uses(item);
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
                            span: ErrorSpan::from_pest_span(protocol_span, &layout),
                            message: "protocol declaration is missing a body".to_string(),
                        })?;
                        let body_span = body_pair.as_span();
                        let types::ParsedBody {
                            roles: body_roles,
                            statements: body_statements,
                        } = parse_protocol_body(
                            body_pair,
                            &declared_roles,
                            &layout,
                            &protocol_defs,
                            allow_roles_decl,
                        )?;

                        if header_roles.is_some() && body_roles.is_some() {
                            return Err(ParseError::Syntax {
                                span: ErrorSpan::from_pest_span(body_span, &layout),
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
                                        &layout,
                                        &mut protocol_defs,
                                    )?;
                                }
                            }
                        }

                        statements = inline_calls(&body_statements, &protocol_defs, &layout)?;
                        validate_linear_vm_assets(&statements, &layout)?;
                        validate_authority_surface(&statements, &layout)?;
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
            span: ErrorSpan::from_line_col(1, 1, &layout),
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
            span: ErrorSpan::from_line_col(1, 1, &layout),
            message,
        })?;
    choreography
        .set_inferred_required_proof_bundles(&inferred_required_bundles)
        .map_err(|message| ParseError::Syntax {
            span: ErrorSpan::from_line_col(1, 1, &layout),
            message,
        })?;
    choreography
        .set_role_sets(&role_sets)
        .map_err(|message| ParseError::Syntax {
            span: ErrorSpan::from_line_col(1, 1, &layout),
            message,
        })?;
    choreography
        .set_topologies(&topologies)
        .map_err(|message| ParseError::Syntax {
            span: ErrorSpan::from_line_col(1, 1, &layout),
            message,
        })?;
    choreography
        .set_type_decls(&type_decls)
        .map_err(|message| ParseError::Syntax {
            span: ErrorSpan::from_line_col(1, 1, &layout),
            message,
        })?;
    choreography
        .set_effect_decls(&effect_decls)
        .map_err(|message| ParseError::Syntax {
            span: ErrorSpan::from_line_col(1, 1, &layout),
            message,
        })?;
    choreography
        .set_protocol_uses(&protocol_uses)
        .map_err(|message| ParseError::Syntax {
            span: ErrorSpan::from_line_col(1, 1, &layout),
            message,
        })?;
    choreography
        .set_fragment_decls(&fragment_decls)
        .map_err(|message| ParseError::Syntax {
            span: ErrorSpan::from_line_col(1, 1, &layout),
            message,
        })?;
    choreography
        .set_operation_decls(&operation_decls)
        .map_err(|message| ParseError::Syntax {
            span: ErrorSpan::from_line_col(1, 1, &layout),
            message,
        })?;
    choreography
        .set_guest_runtime_decls(&guest_runtime_decls)
        .map_err(|message| ParseError::Syntax {
            span: ErrorSpan::from_line_col(1, 1, &layout),
            message,
        })?;

    Ok((choreography, Vec::new()))
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

/// Parse a choreographic protocol from a token stream for macro use.
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

    fn rewrite_legacy_block_heads(input: &str) -> String {
        fn is_ident_char(ch: char) -> bool {
            ch.is_ascii_alphanumeric() || ch == '_'
        }

        fn skip_ws(chars: &[char], mut idx: usize) -> usize {
            while idx < chars.len() && chars[idx].is_whitespace() {
                idx += 1;
            }
            idx
        }

        fn match_keyword(chars: &[char], idx: usize, keyword: &str) -> bool {
            let kw: Vec<char> = keyword.chars().collect();
            if idx + kw.len() > chars.len() {
                return false;
            }
            if idx > 0 && is_ident_char(chars[idx - 1]) {
                return false;
            }
            for (offset, expected) in kw.iter().enumerate() {
                if chars[idx + offset] != *expected {
                    return false;
                }
            }
            let end = idx + kw.len();
            end >= chars.len() || !is_ident_char(chars[end])
        }

        let chars: Vec<char> = input.chars().collect();
        let mut out = String::with_capacity(input.len() + 8);
        let mut idx = 0usize;

        while idx < chars.len() {
            if match_keyword(&chars, idx, "protocol") {
                let start = idx;
                idx += "protocol".len();
                while idx < chars.len() {
                    let ch = chars[idx];
                    if ch == '{' || ch == '=' {
                        break;
                    }
                    idx += 1;
                }
                out.push_str(&input[start..idx]);
                if idx < chars.len() && chars[idx] == '{' {
                    out.push_str(" = ");
                    out.push('{');
                    idx += 1;
                } else if idx < chars.len() && chars[idx] == '=' {
                    out.push('=');
                    idx += 1;
                }
                continue;
            }

            if match_keyword(&chars, idx, "choice") {
                let start = idx;
                idx += "choice".len();
                let role_start = skip_ws(&chars, idx);
                idx = role_start;
                while idx < chars.len() {
                    let ch = chars[idx];
                    if ch == '{' || ch.is_whitespace() {
                        break;
                    }
                    idx += 1;
                }
                let after_role = skip_ws(&chars, idx);

                if after_role < chars.len() && match_keyword(&chars, after_role, "at") {
                    out.push_str(&input[start..after_role + "at".len()]);
                    idx = after_role + "at".len();
                    continue;
                }

                out.push_str(&input[start..idx]);
                if after_role < chars.len() && chars[after_role] == '{' {
                    out.push_str(" at ");
                    out.push('{');
                    idx = after_role + 1;
                    continue;
                }
            }

            out.push(chars[idx]);
            idx += 1;
        }

        out
    }

    let raw = input.to_string();
    let stripped = strip_outer_delimiters(&raw);
    let mut normalized = normalize_composite_ops(stripped.to_string());
    normalized = rewrite_legacy_block_heads(&normalized);
    normalized = normalized.replace(';', "\n");
    normalized
}

/// Parse a choreography from a file
pub fn parse_choreography_file(
    path: &std::path::Path,
) -> std::result::Result<Choreography, ParseError> {
    if path.extension().and_then(std::ffi::OsStr::to_str) != Some(DEFAULT_SOURCE_EXTENSION) {
        return Err(ParseError::Syntax {
            span: ErrorSpan {
                line: 1,
                column: 1,
                line_end: 1,
                column_end: 1,
                snippet: format!("Unsupported source file extension: {}", path.display()),
            },
            message: format!(
                "Telltale source files must use the .{DEFAULT_SOURCE_EXTENSION} extension"
            ),
        });
    }

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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Condition, LocalType, Protocol, ValidationError};
    use crate::compiler::parser::parse_choreography_str;
    use crate::compiler::projection::project;
    use proc_macro2::TokenStream;
    use tempfile::tempdir;

    // ── core_syntax_loops ────────────────────────────────────────────

    #[test]
    fn test_parse_simple_send() {
        let input = r#"
protocol SimpleSend =
  roles Alice, Bob
  Alice -> Bob : Hello
"#;

        let result = parse_choreography_str(input);
        assert!(result.is_ok(), "Failed to parse: {:?}", result.err());

        let choreo = result.unwrap();
        assert_eq!(choreo.name.to_string(), "SimpleSend");
        assert_eq!(choreo.roles.len(), 2);
    }

    #[test]
    fn test_parse_with_choice() {
        let input = r#"
protocol Negotiation =
  roles Buyer, Seller
  Buyer -> Seller : Offer
  choice Seller at
    | accept =>
      Seller -> Buyer : Accept
    | reject =>
      Seller -> Buyer : Reject
"#;

        let result = parse_choreography_str(input);
        assert!(result.is_ok(), "Failed to parse: {:?}", result.err());

        let choreo = result.unwrap();
        assert_eq!(choreo.name.to_string(), "Negotiation");
    }

    #[test]
    fn test_parse_choice_alias() {
        let input = r#"
protocol AliasChoice =
  roles A, B
  choice A at
    | ok =>
      A -> B : Ack
    | fail =>
      A -> B : Nack
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse alias choice: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_parse_undefined_role() {
        let input = r#"
protocol Invalid =
  roles Alice
  Alice -> Bob : Hello
"#;

        let result = parse_choreography_str(input);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(matches!(err, ParseError::UndefinedRole { .. }));

        // Verify error message includes span information
        let err_str = err.to_string();
        assert!(err_str.contains("Undefined role"));
        assert!(err_str.contains("Bob"));
    }

    #[test]
    fn test_parse_duplicate_role() {
        let input = r#"
protocol DuplicateRole =
  roles Alice, Bob, Alice
  Alice -> Bob : Hello
"#;

        let result = parse_choreography_str(input);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(matches!(err, ParseError::DuplicateRole { .. }));

        // Verify error message includes span information
        let err_str = err.to_string();
        assert!(err_str.contains("Duplicate role"));
        assert!(err_str.contains("Alice"));
    }

    #[test]
    fn test_parse_loop_repeat() {
        let input = r#"
protocol LoopProtocol =
  roles Client, Server
  loop repeat 3
    Client -> Server : Request
    Server -> Client : Response
"#;

        let result = parse_choreography_str(input);
        assert!(result.is_ok(), "Failed to parse: {:?}", result.err());
    }

    #[test]
    fn test_parse_loop_decide() {
        let input = r#"
protocol DecideLoop =
  roles Client, Server
  loop decide by Client
    Client -> Server : Ping
    Server -> Client : Pong
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse decide loop: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_role_decides_desugaring() {
        // RoleDecides loops should be desugared to choice+rec pattern (Option B: fused)
        // loop decide by Client { Client -> Server: Ping; ... }
        // becomes:
        //   rec RoleDecidesLoop {
        //       choice Client at {
        //           Ping { Client -> Server: Ping; ...; continue }
        //           Done { Client -> Server: Done }
        //       }
        //   }
        let input = r#"
protocol DecideLoop =
  roles Client, Server
  loop decide by Client
    Client -> Server : Ping
    Server -> Client : Pong
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse decide loop: {:?}",
            result.err()
        );

        let choreo = result.unwrap();
        match &choreo.protocol {
            Protocol::Rec { label, body } => {
                assert_eq!(label.to_string(), "RoleDecidesLoop");
                match body.as_ref() {
                    Protocol::Choice { role, branches, .. } => {
                        assert_eq!(role.name().to_string(), "Client");
                        assert_eq!(branches.len(), 2);

                        // First branch should be the continue branch (using first message label)
                        let continue_branch = branches.first();
                        assert_eq!(continue_branch.label.to_string(), "Ping");

                        // Inside the continue branch, we should have the Send
                        match &continue_branch.protocol {
                            Protocol::Send {
                                from,
                                to,
                                message,
                                continuation,
                                ..
                            } => {
                                assert_eq!(from.name().to_string(), "Client");
                                assert_eq!(to.name().to_string(), "Server");
                                assert_eq!(message.name.to_string(), "Ping");

                                // Continuation should be the response followed by Var (continue)
                                match continuation.as_ref() {
                                    Protocol::Send {
                                        from,
                                        to,
                                        message,
                                        continuation,
                                        ..
                                    } => {
                                        assert_eq!(from.name().to_string(), "Server");
                                        assert_eq!(to.name().to_string(), "Client");
                                        assert_eq!(message.name.to_string(), "Pong");

                                        // Should end with Var (continue RoleDecidesLoop)
                                        match continuation.as_ref() {
                                            Protocol::Var(label) => {
                                                assert_eq!(label.to_string(), "RoleDecidesLoop");
                                            }
                                            _ => panic!(
                                                "Expected Var for continue, got {:?}",
                                                continuation
                                            ),
                                        }
                                    }
                                    _ => panic!("Expected Send for Pong, got {:?}", continuation),
                                }
                            }
                            _ => {
                                panic!("Expected Send for Ping, got {:?}", continue_branch.protocol)
                            }
                        }

                        // Second branch should be Done
                        let done_branch = &branches.as_slice()[1];
                        assert_eq!(done_branch.label.to_string(), "Done");
                        match &done_branch.protocol {
                            Protocol::Send {
                                from,
                                to,
                                message,
                                continuation,
                                ..
                            } => {
                                assert_eq!(from.name().to_string(), "Client");
                                assert_eq!(to.name().to_string(), "Server");
                                assert_eq!(message.name.to_string(), "Done");
                                assert!(matches!(continuation.as_ref(), Protocol::End));
                            }
                            _ => panic!("Expected Send for Done, got {:?}", done_branch.protocol),
                        }
                    }
                    _ => panic!("Expected Choice inside Rec, got {:?}", body),
                }
            }
            _ => panic!("Expected Rec at top level, got {:?}", choreo.protocol),
        }
    }

    #[test]
    fn test_role_decides_wrong_first_sender_no_desugar() {
        // When the first statement is a Send but NOT from the deciding role,
        // the loop should NOT be desugared and should remain as Protocol::Loop
        let input = r#"
protocol WrongSender =
  roles Client, Server
  loop decide by Client
    Server -> Client : Response
    Client -> Server : Ack
"#;

        let result = parse_choreography_str(input);
        assert!(result.is_ok(), "Failed to parse: {:?}", result.err());

        let choreo = result.unwrap();
        // Should remain as Loop, not desugared to Rec
        match &choreo.protocol {
            Protocol::Loop { condition, .. } => match condition {
                Some(Condition::RoleDecides(role)) => {
                    assert_eq!(role.name().to_string(), "Client");
                }
                _ => panic!("Expected RoleDecides condition"),
            },
            _ => panic!(
                "Expected Loop (not desugared) when first sender doesn't match deciding role"
            ),
        }
    }

    #[test]
    fn test_role_decides_single_message() {
        // Minimal case: loop with just one message
        let input = r#"
protocol SingleMessage =
  roles A, B
  loop decide by A
    A -> B : Msg
"#;

        let result = parse_choreography_str(input);
        assert!(result.is_ok(), "Failed to parse: {:?}", result.err());

        let choreo = result.unwrap();
        match &choreo.protocol {
            Protocol::Rec { label, body } => {
                assert_eq!(label.to_string(), "RoleDecidesLoop");
                match body.as_ref() {
                    Protocol::Choice { role, branches, .. } => {
                        assert_eq!(role.name().to_string(), "A");
                        assert_eq!(branches.len(), 2);

                        // Continue branch
                        let continue_branch = branches.first();
                        assert_eq!(continue_branch.label.to_string(), "Msg");
                        match &continue_branch.protocol {
                            Protocol::Send {
                                message,
                                continuation,
                                ..
                            } => {
                                assert_eq!(message.name.to_string(), "Msg");
                                // Should directly continue (no more statements)
                                assert!(matches!(continuation.as_ref(), Protocol::Var(_)));
                            }
                            _ => panic!("Expected Send"),
                        }

                        // Done branch
                        let done_branch = &branches.as_slice()[1];
                        assert_eq!(done_branch.label.to_string(), "Done");
                    }
                    _ => panic!("Expected Choice"),
                }
            }
            _ => panic!("Expected Rec"),
        }
    }

    #[test]
    fn test_role_decides_three_roles() {
        // Test with three roles where deciding role sends to one, then another responds
        let input = r#"
protocol ThreeRoles =
  roles Client, Server, Logger
  loop decide by Client
    Client -> Server : Request
    Server -> Logger : Log
    Logger -> Client : Ack
"#;

        let result = parse_choreography_str(input);
        assert!(result.is_ok(), "Failed to parse: {:?}", result.err());

        let choreo = result.unwrap();
        match &choreo.protocol {
            Protocol::Rec { body, .. } => {
                match body.as_ref() {
                    Protocol::Choice { role, branches, .. } => {
                        assert_eq!(role.name().to_string(), "Client");

                        let continue_branch = branches.first();
                        assert_eq!(continue_branch.label.to_string(), "Request");

                        // Verify the chain: Request -> Log -> Ack -> continue
                        match &continue_branch.protocol {
                            Protocol::Send {
                                from,
                                to,
                                message,
                                continuation,
                                ..
                            } => {
                                assert_eq!(from.name().to_string(), "Client");
                                assert_eq!(to.name().to_string(), "Server");
                                assert_eq!(message.name.to_string(), "Request");

                                match continuation.as_ref() {
                                    Protocol::Send {
                                        from,
                                        to,
                                        message,
                                        continuation,
                                        ..
                                    } => {
                                        assert_eq!(from.name().to_string(), "Server");
                                        assert_eq!(to.name().to_string(), "Logger");
                                        assert_eq!(message.name.to_string(), "Log");

                                        match continuation.as_ref() {
                                            Protocol::Send {
                                                from,
                                                to,
                                                message,
                                                continuation,
                                                ..
                                            } => {
                                                assert_eq!(from.name().to_string(), "Logger");
                                                assert_eq!(to.name().to_string(), "Client");
                                                assert_eq!(message.name.to_string(), "Ack");
                                                assert!(matches!(
                                                    continuation.as_ref(),
                                                    Protocol::Var(_)
                                                ));
                                            }
                                            _ => panic!("Expected Send for Ack"),
                                        }
                                    }
                                    _ => panic!("Expected Send for Log"),
                                }
                            }
                            _ => panic!("Expected Send for Request"),
                        }

                        // Done branch sends to Server (same as first message target)
                        let done_branch = &branches.as_slice()[1];
                        match &done_branch.protocol {
                            Protocol::Send { from, to, .. } => {
                                assert_eq!(from.name().to_string(), "Client");
                                assert_eq!(to.name().to_string(), "Server");
                            }
                            _ => panic!("Expected Send in Done branch"),
                        }
                    }
                    _ => panic!("Expected Choice"),
                }
            }
            _ => panic!("Expected Rec"),
        }
    }

    #[test]
    fn test_role_decides_with_type_annotation() {
        // Test that type annotations are preserved through desugaring
        let input = r#"
protocol TypedLoop =
  roles Client, Server
  loop decide by Client
    Client -> Server : Request of builtins.String
    Server -> Client : Response of builtins.U32
"#;

        let result = parse_choreography_str(input);
        assert!(result.is_ok(), "Failed to parse: {:?}", result.err());

        let choreo = result.unwrap();
        match &choreo.protocol {
            Protocol::Rec { body, .. } => {
                match body.as_ref() {
                    Protocol::Choice { branches, .. } => {
                        let continue_branch = branches.first();
                        match &continue_branch.protocol {
                            Protocol::Send {
                                message,
                                continuation,
                                ..
                            } => {
                                assert_eq!(message.name.to_string(), "Request");
                                assert!(message.payload.is_some());
                                let type_str = message.payload.as_ref().unwrap().to_string();
                                assert!(
                                    type_str.contains("String"),
                                    "Expected String type, got: {}",
                                    type_str
                                );

                                match continuation.as_ref() {
                                    Protocol::Send { message, .. } => {
                                        assert_eq!(message.name.to_string(), "Response");
                                        assert!(message.payload.is_some());
                                        let type_str = message.payload.as_ref().unwrap().to_string();
                                        assert!(
                                            type_str.contains("U32"),
                                            "Expected U32 type, got: {}",
                                            type_str
                                        );
                                    }
                                    _ => panic!("Expected Send for Response"),
                                }
                            }
                            _ => panic!("Expected Send for Request"),
                        }
                    }
                    _ => panic!("Expected Choice"),
                }
            }
            _ => panic!("Expected Rec"),
        }
    }

    #[test]
    fn test_role_decides_first_stmt_is_choice_no_desugar() {
        // When the first statement is NOT a Send (e.g., it's a choice),
        // the loop should NOT be desugared
        let input = r#"
protocol FirstIsChoice =
  roles A, B
  loop decide by A
    choice A at
      | opt1 =>
        A -> B : Msg1
      | opt2 =>
        A -> B : Msg2
"#;

        let result = parse_choreography_str(input);
        assert!(result.is_ok(), "Failed to parse: {:?}", result.err());

        let choreo = result.unwrap();
        // Should remain as Loop, not desugared
        match &choreo.protocol {
            Protocol::Loop { condition, body } => {
                match condition {
                    Some(Condition::RoleDecides(role)) => {
                        assert_eq!(role.name().to_string(), "A");
                    }
                    _ => panic!("Expected RoleDecides condition"),
                }
                // Body should be a Choice
                match body.as_ref() {
                    Protocol::Choice { .. } => {}
                    _ => panic!("Expected Choice in body"),
                }
            }
            _ => panic!("Expected Loop (not desugared) when first statement is not a Send"),
        }
    }

    // ── annotations_and_parallel ─────────────────────────────────────

    #[test]
    fn test_role_decides_followed_by_statements() {
        // Test that statements after the loop are preserved
        let input = r#"
protocol LoopThenMore =
  roles A, B
  loop decide by A
    A -> B : Request
    B -> A : Response
  A -> B : Goodbye
"#;

        let result = parse_choreography_str(input);
        assert!(result.is_ok(), "Failed to parse: {:?}", result.err());

        let choreo = result.unwrap();
        // The loop should be desugared, followed by the Goodbye send
        match &choreo.protocol {
            Protocol::Rec { body, .. } => {
                match body.as_ref() {
                    Protocol::Choice { branches, .. } => {
                        // Done branch should continue to the Goodbye message
                        let done_branch = &branches.as_slice()[1];
                        match &done_branch.protocol {
                            Protocol::Send {
                                message,
                                continuation,
                                ..
                            } => {
                                assert_eq!(message.name.to_string(), "Done");
                                // After Done, should be the Goodbye send
                                match continuation.as_ref() {
                                    Protocol::Send { message, .. } => {
                                        assert_eq!(message.name.to_string(), "Goodbye");
                                    }
                                    _ => panic!("Expected Goodbye after Done"),
                                }
                            }
                            _ => panic!("Expected Send in Done branch"),
                        }
                    }
                    _ => panic!("Expected Choice"),
                }
            }
            _ => panic!("Expected Rec"),
        }
    }

    #[test]
    fn test_role_decides_multiple_loops() {
        // Test two consecutive RoleDecides loops
        let input = r#"
protocol TwoLoops =
  roles A, B
  loop decide by A
    A -> B : First
  loop decide by B
    B -> A : Second
"#;

        let result = parse_choreography_str(input);
        assert!(result.is_ok(), "Failed to parse: {:?}", result.err());

        let choreo = result.unwrap();
        // First loop should be Rec
        match &choreo.protocol {
            Protocol::Rec { label, body } => {
                assert_eq!(label.to_string(), "RoleDecidesLoop");
                match body.as_ref() {
                    Protocol::Choice { role, branches, .. } => {
                        assert_eq!(role.name().to_string(), "A");

                        // Done branch should lead to second loop
                        let done_branch = &branches.as_slice()[1];
                        match &done_branch.protocol {
                            Protocol::Send { continuation, .. } => {
                                // After first loop's Done, should be second Rec
                                match continuation.as_ref() {
                                    Protocol::Rec { body, .. } => match body.as_ref() {
                                        Protocol::Choice { role, .. } => {
                                            assert_eq!(role.name().to_string(), "B");
                                        }
                                        _ => panic!("Expected Choice in second loop"),
                                    },
                                    _ => panic!("Expected second Rec after first loop"),
                                }
                            }
                            _ => panic!("Expected Send in Done branch"),
                        }
                    }
                    _ => panic!("Expected Choice in first loop"),
                }
            }
            _ => panic!("Expected Rec"),
        }
    }

    #[test]
    fn test_role_decides_empty_body_edge_case() {
        // Edge case: empty loop body (should parse but not desugar - no first statement)
        // Note: This tests the parser's robustness, not valid protocol design
        let input = r#"
protocol EmptyBody =
  roles A, B
  loop decide by A
  A -> B : AfterLoop
"#;

        // This might fail to parse or produce a Loop with empty body
        // Either way, we should handle it gracefully
        let result = parse_choreography_str(input);
        // Just verify it doesn't panic - the exact behavior depends on grammar
        if let Ok(choreo) = result {
            // If parsed, should not be desugared (no first Send)
            match &choreo.protocol {
                Protocol::Loop { .. } => {
                    // Expected: Loop not desugared due to empty/invalid body
                }
                Protocol::Send { .. } => {
                    // Also acceptable: empty loop might be elided
                }
                _ => {
                    // Any other result is acceptable for this edge case
                }
            }
        }
        // Parsing failure is also acceptable for this malformed input
    }

    #[test]
    fn test_role_decides_preserves_branch_label_from_message() {
        // Verify that the branch label matches the first message name exactly
        let input = r#"
protocol CustomMessageName =
  roles Producer, Consumer
  loop decide by Producer
    Producer -> Consumer : DataChunk
    Consumer -> Producer : Ack
"#;

        let result = parse_choreography_str(input);
        assert!(result.is_ok());

        let choreo = result.unwrap();
        match &choreo.protocol {
            Protocol::Rec { body, .. } => {
                match body.as_ref() {
                    Protocol::Choice { branches, .. } => {
                        // First branch label should be "DataChunk" (the message name)
                        let continue_branch = branches.first();
                        assert_eq!(continue_branch.label.to_string(), "DataChunk");

                        // Second branch label should be "Done"
                        let done_branch = &branches.as_slice()[1];
                        assert_eq!(done_branch.label.to_string(), "Done");
                    }
                    _ => panic!("Expected Choice"),
                }
            }
            _ => panic!("Expected Rec"),
        }
    }

    #[test]
    fn test_role_decides_done_message_targets_same_receiver() {
        // The Done message should go to the same receiver as the first message
        let input = r#"
protocol TargetConsistency =
  roles Sender, Receiver, Observer
  loop decide by Sender
    Sender -> Receiver : Data
    Receiver -> Observer : Forward
"#;

        let result = parse_choreography_str(input);
        assert!(result.is_ok());

        let choreo = result.unwrap();
        match &choreo.protocol {
            Protocol::Rec { body, .. } => {
                match body.as_ref() {
                    Protocol::Choice { branches, .. } => {
                        // Continue branch sends to Receiver
                        let continue_branch = branches.first();
                        match &continue_branch.protocol {
                            Protocol::Send { to, .. } => {
                                assert_eq!(to.name().to_string(), "Receiver");
                            }
                            _ => panic!("Expected Send"),
                        }

                        // Done branch should also send to Receiver (same target)
                        let done_branch = &branches.as_slice()[1];
                        match &done_branch.protocol {
                            Protocol::Send { from, to, .. } => {
                                assert_eq!(from.name().to_string(), "Sender");
                                assert_eq!(to.name().to_string(), "Receiver");
                            }
                            _ => panic!("Expected Send in Done branch"),
                        }
                    }
                    _ => panic!("Expected Choice"),
                }
            }
            _ => panic!("Expected Rec"),
        }
    }

    #[test]
    fn test_parse_parallel_branches() {
        let input = r#"
protocol Parallel =
  roles A, B, C, D
  par
    | A -> B : Msg1
    | C -> D : Msg2
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse parallel: {:?}",
            result.err()
        );

        let choreo = result.unwrap();
        match choreo.protocol {
            Protocol::Parallel { protocols } => {
                assert_eq!(protocols.len(), 2);
            }
            _ => panic!("Expected top-level parallel protocol"),
        }
    }

    #[test]
    fn test_single_branch_is_error() {
        let input = r#"
protocol SingleBranch =
  roles A, B
  par
    | A -> B : Msg
"#;

        let result = parse_choreography_str(input);
        assert!(result.is_err());
    }

    #[test]
    fn test_parse_timeout_branch_surface() {
        let input = r#"
protocol TimedRequest =
  roles Alice, Bob
  timeout 5s Alice at
    Alice -> Bob : Request
  on timeout =>
    Alice -> Bob : Cancel
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse timeout surface: {:?}",
            result.err()
        );

        let choreo = result.unwrap();
        assert_eq!(choreo.name.to_string(), "TimedRequest");

        match &choreo.protocol {
            Protocol::Timeout {
                role,
                duration_ms,
                on_cancel,
                ..
            } => {
                assert_eq!(role.name().to_string(), "Alice");
                assert_eq!(*duration_ms, 5_000);
                assert!(on_cancel.is_none());
            }
            _ => panic!("Expected Timeout as first protocol"),
        }
    }

    #[test]
    fn test_parse_timeout_milliseconds() {
        let input = r#"
protocol QuickTimeout =
  roles Client, Server
  timeout 500ms Client at
    Server -> Client : Data
  on timeout =>
    Client -> Server : Abort
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse timeout with ms: {:?}",
            result.err()
        );

        let choreo = result.unwrap();
        match &choreo.protocol {
            Protocol::Timeout { duration_ms, .. } => {
                assert_eq!(*duration_ms, 500);
            }
            _ => panic!("Expected Timeout as first protocol"),
        }
    }

    #[test]
    fn test_parse_timeout_minutes() {
        let input = r#"
protocol LongTimeout =
  roles A, B
  timeout 2m A at
    B -> A : Complete
  on timeout =>
    A -> B : Timeout
"#;

        let result = parse_choreography_str(input);
        assert!(result.is_ok(), "Failed to parse: {:?}", result.err());

        let choreo = result.unwrap();
        match &choreo.protocol {
            Protocol::Timeout { duration_ms, .. } => {
                assert_eq!(*duration_ms, 120_000);
            }
            _ => panic!("Expected Timeout"),
        }
    }

    #[test]
    fn test_parse_heartbeat() {
        let input = r#"
protocol Liveness =
  roles Alice, Bob
  heartbeat Alice -> Bob every 1s on_missing(3) {
    Bob -> Alice : Disconnect
  } body {
    Alice -> Bob : Data
  }
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse heartbeat: {:?}",
            result.err()
        );

        let choreo = result.unwrap();
        assert_eq!(choreo.name.to_string(), "Liveness");

        // Heartbeat desugars to: rec HeartbeatLoop { ... }
        match &choreo.protocol {
            Protocol::Rec { label, body } => {
                assert_eq!(label.to_string(), "HeartbeatLoop");

                // Inside: Sender -> Receiver: Heartbeat; choice Receiver at { ... }
                match body.as_ref() {
                    Protocol::Send {
                        from,
                        to,
                        message,
                        continuation,
                        ..
                    } => {
                        assert_eq!(from.name().to_string(), "Alice");
                        assert_eq!(to.name().to_string(), "Bob");
                        assert_eq!(message.name.to_string(), "Heartbeat");

                        // Continuation is Choice at Receiver
                        match continuation.as_ref() {
                            Protocol::Choice {
                                role,
                                branches,
                                annotations,
                            } => {
                                assert_eq!(role.name().to_string(), "Bob");
                                assert_eq!(branches.len(), 2);
                                assert_eq!(branches[0].label.to_string(), "Alive");
                                assert_eq!(branches[1].label.to_string(), "Dead");

                                // Check heartbeat annotation
                                assert!(annotations.has_heartbeat());
                                let (interval, on_missing) = annotations.heartbeat().unwrap();
                                assert_eq!(interval, std::time::Duration::from_secs(1));
                                assert_eq!(on_missing, 3);
                            }
                            _ => panic!("Expected Choice as continuation"),
                        }
                    }
                    _ => panic!("Expected Send inside Rec"),
                }
            }
            _ => panic!("Expected Rec as top-level protocol"),
        }
    }

    #[test]
    fn test_parse_heartbeat_milliseconds() {
        let input = r#"
protocol FastHeartbeat =
  roles Client, Server
  heartbeat Client -> Server every 500ms on_missing(5) {
    Server -> Client : Dead
  } body {
    Client -> Server : Ping
  }
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse heartbeat with ms: {:?}",
            result.err()
        );

        let choreo = result.unwrap();
        match &choreo.protocol {
            Protocol::Rec { body, .. } => match body.as_ref() {
                Protocol::Send { continuation, .. } => match continuation.as_ref() {
                    Protocol::Choice { annotations, .. } => {
                        assert!(annotations.has_heartbeat());
                        let (interval, on_missing) = annotations.heartbeat().unwrap();
                        assert_eq!(interval, std::time::Duration::from_millis(500));
                        assert_eq!(on_missing, 5);
                    }
                    _ => panic!("Expected Choice"),
                },
                _ => panic!("Expected Send"),
            },
            _ => panic!("Expected Rec"),
        }
    }

    #[test]
    fn test_parse_runtime_timeout_annotation() {
        let input = r#"
protocol TimedRequest =
  roles Client, Server
  Client { runtime_timeout = 5s } -> Server : Request
  Server -> Client : Response
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse sender-record runtime_timeout: {:?}",
            result.err()
        );

        let choreo = result.unwrap();
        match &choreo.protocol {
            Protocol::Send {
                annotations,
                continuation,
                ..
            } => {
                // Check the runtime_timeout annotation was parsed
                assert!(annotations.has_runtime_timeout());
                let timeout = annotations.runtime_timeout().unwrap();
                assert_eq!(timeout, std::time::Duration::from_secs(5));

                // Check continuation doesn't have the annotation
                match continuation.as_ref() {
                    Protocol::Send { annotations, .. } => {
                        assert!(!annotations.has_runtime_timeout());
                    }
                    _ => panic!("Expected Send for Response"),
                }
            }
            _ => panic!("Expected Send for Request"),
        }
    }

    #[test]
    fn test_parse_multiline_runtime_timeout_annotation_with_closing_paren_on_own_line() {
        let input = r#"
protocol TimedRequest =
  roles Client, Server
  Client {
    runtime_timeout = 5s,
  }
    -> Server : Request
  Server -> Client : Response
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse multiline sender-record runtime_timeout: {:?}",
            result.err()
        );

        let choreo = result.unwrap();
        match &choreo.protocol {
            Protocol::Send { annotations, .. } => {
                assert!(annotations.has_runtime_timeout());
                assert_eq!(
                    annotations.runtime_timeout(),
                    Some(std::time::Duration::from_secs(5))
                );
            }
            _ => panic!("Expected Send for Request"),
        }
    }

    #[test]
    fn test_parse_runtime_timeout_milliseconds() {
        let input = r#"
protocol QuickCheck =
  roles A, B
  A { runtime_timeout = 100ms } -> B : Ping
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse sender-record runtime_timeout with ms: {:?}",
            result.err()
        );

        let choreo = result.unwrap();
        match &choreo.protocol {
            Protocol::Send { annotations, .. } => {
                assert!(annotations.has_runtime_timeout());
                let timeout = annotations.runtime_timeout().unwrap();
                assert_eq!(timeout, std::time::Duration::from_millis(100));
            }
            _ => panic!("Expected Send"),
        }
    }

    #[test]
    fn test_parse_parallel_annotation() {
        let input = r#"
protocol Broadcast =
  roles Coordinator, Worker
  Coordinator { parallel = true } -> Worker : Task
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse sender-record parallel metadata: {:?}",
            result.err()
        );

        let choreo = result.unwrap();
        match &choreo.protocol {
            Protocol::Send { annotations, .. } => {
                assert!(annotations.has_parallel(), "Expected parallel annotation");
            }
            _ => panic!("Expected Send"),
        }
    }

    #[test]
    fn test_parse_choice_with_bar_prefixed_branches() {
        let input = r#"
protocol Decision =
  roles A, B
  choice A at
    | Accept =>
        A -> B : Ok
    | Reject =>
        A -> B : No
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse choice with bar-prefixed branches: {:?}",
            result.err()
        );

        let choreo = result.unwrap();
        match &choreo.protocol {
            Protocol::Choice { branches, .. } => {
                assert_eq!(branches.len(), 2);
                assert_eq!(branches.first().label.to_string(), "Accept");
                assert_eq!(branches.as_slice()[1].label.to_string(), "Reject");
            }
            _ => panic!("Expected Choice"),
        }
    }

    #[test]
    fn test_parse_par_with_single_line_bar_branches() {
        let input = r#"
protocol ParallelBars =
  roles A, B, C, D
  par
    | A -> B : Left
    | C -> D : Right
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse `par` with single-line branches: {:?}",
            result.err()
        );

        let choreo = result.unwrap();
        match &choreo.protocol {
            Protocol::Parallel { protocols } => {
                assert_eq!(protocols.len(), 2);
            }
            _ => panic!("Expected Parallel"),
        }
    }

    #[test]
    fn test_parse_par_with_block_branch() {
        let input = r#"
protocol ParallelBarsBlock =
  roles A, B, C, D
  par
    |
      A -> B : Left
      B -> A : Ack
    | C -> D : Right
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse `par` with block branch: {:?}",
            result.err()
        );

        let choreo = result.unwrap();
        match &choreo.protocol {
            Protocol::Parallel { protocols } => {
                assert_eq!(protocols.len(), 2);
                match &protocols.first() {
                    Protocol::Send { continuation, .. } => {
                        assert!(matches!(continuation.as_ref(), Protocol::Send { .. }));
                    }
                    _ => panic!("Expected first branch to be a send sequence"),
                }
            }
            _ => panic!("Expected Parallel"),
        }
    }

    #[test]
    fn test_reject_par_without_bar_branches() {
        let input = r#"
protocol ParallelMissingBars =
  roles A, B, C, D
  par
    A -> B : Left
    C -> D : Right
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_err(),
            "`par` branches must be introduced with `|`"
        );
    }

    #[test]
    fn test_parse_sender_role_annotation_block() {
        let input = r#"
protocol RoleAnnotatedSend =
  roles Role, OtherRole
  Role {
    annotation1 = "value",
    annotation2 = 100,
    annotation3 = another,
  } -> OtherRole : Message of crate.Type
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse sender role annotation block: {:?}",
            result.err()
        );

        let choreo = result.unwrap();
        match &choreo.protocol {
            Protocol::Send {
                from,
                to,
                message,
                from_annotations,
                ..
            } => {
                assert_eq!(from.name().to_string(), "Role");
                assert_eq!(to.name().to_string(), "OtherRole");
                assert_eq!(message.name.to_string(), "Message");
                assert_eq!(
                    message.payload.as_ref().map(ToString::to_string),
                    Some("crate :: Type".to_string())
                );
                assert_eq!(from_annotations.custom("annotation1"), Some("value"));
                assert_eq!(from_annotations.custom("annotation2"), Some("100"));
                assert_eq!(from_annotations.custom("annotation3"), Some("another"));
            }
            _ => panic!("Expected Send"),
        }
    }

    #[test]
    fn test_parse_sender_record_with_aligned_arrow_layout() {
        let input = r#"
protocol StyledSend =
  roles Buyer, Seller
  Buyer { priority = high }
    -> Seller : Request of shop.Order
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse aligned-arrow sender record syntax: {:?}",
            result.err()
        );

        let choreo = result.unwrap();
        match &choreo.protocol {
            Protocol::Send {
                from_annotations,
                message,
                ..
            } => {
                assert_eq!(from_annotations.custom("priority"), Some("high"));
                assert_eq!(
                    message.payload.as_ref().map(ToString::to_string),
                    Some("shop :: Order".to_string())
                );
            }
            _ => panic!("Expected Send"),
        }
    }

    #[test]
    fn test_parse_sender_role_annotation_block_with_indexed_role() {
        let input = r#"
protocol RoleAnnotatedIndexedSend =
  roles Worker[N], Coordinator
  Worker[0] {
    shard = 0,
  } -> Coordinator : Result
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse sender annotation block on indexed role: {:?}",
            result.err()
        );

        let choreo = result.unwrap();
        match &choreo.protocol {
            Protocol::Send {
                from,
                from_annotations,
                ..
            } => {
                assert_eq!(from.name().to_string(), "Worker");
                assert_eq!(
                    from.index().as_ref().map(ToString::to_string),
                    Some("0".to_string())
                );
                assert_eq!(from_annotations.custom("shard"), Some("0"));
            }
            _ => panic!("Expected Send"),
        }
    }

    #[test]
    fn test_parse_sender_role_annotation_block_on_broadcast() {
        let input = r#"
protocol RoleAnnotatedBroadcast =
  roles Coordinator, Worker
  Coordinator {
    batch_size = 100,
  } ->* : Task
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse sender annotation block on broadcast: {:?}",
            result.err()
        );

        let choreo = result.unwrap();
        match &choreo.protocol {
            Protocol::Broadcast {
                from,
                from_annotations,
                ..
            } => {
                assert_eq!(from.name().to_string(), "Coordinator");
                assert_eq!(from_annotations.custom("batch_size"), Some("100"));
            }
            _ => panic!("Expected Broadcast"),
        }
    }

    #[test]
    fn test_reject_sender_metadata_in_square_brackets() {
        let input = r#"
protocol InvalidRoleMetadata =
  roles Role, OtherRole
  Role[annotation1 = "value"] -> OtherRole : Message
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_err(),
            "square brackets must stay reserved for role indexing"
        );
    }

    #[test]
    fn test_parse_ordered_annotation() {
        let input = r#"
protocol OrderedCollect =
  roles Coordinator, Worker
  Worker { ordered = true } -> Coordinator : Result
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse sender-record ordered metadata: {:?}",
            result.err()
        );

        let choreo = result.unwrap();
        match &choreo.protocol {
            Protocol::Send { annotations, .. } => {
                assert!(annotations.has_ordered(), "Expected ordered annotation");
            }
            _ => panic!("Expected Send"),
        }
    }

    // ── proof_bundles_predicates ──────────────────────────────────────

    #[test]
    fn test_parse_min_responses_annotation() {
        let input = r#"
protocol ThresholdSign =
  roles Coordinator, Signer
  Signer { min_responses = 3 } -> Coordinator : Signature
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse sender-record min_responses: {:?}",
            result.err()
        );

        let choreo = result.unwrap();
        match &choreo.protocol {
            Protocol::Send { annotations, .. } => {
                assert!(
                    annotations.has_min_responses(),
                    "Expected min_responses annotation"
                );
                assert_eq!(annotations.min_responses(), Some(3));
            }
            _ => panic!("Expected Send"),
        }
    }

    #[test]
    fn test_parse_multiline_min_responses_annotation_with_closing_paren_on_own_line() {
        let input = r#"
protocol ThresholdSign =
  roles Coordinator, Signer
  Signer {
    min_responses = 3,
  }
    -> Coordinator : Signature
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse multiline sender-record min_responses: {:?}",
            result.err()
        );

        let choreo = result.unwrap();
        match &choreo.protocol {
            Protocol::Send { annotations, .. } => {
                assert!(
                    annotations.has_min_responses(),
                    "Expected multiline min_responses annotation"
                );
                assert_eq!(annotations.min_responses(), Some(3));
            }
            _ => panic!("Expected Send"),
        }
    }

    #[test]
    fn test_parse_combined_annotations() {
        let input = r#"
protocol ParallelThreshold =
  roles Coordinator, Worker
  Worker {
    parallel = true,
    min_responses = 2,
  } -> Coordinator : Vote
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse combined sender-record metadata: {:?}",
            result.err()
        );

        let choreo = result.unwrap();
        match &choreo.protocol {
            Protocol::Send { annotations, .. } => {
                assert!(annotations.has_parallel(), "Expected parallel annotation");
                assert!(
                    annotations.has_min_responses(),
                    "Expected min_responses annotation"
                );
                assert_eq!(annotations.min_responses(), Some(2));
            }
            _ => panic!("Expected Send"),
        }
    }

    #[test]
    fn test_parse_proof_bundles_and_protocol_requires_metadata() {
        let input = r#"
proof_bundle Base requires [guard_tokens, delegation]
proof_bundle Extra requires [knowledge_flow]
protocol WithBundles requires Base, Extra =
  roles A, B
  A -> B : Ping
"#;

        let choreo = parse_choreography_str(input).expect("parse should succeed");
        let bundles = choreo.proof_bundles();
        assert_eq!(bundles.len(), 2);
        assert_eq!(bundles[0].name, "Base");
        assert_eq!(
            bundles[0].capabilities,
            vec!["guard_tokens".to_string(), "delegation".to_string()]
        );
        assert_eq!(bundles[1].name, "Extra");
        assert_eq!(bundles[1].capabilities, vec!["knowledge_flow".to_string()]);
        assert_eq!(
            choreo.required_proof_bundles(),
            vec!["Base".to_string(), "Extra".to_string()]
        );
    }

    #[test]
    fn test_parse_vm_core_statements_into_extensions() {
        fn collect_vm_ops(protocol: &Protocol, out: &mut Vec<String>) {
            match protocol {
                Protocol::Extension {
                    annotations,
                    continuation,
                    ..
                } => {
                    if let Some(op) = annotations.custom("vm_core_op") {
                        out.push(op.to_string());
                    }
                    collect_vm_ops(continuation, out);
                }
                Protocol::Send { continuation, .. }
                | Protocol::Broadcast { continuation, .. }
                | Protocol::Publish { continuation, .. }
                | Protocol::Handoff { continuation, .. }
                | Protocol::DependentWork { continuation, .. } => {
                    collect_vm_ops(continuation, out);
                }
                Protocol::Let { continuation, .. } => collect_vm_ops(continuation, out),
                Protocol::Choice { branches, .. } => {
                    for branch in branches {
                        collect_vm_ops(&branch.protocol, out);
                    }
                }
                Protocol::Case { branches, .. } => {
                    for branch in branches {
                        collect_vm_ops(&branch.protocol, out);
                    }
                }
                Protocol::Timeout {
                    body,
                    on_timeout,
                    on_cancel,
                    ..
                } => {
                    collect_vm_ops(body, out);
                    collect_vm_ops(on_timeout, out);
                    if let Some(on_cancel) = on_cancel.as_deref() {
                        collect_vm_ops(on_cancel, out);
                    }
                }
                Protocol::Loop { body, .. } | Protocol::Rec { body, .. } => {
                    collect_vm_ops(body, out);
                }
                Protocol::Parallel { protocols } => {
                    for protocol in protocols {
                        collect_vm_ops(protocol, out);
                    }
                }
                Protocol::Var(_) | Protocol::End => {}
            }
        }

        let input = r#"
protocol VmOps =
  roles A, B
  acquire guard as token
  transfer token to B with bundle Base
  check k for B into out
  A -> B : Ping
"#;

        let choreo = parse_choreography_str(input).expect("parse should succeed");
        let mut vm_ops = Vec::new();
        collect_vm_ops(&choreo.protocol, &mut vm_ops);
        assert_eq!(
            vm_ops,
            vec![
                "acquire".to_string(),
                "transfer".to_string(),
                "check".to_string()
            ]
        );
    }

    #[test]
    fn test_validate_missing_required_bundle_fails() {
        let input = r#"
protocol MissingBundle requires Core =
  roles A, B
  A -> B : Ping
"#;

        let choreo = parse_choreography_str(input).expect("parse should succeed");
        let err = choreo.validate().expect_err("validation should fail");
        assert!(matches!(
            err,
            ValidationError::MissingProofBundle(ref name) if name == "Core"
        ));
    }

    #[test]
    fn test_validate_missing_capability_fails() {
        let input = r#"
proof_bundle DelegationOnly requires [delegation]
protocol NeedGuard requires DelegationOnly =
  roles A, B
  acquire guard as token
  A -> B : Ping
"#;

        let choreo = parse_choreography_str(input).expect("parse should succeed");
        let err = choreo.validate().expect_err("validation should fail");
        assert!(matches!(
            err,
            ValidationError::MissingCapability(ref cap) if cap == "guard_tokens"
        ));
    }

    #[test]
    fn test_validate_duplicate_bundle_fails() {
        let input = r#"
proof_bundle Core requires [delegation]
proof_bundle Core requires [guard_tokens]
protocol DuplicateBundle requires Core =
  roles A, B
  A -> B : Ping
"#;

        let choreo = parse_choreography_str(input).expect("parse should succeed");
        let err = choreo.validate().expect_err("validation should fail");
        assert!(matches!(
            err,
            ValidationError::DuplicateProofBundle(ref name) if name == "Core"
        ));
    }

    #[test]
    fn test_parse_guard_predicate_rejects_non_boolean_expression() {
        let input = r#"
protocol GuardTypeCheck =
  roles A, B
  choice A at
    | ok when (count + 1) =>
      A -> B : Ack
    | no =>
      A -> B : Nack
"#;

        let err = parse_choreography_str(input).expect_err("guard should fail");
        assert!(matches!(err, ParseError::Syntax { .. }));
        assert!(err.to_string().contains("boolean-like"));
    }

    #[test]
    fn test_parse_loop_while_rejects_non_boolean_expression() {
        let input = r#"
protocol LoopTypeCheck =
  roles A, B
  loop while "count + 1"
    A -> B : Tick
"#;

        let err = parse_choreography_str(input).expect_err("loop condition should fail");
        assert!(matches!(err, ParseError::InvalidCondition { .. }));
        assert!(err.to_string().contains("boolean-like"));
    }

    #[test]
    fn test_projection_preserves_continuation_after_extension() {
        let input = r#"
protocol ExtensionProjection =
  roles A, B
  acquire guard as token
  A -> B : Ping
"#;

        let choreo = parse_choreography_str(input).expect("parse should succeed");
        let role_a = choreo
            .roles
            .iter()
            .find(|r| r.name() == "A")
            .expect("role A should exist");
        let projected =
            crate::compiler::projection::project(&choreo, role_a).expect("projection must work");

        match projected {
            LocalType::Send { to, .. } => assert_eq!(to.name(), "B"),
            other => panic!("expected send continuation projection, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_enriched_proof_bundle_metadata() {
        let input = r#"
proof_bundle Base version "1.0.0" issuer "did:example:issuer" constraint "fresh_nonce" constraint "sig_valid" requires [delegation, guard_tokens]
protocol BundleMeta requires Base =
  roles A, B
  A -> B : Ping
"#;

        let choreo = parse_choreography_str(input).expect("parse should succeed");
        let bundles = choreo.proof_bundles();
        assert_eq!(bundles.len(), 1);
        let bundle = &bundles[0];
        assert_eq!(bundle.name, "Base");
        assert_eq!(bundle.version.as_deref(), Some("1.0.0"));
        assert_eq!(bundle.issuer.as_deref(), Some("did:example:issuer"));
        assert_eq!(
            bundle.constraints,
            vec!["fresh_nonce".to_string(), "sig_valid".to_string()]
        );
        assert_eq!(
            bundle.capabilities,
            vec!["delegation".to_string(), "guard_tokens".to_string()]
        );
    }

    #[test]
    fn test_infer_required_bundles_from_vm_capabilities() {
        let input = r#"
proof_bundle Spec requires [speculation]
protocol Inferred =
  roles A, B
  fork ghost0
  A -> B : Ping
"#;

        let choreo = parse_choreography_str(input).expect("parse should succeed");
        assert_eq!(choreo.required_proof_bundles(), vec!["Spec".to_string()]);
        assert_eq!(
            choreo.inferred_required_proof_bundles(),
            vec!["Spec".to_string()]
        );
        assert!(choreo.validate().is_ok());
    }

    #[test]
    fn test_linear_assets_reject_double_consume() {
        let input = r#"
protocol LinearDoubleConsume =
  roles A, B
  acquire guard as token
  release guard using token
  release guard using token
"#;

        let err = parse_choreography_str(input).expect_err("parse should fail");
        assert!(err.to_string().contains("before acquire"));
    }

    #[test]
    fn test_linear_assets_reject_branch_divergence() {
        let input = r#"
protocol LinearBranchDivergence =
  roles A, B
  acquire guard as token
  choice A at
    | consume =>
      release guard using token
    | keep =>
      A -> B : Skip
"#;

        let err = parse_choreography_str(input).expect_err("parse should fail");
        assert!(err.to_string().contains("diverge"));
    }

    #[test]
    fn test_parse_first_class_combinators() {
        fn has_quorum_extension(protocol: &Protocol) -> bool {
            match protocol {
                Protocol::Extension {
                    annotations,
                    continuation,
                    ..
                } => {
                    annotations.custom("dsl_combinator") == Some("quorum_collect")
                        || has_quorum_extension(continuation)
                }
                Protocol::Send { continuation, .. }
                | Protocol::Broadcast { continuation, .. }
                | Protocol::Publish { continuation, .. }
                | Protocol::Handoff { continuation, .. }
                | Protocol::DependentWork { continuation, .. } => has_quorum_extension(continuation),
                Protocol::Let { continuation, .. } => has_quorum_extension(continuation),
                Protocol::Choice { branches, .. } => {
                    branches.iter().any(|b| has_quorum_extension(&b.protocol))
                }
                Protocol::Case { branches, .. } => {
                    branches.iter().any(|b| has_quorum_extension(&b.protocol))
                }
                Protocol::Timeout {
                    body,
                    on_timeout,
                    on_cancel,
                    ..
                } => {
                    has_quorum_extension(body)
                        || has_quorum_extension(on_timeout)
                        || on_cancel.as_deref().is_some_and(has_quorum_extension)
                }
                Protocol::Loop { body, .. } | Protocol::Rec { body, .. } => has_quorum_extension(body),
                Protocol::Parallel { protocols } => protocols.iter().any(has_quorum_extension),
                Protocol::Var(_) | Protocol::End => false,
            }
        }

        let input = r#"
protocol Combinators =
  roles A, B
  handshake A <-> B : Hello
  quorum_collect A -> B min 2 : Vote
  A -> B : Done
  retry 2 {
    A -> B : Ping
  }
"#;

        let choreo = parse_choreography_str(input).expect("parse should succeed");
        match &choreo.protocol {
            Protocol::Send {
                from,
                to,
                message,
                continuation,
                ..
            } => {
                assert_eq!(from.name(), "A");
                assert_eq!(to.name(), "B");
                assert_eq!(message.name.to_string(), "Hello");
                match continuation.as_ref() {
                    Protocol::Send { message, .. } => {
                        assert_eq!(message.name.to_string(), "HelloAck");
                    }
                    _ => panic!("expected second send from handshake"),
                }
            }
            _ => panic!("expected send from handshake lowering"),
        }
        assert!(has_quorum_extension(&choreo.protocol));
    }

    #[test]
    fn test_parse_role_sets_and_topologies() {
        let input = r#"
role_set Signers = Alice, Bob, Carol
role_set Quorum = subset(Signers, 0..2)
cluster LocalCluster = Signers, Quorum
ring RingNet = Alice, Bob, Carol
mesh FullMesh = Alice, Bob, Carol
protocol TopologyAware =
  roles Alice, Bob
  Alice -> Bob : Ping
"#;

        let choreo = parse_choreography_str(input).expect("parse should succeed");
        let role_sets = choreo.role_sets();
        assert_eq!(role_sets.len(), 2);
        assert_eq!(role_sets[0].name, "Signers");
        assert_eq!(
            role_sets[0].members,
            vec!["Alice".to_string(), "Bob".to_string(), "Carol".to_string()]
        );
        assert_eq!(role_sets[1].subset_of.as_deref(), Some("Signers"));
        assert_eq!(role_sets[1].subset_start, Some(0));
        assert_eq!(role_sets[1].subset_end, Some(2));

        let topologies = choreo.topologies();
        assert_eq!(topologies.len(), 3);
        assert_eq!(topologies[0].kind, "cluster");
        assert_eq!(topologies[1].kind, "ring");
        assert_eq!(topologies[2].kind, "mesh");
    }

    #[test]
    fn test_explain_lowering_and_lint_suggestions() {
        let input = r#"
proof_bundle Spec requires [speculation]
protocol ExplainMe =
  roles A, B
  fork ghost0
  A -> B : Ping
"#;

        let report = explain_lowering(input).expect("report generation should succeed");
        assert!(report.contains("Inferred bundles: Spec"));
        assert!(report.contains("dsl.inferred_requires"));
        assert!(report.contains("Lowering:"));

        let choreo = parse_choreography_str(input).expect("parse should succeed");
        let lints = collect_dsl_lints(&choreo, LintLevel::Warn);
        assert!(!lints.is_empty());
        assert!(lints[0]
            .suggestion
            .as_deref()
            .unwrap_or_default()
            .contains("requires"));
        let lsp = render_lsp_lint_diagnostics(&choreo, LintLevel::Warn);
        assert!(lsp.contains("\"quickFix\""));
    }

    #[test]
    fn test_typed_predicate_ir_rejects_if_expression() {
        let input = r#"
protocol PredicateTyping =
  roles A, B
  choice A at
    | ok when (if ready { true } else { false }) =>
      A -> B : Accept
    | no =>
      A -> B : Reject
"#;

        let err = parse_choreography_str(input).expect_err("parse should fail");
        assert!(matches!(err, ParseError::Syntax { .. }));
        assert!(err.to_string().contains("boolean-like"));
    }

    #[test]
    fn test_parse_choreography_macro_tokens_basic() {
        let input: TokenStream = quote::quote! {
            protocol PingPong = {
                roles Alice, Bob;
                Alice -> Bob : Ping;
                Bob -> Alice : Pong;
            }
        };

        let choreo = parse_choreography(input).expect("macro token parsing should succeed");
        assert_eq!(choreo.name.to_string(), "PingPong");
        assert_eq!(choreo.roles.len(), 2);
    }

    #[test]
    fn test_parse_choreography_macro_tokens_normalizes_composite_operators() {
        let input: TokenStream = quote::quote! {
            protocol Ops = {
                roles A, B;
                handshake A <-> B : Hello;
                A ->* : Notice;
            }
        };

        let choreo = parse_choreography(input).expect("macro token parsing should succeed");
        assert_eq!(choreo.name.to_string(), "Ops");
        assert_eq!(choreo.roles.len(), 2);
    }

    #[test]
    fn test_parse_choreography_macro_tokens_with_sender_record_and_of_payload() {
        let input: TokenStream = quote::quote! {
            protocol Purchase = {
                roles Buyer, Seller;
                Buyer { priority = high } -> Seller : Request of shop.Order;
            }
        };

        let choreo = parse_choreography(input).expect("macro token parsing should succeed");
        match &choreo.protocol {
            Protocol::Send {
                from_annotations,
                message,
                ..
            } => {
                assert_eq!(from_annotations.custom("priority"), Some("high"));
                assert_eq!(
                    message.payload.as_ref().map(ToString::to_string),
                    Some("shop :: Order".to_string())
                );
            }
            _ => panic!("Expected Send"),
        }
    }

    #[test]
    fn test_parse_choreography_macro_string_literal_with_preferred_syntax() {
        let input: TokenStream = quote::quote! {
            r#"
protocol ReplicatedWrite =
  roles Client, Leader, Replica0, Replica1
  Client { priority = high }
    -> Leader : Put of kv.Write
  par
    | Leader { shard = 0 } -> Replica0 : Replicate of kv.Write
    | Leader { shard = 1 } -> Replica1 : Replicate of kv.Write
"#
        };

        let choreo = parse_choreography(input).expect("macro string-literal parsing should succeed");
        match &choreo.protocol {
            Protocol::Send {
                from_annotations,
                message,
                continuation,
                ..
            } => {
                assert_eq!(from_annotations.custom("priority"), Some("high"));
                assert_eq!(
                    message.payload.as_ref().map(ToString::to_string),
                    Some("kv :: Write".to_string())
                );
                match continuation.as_ref() {
                    Protocol::Parallel { protocols } => assert_eq!(protocols.len(), 2),
                    _ => panic!("Expected parallel continuation"),
                }
            }
            _ => panic!("Expected Send"),
        }
    }

    #[test]
    fn test_parse_choreography_macro_tokens_with_choice_bars_and_par() {
        let input: TokenStream = quote::quote! {
            protocol Branchy = {
                roles A, B, C, D;
                par {
                    | {
                        choice A at {
                            | Accept => {
                                A -> B : Ok;
                            }
                            | Reject => {
                                A -> B : No;
                            }
                        }
                    }
                    | B -> D : Right;
                }
            }
        };

        let choreo = parse_choreography(input).expect("macro token parsing should succeed");
        match &choreo.protocol {
            Protocol::Parallel { protocols } => {
                assert_eq!(protocols.len(), 2);
                match protocols.first() {
                    Protocol::Choice { branches, .. } => {
                        assert_eq!(branches.len(), 2);
                        assert_eq!(branches.first().label.to_string(), "Accept");
                        assert_eq!(branches.as_slice()[1].label.to_string(), "Reject");
                    }
                    _ => panic!("Expected choice in first parallel branch"),
                }
            }
            _ => panic!("Expected Parallel"),
        }
    }

    // ── authority_surface ────────────────────────────────────────────

    #[test]
    fn test_parse_authority_surface_with_effects_types_and_uses() {
        let input = r#"
type CommitError =
  | NotReady
  | TimedOut

type alias ReadyWitness = { epoch : Int, issuedBy : Role }

effect Runtime
  authoritative ready : Session -> Result CommitError ReadyWitness
  command transfer : TransferRequest -> Result TransferError TransferReceipt

effect Audit
  observe record : AuditEvent -> Unit

protocol CommitFlow uses Runtime, Audit =
  roles Coordinator, Worker, Client
  let readiness = check Runtime.ready(session)
  case readiness of
    | Ok(witness) =>
        Coordinator -> Worker : Commit(witness)
    | Err(reason) =>
        Coordinator -> Client : Retry(reason)
  timeout 5s Coordinator at
    Worker -> Coordinator : Ready
  on timeout =>
    Coordinator -> Worker : Cancel
  on cancel =>
    Coordinator -> Client : Cancelled
  choice Coordinator at
    | Commit when check Runtime.ready(session) yields witness =>
        Coordinator -> Worker : CommitAgain(witness)
    | Abort =>
        Coordinator -> Worker : Abort
"#;

        let choreography = parse_choreography_str(input).expect("authority surface should parse");
        assert_eq!(choreography.type_decls().len(), 2);
        assert_eq!(choreography.effect_decls().len(), 2);
        assert_eq!(
            choreography.protocol_uses(),
            vec!["Runtime".to_string(), "Audit".to_string()]
        );
        let runtime_metadata = choreography.runtime_effect_metadata();
        assert!(
            runtime_metadata.iter().any(|op| {
                op.interface_name == "Runtime"
                    && op.operation_name == "ready"
                    && op.authority_class == crate::ast::EffectOpAuthorityClass::Authoritative
            }),
            "runtime effect metadata should carry effect authority class"
        );
        choreography.validate().expect("declared effect uses should validate");
    }

    #[test]
    fn test_parse_let_in_and_maybe_surface() {
        let input = r#"
type alias InviteHandle = { id : Int }

effect Runtime
  lookupInvite : Session -> Maybe InviteHandle

protocol InviteFlow uses Runtime =
  roles Coordinator, Worker
  let invite = check Runtime.lookupInvite(session) in
    case invite of
      | Just(handle) =>
          Coordinator -> Worker : UseInvite(handle)
      | Nothing =>
          Coordinator -> Worker : MissingInvite
"#;

        let choreography = parse_choreography_str(input).expect("let-in Maybe surface should parse");
        choreography.validate().expect("effect invocation should validate");
    }

    #[test]
    fn test_reject_non_exhaustive_result_case() {
        let input = r#"
effect Runtime
  ready : Session -> Result CommitError ReadyWitness

protocol CommitFlow uses Runtime =
  roles Coordinator, Worker
  let readiness = check Runtime.ready(session)
  case readiness of
    | Ok(witness) =>
        Coordinator -> Worker : Commit(witness)
"#;

        let err = parse_choreography_str(input).expect_err("non-exhaustive Result case should fail");
        assert!(!err.to_string().is_empty());
    }

    #[test]
    fn test_reject_duplicate_linear_binding_use() {
        let input = r#"
protocol TransferFlow =
  roles Coordinator, Worker, Client
  let receipt = transfer Session from Coordinator to Worker
  Coordinator -> Worker : TransferAccepted(receipt)
  Coordinator -> Client : ReceiptAudit(receipt)
"#;

        let err = parse_choreography_str(input).expect_err("duplicate linear use should fail");
        assert!(err.to_string().contains("consumed more than once"));
    }

    #[test]
    fn test_reject_dropped_linear_binding_use() {
        let input = r#"
protocol TransferFlow =
  roles Coordinator, Worker
  let receipt = transfer Session from Coordinator to Worker
  Coordinator -> Worker : TransferAccepted
"#;

        let err = parse_choreography_str(input).expect_err("dropped linear binding should fail");
        assert!(err.to_string().contains("never consumed"));
    }

    #[test]
    fn test_reject_undeclared_protocol_use() {
        let input = r#"
protocol CommitFlow uses Runtime =
  roles Coordinator, Worker
  Coordinator -> Worker : Ping
"#;

        let choreography = parse_choreography_str(input).expect("parse should succeed");
        let err = choreography
            .validate()
            .expect_err("undeclared effect interface should fail validation");
        assert!(err.to_string().contains("undeclared effect interface"));
    }

    #[test]
    fn test_reject_undeclared_effect_operation_invocation() {
        let input = r#"
effect Runtime
  ready : Session -> Result CommitError ReadyWitness

protocol CommitFlow uses Runtime =
  roles Coordinator, Worker
  let readiness = check Runtime.lookup(session)
  case readiness of
    | Ok(witness) =>
        Coordinator -> Worker : Commit(witness)
    | Err(reason) =>
        Coordinator -> Worker : Retry(reason)
"#;

        let choreography = parse_choreography_str(input).expect("parse should succeed");
        let err = choreography
            .validate()
            .expect_err("undeclared effect operation should fail validation");
        assert!(err.to_string().contains("undeclared operation"));
    }

    #[test]
    fn test_reject_duplicate_effect_declarations() {
        let input = r#"
effect Runtime
  ready : Session -> Result CommitError ReadyWitness

effect Runtime
  transfer : TransferRequest -> Result TransferError TransferReceipt

protocol CommitFlow uses Runtime =
  roles Coordinator, Worker
  Coordinator -> Worker : Ping
"#;

        let choreography = parse_choreography_str(input).expect("parse should succeed");
        let err = choreography
            .validate()
            .expect_err("duplicate effect declarations should fail validation");
        assert!(err.to_string().contains("duplicate effect interface declaration"));
    }

    #[test]
    fn test_reject_observational_effect_used_with_check() {
        let input = r#"
effect Runtime
  observe watchPresence : Session -> PresenceView

protocol WatchFlow uses Runtime =
  roles Coordinator, Worker
  let presence = check Runtime.watchPresence(session)
  Coordinator -> Worker : Seen(presence)
"#;

        let choreography = parse_choreography_str(input).expect("parse should succeed");
        let err = choreography
            .validate()
            .expect_err("observational effect use should fail validation");
        assert!(err.to_string().contains("observational"));
    }

    #[test]
    fn test_parse_fragments_operations_and_guest_runtime_metadata() {
        let input = r#"
fragment ChannelMembership(channel)

operation syncMembership(channel : ChannelId) at Worker within ChannelMembership(channel) =
  publish SyncQueued(channel)

guest runtime MessagingGuest =
  uses Runtime, Audit
  entry CommitFlow

protocol CommitFlow uses Runtime, Audit =
  roles Coordinator, Worker
  Coordinator -> Worker : Ping
"#;

        let choreography = parse_choreography_str(input).expect("surface metadata should parse");
        assert_eq!(choreography.fragment_decls().len(), 1);
        assert_eq!(choreography.fragment_decls()[0].name, "ChannelMembership");
        assert_eq!(choreography.fragment_decls()[0].params, vec!["channel"]);

        assert_eq!(choreography.operation_decls().len(), 1);
        let operation = &choreography.operation_decls()[0];
        assert_eq!(operation.name, "syncMembership");
        assert_eq!(operation.owner_role, "Worker");
        assert_eq!(operation.within.as_deref(), Some("ChannelMembership(channel)"));
        assert_eq!(operation.params.len(), 1);
        assert!(operation.body_source.contains("publish SyncQueued(channel)"));

        assert_eq!(choreography.guest_runtime_decls().len(), 1);
        let guest_runtime = &choreography.guest_runtime_decls()[0];
        assert_eq!(guest_runtime.name, "MessagingGuest");
        assert_eq!(guest_runtime.uses, vec!["Runtime", "Audit"]);
        assert_eq!(guest_runtime.entry, "CommitFlow");
    }

    #[test]
    fn test_parse_publish_handoff_and_dependent_work_and_fail_projection_closed() {
        let input = r#"
protocol AcceptFlow =
  roles Coordinator, Worker
  publish Started
  let receipt = transfer Session from Coordinator to Worker
  handoff acceptInvite to Worker using receipt
  dependent work SyncMembership(channel) required for acceptInvite
  Coordinator -> Worker : Commit
"#;

        let choreography = parse_choreography_str(input).expect("semantic surface should parse");
        let err = project(&choreography, &choreography.roles[0])
            .expect_err("new semantic forms should remain fail-closed in projection");
        assert!(!err.to_string().is_empty());
    }

    // ── standalone tests ─────────────────────────────────────────────

    #[test]
    fn parse_choreography_file_accepts_tell_extension() {
        let dir = tempdir().expect("tempdir");
        let path = dir.path().join("protocol.tell");
        std::fs::write(&path, "protocol Ping =\n  roles A, B\n  A -> B : Msg\n")
            .expect("write tell fixture");

        let parsed = parse_choreography_file(&path).expect("parse .tell source");
        assert_eq!(parsed.name.to_string(), "Ping");
    }

    #[test]
    fn parse_choreography_file_rejects_choreo_extension() {
        let dir = tempdir().expect("tempdir");
        let path = dir.path().join("protocol.choreo");
        std::fs::write(&path, "protocol Ping =\n  roles A, B\n  A -> B : Msg\n")
            .expect("write choreo fixture");

        let err = parse_choreography_file(&path).expect_err("reject legacy extension");
        let rendered = err.to_string();
        assert!(
            rendered.contains(".tell"),
            "error should point to canonical .tell extension: {rendered}"
        );
    }
}
