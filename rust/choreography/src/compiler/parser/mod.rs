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
mod error;
mod role;
mod statement;
mod stmt_parsers;
mod types;

// Re-export public API
pub use error::{ErrorSpan, ParseError};

use crate::ast::{Choreography, ProofBundleDecl, Protocol, RoleSetDecl, TopologyDecl};
use crate::compiler::layout::preprocess_layout;
use crate::extensions::{ExtensionRegistry, ProtocolExtension};
use pest::Parser;
use pest_derive::Parser;
use proc_macro2::{Span, TokenStream};
use quote::format_ident;
use std::collections::{HashMap, HashSet};
use std::fmt::Write as _;

use conversion::{convert_statements_to_protocol, inline_calls};
use role::parse_roles_from_pair;
use statement::{parse_local_protocol_decl, parse_protocol_body};
use types::{Statement, VmCoreOp};

#[derive(Parser)]
#[grammar = "compiler/choreography.pest"]
struct ChoreographyParser;

/// Parse a namespace declaration from the AST
fn parse_module_decl(
    pair: pest::iterators::Pair<Rule>,
    input: &str,
) -> std::result::Result<String, ParseError> {
    let span = pair.as_span();
    let mut inner = pair.into_inner();
    if let Some(ident) = inner.next() {
        if ident.as_rule() == Rule::ident {
            return Ok(ident.as_str().to_string());
        }
    }
    Err(ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "Invalid module declaration".to_string(),
    })
}

/// Parse a proof-bundle declaration from the AST.
fn parse_proof_bundle_decl(
    pair: pest::iterators::Pair<Rule>,
    input: &str,
) -> std::result::Result<ProofBundleDecl, ParseError> {
    let span = pair.as_span();
    let mut inner = pair.into_inner();
    let Some(name_pair) = inner.next() else {
        return Err(ParseError::Syntax {
            span: ErrorSpan::from_pest_span(span, input),
            message: "Invalid proof_bundle declaration".to_string(),
        });
    };
    if name_pair.as_rule() != Rule::ident {
        return Err(ParseError::Syntax {
            span: ErrorSpan::from_pest_span(span, input),
            message: "Invalid proof_bundle name".to_string(),
        });
    }

    let mut capabilities = Vec::new();
    let mut version = None;
    let mut issuer = None;
    let mut constraints = Vec::new();

    for item in inner {
        match item.as_rule() {
            Rule::proof_bundle_meta => {
                let Some(meta) = item.into_inner().next() else {
                    continue;
                };
                match meta.as_rule() {
                    Rule::proof_bundle_version => {
                        let value = meta.into_inner().next().ok_or_else(|| ParseError::Syntax {
                            span: ErrorSpan::from_pest_span(span, input),
                            message: "proof_bundle version is missing value".to_string(),
                        })?;
                        version = Some(parse_quoted_string(value.as_str()).map_err(|message| {
                            ParseError::Syntax {
                                span: ErrorSpan::from_pest_span(span, input),
                                message,
                            }
                        })?);
                    }
                    Rule::proof_bundle_issuer => {
                        let value = meta.into_inner().next().ok_or_else(|| ParseError::Syntax {
                            span: ErrorSpan::from_pest_span(span, input),
                            message: "proof_bundle issuer is missing value".to_string(),
                        })?;
                        issuer = Some(parse_quoted_string(value.as_str()).map_err(|message| {
                            ParseError::Syntax {
                                span: ErrorSpan::from_pest_span(span, input),
                                message,
                            }
                        })?);
                    }
                    Rule::proof_bundle_constraint => {
                        let value = meta.into_inner().next().ok_or_else(|| ParseError::Syntax {
                            span: ErrorSpan::from_pest_span(span, input),
                            message: "proof_bundle constraint is missing value".to_string(),
                        })?;
                        constraints.push(parse_quoted_string(value.as_str()).map_err(
                            |message| ParseError::Syntax {
                                span: ErrorSpan::from_pest_span(span, input),
                                message,
                            },
                        )?);
                    }
                    _ => {}
                }
            }
            Rule::proof_bundle_requires => {
                for requires_item in item.into_inner() {
                    if requires_item.as_rule() == Rule::capability_list {
                        for cap in requires_item.into_inner() {
                            if cap.as_rule() == Rule::ident {
                                capabilities.push(cap.as_str().to_string());
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }

    Ok(ProofBundleDecl {
        name: name_pair.as_str().to_string(),
        capabilities,
        version,
        issuer,
        constraints,
    })
}

fn parse_quoted_string(value: &str) -> Result<String, String> {
    if value.starts_with('\"') && value.ends_with('\"') && value.len() >= 2 {
        Ok(value[1..value.len() - 1].to_string())
    } else {
        Err("expected quoted string literal".to_string())
    }
}

/// Parse protocol-level required proof bundles.
fn parse_protocol_requires(pair: pest::iterators::Pair<Rule>) -> Vec<String> {
    pair.into_inner()
        .filter(|p| p.as_rule() == Rule::ident)
        .map(|p| p.as_str().to_string())
        .collect()
}

fn parse_role_set_decl(
    pair: pest::iterators::Pair<Rule>,
    input: &str,
) -> std::result::Result<RoleSetDecl, ParseError> {
    let span = pair.as_span();
    let mut inner = pair.into_inner();
    let name = inner
        .next()
        .ok_or_else(|| ParseError::Syntax {
            span: ErrorSpan::from_pest_span(span, input),
            message: "role_set is missing name".to_string(),
        })?
        .as_str()
        .to_string();
    let expr = inner.next().ok_or_else(|| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "role_set is missing expression".to_string(),
    })?;

    let mut decl = RoleSetDecl {
        name,
        members: Vec::new(),
        subset_of: None,
        subset_start: None,
        subset_end: None,
    };

    for expr_item in expr.into_inner() {
        match expr_item.as_rule() {
            Rule::role_set_members => {
                decl.members = expr_item
                    .into_inner()
                    .filter(|p| p.as_rule() == Rule::ident)
                    .map(|p| p.as_str().to_string())
                    .collect();
            }
            Rule::role_set_subset => {
                let mut subset_inner = expr_item.into_inner();
                let source = subset_inner.next().ok_or_else(|| ParseError::Syntax {
                    span: ErrorSpan::from_pest_span(span, input),
                    message: "role_set subset is missing source".to_string(),
                })?;
                let start = subset_inner.next().ok_or_else(|| ParseError::Syntax {
                    span: ErrorSpan::from_pest_span(span, input),
                    message: "role_set subset is missing start".to_string(),
                })?;
                let end = subset_inner.next().ok_or_else(|| ParseError::Syntax {
                    span: ErrorSpan::from_pest_span(span, input),
                    message: "role_set subset is missing end".to_string(),
                })?;
                decl.subset_of = Some(source.as_str().to_string());
                decl.subset_start =
                    Some(
                        start
                            .as_str()
                            .parse::<u32>()
                            .map_err(|_| ParseError::Syntax {
                                span: ErrorSpan::from_pest_span(span, input),
                                message: "role_set subset start must be an integer".to_string(),
                            })?,
                    );
                decl.subset_end =
                    Some(
                        end.as_str()
                            .parse::<u32>()
                            .map_err(|_| ParseError::Syntax {
                                span: ErrorSpan::from_pest_span(span, input),
                                message: "role_set subset end must be an integer".to_string(),
                            })?,
                    );
            }
            _ => {}
        }
    }

    Ok(decl)
}

fn parse_topology_decl(
    pair: pest::iterators::Pair<Rule>,
    input: &str,
) -> std::result::Result<TopologyDecl, ParseError> {
    let span = pair.as_span();
    let mut inner = pair.into_inner();
    let kind = inner
        .next()
        .ok_or_else(|| ParseError::Syntax {
            span: ErrorSpan::from_pest_span(span, input),
            message: "topology declaration is missing kind".to_string(),
        })?
        .as_str()
        .to_string();
    let name = inner
        .next()
        .ok_or_else(|| ParseError::Syntax {
            span: ErrorSpan::from_pest_span(span, input),
            message: "topology declaration is missing name".to_string(),
        })?
        .as_str()
        .to_string();
    let members_pair = inner.next().ok_or_else(|| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "topology declaration is missing members".to_string(),
    })?;
    let members = members_pair
        .into_inner()
        .filter(|p| p.as_rule() == Rule::ident)
        .map(|p| p.as_str().to_string())
        .collect();
    Ok(TopologyDecl {
        kind,
        name,
        members,
    })
}

fn linear_usage_error(input: &str, message: impl Into<String>) -> ParseError {
    ParseError::Syntax {
        span: ErrorSpan::from_line_col(1, 1, input),
        message: message.into(),
    }
}

fn consume_linear_asset(
    live_assets: &mut HashSet<String>,
    asset: &str,
    input: &str,
    op: &str,
) -> Result<(), ParseError> {
    if live_assets.remove(asset) {
        Ok(())
    } else {
        Err(linear_usage_error(
            input,
            format!("linear asset '{asset}' used by {op} before acquire"),
        ))
    }
}

fn validate_linear_vm_assets(statements: &[Statement], input: &str) -> Result<(), ParseError> {
    fn validate_block(
        statements: &[Statement],
        incoming: &HashSet<String>,
        input: &str,
    ) -> Result<HashSet<String>, ParseError> {
        let mut live_assets = incoming.clone();

        for statement in statements {
            match statement {
                Statement::VmCoreOp { op } => match op {
                    VmCoreOp::Acquire { dst, .. } => {
                        if !live_assets.insert(dst.clone()) {
                            return Err(linear_usage_error(
                                input,
                                format!("linear asset '{dst}' acquired more than once"),
                            ));
                        }
                    }
                    VmCoreOp::Release { evidence, .. } => {
                        consume_linear_asset(&mut live_assets, evidence, input, "release")?;
                    }
                    VmCoreOp::Transfer { endpoint, .. } => {
                        consume_linear_asset(&mut live_assets, endpoint, input, "transfer")?;
                    }
                    VmCoreOp::Fork { .. }
                    | VmCoreOp::Join
                    | VmCoreOp::Abort
                    | VmCoreOp::Tag { .. }
                    | VmCoreOp::Check { .. } => {}
                },
                Statement::Choice { branches, .. } | Statement::TimedChoice { branches, .. } => {
                    let mut merged: Option<HashSet<String>> = None;
                    for branch in branches {
                        let out = validate_block(&branch.statements, &live_assets, input)?;
                        if let Some(prev) = &merged {
                            if prev != &out {
                                return Err(linear_usage_error(
                                    input,
                                    "linear assets diverge across choice branches",
                                ));
                            }
                        } else {
                            merged = Some(out);
                        }
                    }
                    if let Some(out) = merged {
                        live_assets = out;
                    }
                }
                Statement::Loop { body, .. } => {
                    let out = validate_block(body, &live_assets, input)?;
                    if out != live_assets {
                        return Err(linear_usage_error(
                            input,
                            "loop body must preserve linear assets across iterations",
                        ));
                    }
                }
                Statement::Rec { body, .. } => {
                    let out = validate_block(body, &live_assets, input)?;
                    if out != live_assets {
                        return Err(linear_usage_error(
                            input,
                            "recursive body must preserve linear assets across unfoldings",
                        ));
                    }
                }
                Statement::Parallel { branches } => {
                    for branch in branches {
                        let out = validate_block(branch, &live_assets, input)?;
                        if out != live_assets {
                            return Err(linear_usage_error(
                                input,
                                "parallel branches must preserve linear assets",
                            ));
                        }
                    }
                }
                Statement::Branch { body, .. } => {
                    let out = validate_block(body, &live_assets, input)?;
                    if out != live_assets {
                        return Err(linear_usage_error(
                            input,
                            "branch blocks must preserve linear assets",
                        ));
                    }
                }
                Statement::Heartbeat {
                    on_missing_body,
                    body,
                    ..
                } => {
                    let alive = validate_block(body, &live_assets, input)?;
                    let missing = validate_block(on_missing_body, &live_assets, input)?;
                    if alive != missing || alive != live_assets {
                        return Err(linear_usage_error(
                            input,
                            "heartbeat branches must preserve identical linear assets",
                        ));
                    }
                }
                Statement::Send { .. }
                | Statement::Broadcast { .. }
                | Statement::Continue { .. }
                | Statement::Handshake { .. }
                | Statement::QuorumCollect { .. }
                | Statement::Call { .. } => {}
            }
        }

        Ok(live_assets)
    }

    validate_block(statements, &HashSet::new(), input).map(|_| ())
}

fn collect_vm_required_capabilities(statements: &[Statement], out: &mut HashSet<String>) {
    for statement in statements {
        match statement {
            Statement::VmCoreOp { op } => {
                out.insert(op.required_capability().to_string());
            }
            Statement::Choice { branches, .. } | Statement::TimedChoice { branches, .. } => {
                for branch in branches {
                    collect_vm_required_capabilities(&branch.statements, out);
                }
            }
            Statement::Loop { body, .. }
            | Statement::Rec { body, .. }
            | Statement::Branch { body, .. } => {
                collect_vm_required_capabilities(body, out);
            }
            Statement::Parallel { branches } => {
                for branch in branches {
                    collect_vm_required_capabilities(branch, out);
                }
            }
            Statement::Heartbeat {
                on_missing_body,
                body,
                ..
            } => {
                collect_vm_required_capabilities(on_missing_body, out);
                collect_vm_required_capabilities(body, out);
            }
            Statement::Send { .. }
            | Statement::Broadcast { .. }
            | Statement::Continue { .. }
            | Statement::Handshake { .. }
            | Statement::QuorumCollect { .. }
            | Statement::Call { .. } => {}
        }
    }
}

fn infer_required_proof_bundles(
    explicit_required: &[String],
    proof_bundles: &[ProofBundleDecl],
    statements: &[Statement],
) -> Vec<String> {
    if !explicit_required.is_empty() {
        return Vec::new();
    }
    if proof_bundles.is_empty() {
        return Vec::new();
    }

    let mut required_caps = HashSet::new();
    collect_vm_required_capabilities(statements, &mut required_caps);
    if required_caps.is_empty() {
        return Vec::new();
    }

    let mut selected = Vec::new();
    let mut covered = HashSet::new();
    let mut caps: Vec<_> = required_caps.into_iter().collect();
    caps.sort();

    for cap in caps {
        if covered.contains(&cap) {
            continue;
        }
        let Some(bundle) = proof_bundles
            .iter()
            .find(|bundle| bundle.capabilities.iter().any(|c| c == &cap))
        else {
            return Vec::new();
        };
        if !selected.contains(&bundle.name) {
            selected.push(bundle.name.clone());
        }
        for bundle_cap in &bundle.capabilities {
            covered.insert(bundle_cap.clone());
        }
    }

    selected
}

/// Parse a choreographic protocol from a string
pub fn parse_choreography_str(input: &str) -> std::result::Result<Choreography, ParseError> {
    parse_choreography_str_with_extensions(input, &ExtensionRegistry::new())
        .map(|(choreo, _)| choreo)
}

/// Parse a choreographic protocol from a string with extension support
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
                        // Imports are parsed for completeness but ignored for now.
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
                        let mut proto_inner = inner.into_inner();
                        let name_pair = proto_inner
                            .next()
                            .expect("grammar: protocol_decl must have name");
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
                        let body_pair = body_pair.expect("grammar: protocol_decl must have body");
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
/// The new DSL drops annotation/extension surface syntax for now, so this is a
/// no-op placeholder that keeps the API stable.
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

/// Lint level for parser diagnostics.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LintLevel {
    Off,
    Warn,
    Deny,
}

/// Structured lint diagnostic with optional fix suggestion.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LintDiagnostic {
    pub code: String,
    pub level: LintLevel,
    pub message: String,
    pub suggestion: Option<String>,
}

/// Collect DSL lint diagnostics for a parsed choreography.
pub fn collect_dsl_lints(choreography: &Choreography, level: LintLevel) -> Vec<LintDiagnostic> {
    if level == LintLevel::Off {
        return Vec::new();
    }

    let mut diagnostics = Vec::new();
    let inferred = choreography.inferred_required_proof_bundles();
    let required = choreography.required_proof_bundles();
    if !inferred.is_empty() && inferred == required {
        diagnostics.push(LintDiagnostic {
            code: "dsl.inferred_requires".to_string(),
            level,
            message: "Protocol requirements were inferred from VM-core capabilities".to_string(),
            suggestion: Some(format!(
                "Add explicit `requires {}` to the protocol header",
                inferred.join(", ")
            )),
        });
    }

    diagnostics
}

/// Render lint diagnostics into a lightweight LSP-like JSON string.
pub fn render_lsp_lint_diagnostics(choreography: &Choreography, level: LintLevel) -> String {
    let diagnostics: Vec<serde_json::Value> = collect_dsl_lints(choreography, level)
        .into_iter()
        .map(|lint| {
            serde_json::json!({
                "code": lint.code,
                "severity": match lint.level {
                    LintLevel::Off => "off",
                    LintLevel::Warn => "warning",
                    LintLevel::Deny => "error",
                },
                "message": lint.message,
                "range": {
                    "start": {"line": 0, "character": 0},
                    "end": {"line": 0, "character": 1}
                },
                "data": {
                    "quickFix": lint.suggestion
                }
            })
        })
        .collect();
    serde_json::to_string_pretty(&diagnostics).unwrap_or_else(|_| "[]".to_string())
}

/// Produce a canonical lowering report for a DSL snippet.
pub fn explain_lowering(input: &str) -> std::result::Result<String, ParseError> {
    fn render_protocol(protocol: &Protocol, depth: usize, out: &mut String) {
        let indent = "  ".repeat(depth);
        match protocol {
            Protocol::Send {
                from,
                to,
                message,
                continuation,
                ..
            } => {
                let _ = writeln!(
                    out,
                    "{indent}- send {} -> {} : {}",
                    from.name(),
                    to.name(),
                    message.name
                );
                render_protocol(continuation, depth + 1, out);
            }
            Protocol::Broadcast {
                from,
                message,
                continuation,
                ..
            } => {
                let _ = writeln!(
                    out,
                    "{indent}- broadcast {} ->* : {}",
                    from.name(),
                    message.name
                );
                render_protocol(continuation, depth + 1, out);
            }
            Protocol::Choice { role, branches, .. } => {
                let _ = writeln!(out, "{indent}- choice at {}", role.name());
                for branch in branches {
                    let _ = writeln!(out, "{indent}  branch {}", branch.label);
                    render_protocol(&branch.protocol, depth + 2, out);
                }
            }
            Protocol::Loop { body, .. } => {
                let _ = writeln!(out, "{indent}- loop");
                render_protocol(body, depth + 1, out);
            }
            Protocol::Parallel { protocols } => {
                let _ = writeln!(out, "{indent}- parallel");
                for (idx, branch) in protocols.iter().enumerate() {
                    let _ = writeln!(out, "{indent}  branch#{idx}");
                    render_protocol(branch, depth + 2, out);
                }
            }
            Protocol::Rec { label, body } => {
                let _ = writeln!(out, "{indent}- rec {label}");
                render_protocol(body, depth + 1, out);
            }
            Protocol::Var(label) => {
                let _ = writeln!(out, "{indent}- continue {label}");
            }
            Protocol::Extension {
                annotations,
                continuation,
                ..
            } => {
                let kind = annotations
                    .custom("vm_core_op")
                    .or_else(|| annotations.custom("dsl_combinator"))
                    .unwrap_or("extension");
                let _ = writeln!(out, "{indent}- extension {kind}");
                render_protocol(continuation, depth + 1, out);
            }
            Protocol::End => {
                let _ = writeln!(out, "{indent}- end");
            }
        }
    }

    let choreography = parse_choreography_str(input)?;
    let mut out = String::new();
    let _ = writeln!(out, "Protocol: {}", choreography.qualified_name());
    let _ = writeln!(
        out,
        "Roles: {}",
        choreography
            .roles
            .iter()
            .map(|r| r.name().to_string())
            .collect::<Vec<_>>()
            .join(", ")
    );
    let bundles = choreography.proof_bundles();
    if !bundles.is_empty() {
        let _ = writeln!(
            out,
            "Proof bundles: {}",
            bundles
                .iter()
                .map(|b| b.name.clone())
                .collect::<Vec<_>>()
                .join(", ")
        );
    }
    let required = choreography.required_proof_bundles();
    if !required.is_empty() {
        let _ = writeln!(out, "Required bundles: {}", required.join(", "));
    }
    let inferred = choreography.inferred_required_proof_bundles();
    if !inferred.is_empty() {
        let _ = writeln!(out, "Inferred bundles: {}", inferred.join(", "));
    }
    let _ = writeln!(out, "Lowering:");
    render_protocol(&choreography.protocol, 1, &mut out);

    let lints = collect_dsl_lints(&choreography, LintLevel::Warn);
    if !lints.is_empty() {
        let _ = writeln!(out, "Lints:");
        for lint in lints {
            let _ = writeln!(out, "- [{}] {}", lint.code, lint.message);
            if let Some(fix) = lint.suggestion {
                let _ = writeln!(out, "  fix: {fix}");
            }
        }
    }

    Ok(out)
}

// Example of how the macro would work
#[doc(hidden)]
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
  case choose Seller of
    accept ->
      Seller -> Buyer : Accept
    reject ->
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
  choice at A
    ok ->
      A -> B : Ack
    fail ->
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
        //       choice at Client {
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
    Client -> Server : Request<String>
    Server -> Client : Response<u32>
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
                                // Type annotation should be preserved
                                assert!(message.type_annotation.is_some());
                                let type_str =
                                    message.type_annotation.as_ref().unwrap().to_string();
                                assert!(
                                    type_str.contains("String"),
                                    "Expected String type, got: {}",
                                    type_str
                                );

                                match continuation.as_ref() {
                                    Protocol::Send { message, .. } => {
                                        assert_eq!(message.name.to_string(), "Response");
                                        assert!(message.type_annotation.is_some());
                                        let type_str =
                                            message.type_annotation.as_ref().unwrap().to_string();
                                        assert!(
                                            type_str.contains("u32"),
                                            "Expected u32 type, got: {}",
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
    choice at A
      opt1 ->
        A -> B : Msg1
      opt2 ->
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
  branch
    A -> B : Msg1
  branch
    C -> D : Msg2
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
  branch
    A -> B : Msg
"#;

        let result = parse_choreography_str(input);
        assert!(result.is_err());
        let err = result.unwrap_err();
        let err_str = err.to_string();
        assert!(err_str.contains("parallel requires at least two adjacent branch blocks"));
    }

    #[test]
    fn test_parse_timed_choice() {
        let input = r#"
protocol TimedRequest =
  roles Alice, Bob
  Alice -> Bob : Request
  timed_choice at Alice(5s) {
    OnTime -> {
      Bob -> Alice : Response
    }
    TimedOut -> {
      Alice -> Bob : Cancel
    }
  }
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse timed_choice: {:?}",
            result.err()
        );

        let choreo = result.unwrap();
        assert_eq!(choreo.name.to_string(), "TimedRequest");

        // Verify timed_choice is desugared to Choice with typed annotation
        match &choreo.protocol {
            Protocol::Send { continuation, .. } => {
                match continuation.as_ref() {
                    Protocol::Choice {
                        role,
                        branches,
                        annotations,
                    } => {
                        assert_eq!(role.name().to_string(), "Alice");
                        assert_eq!(branches.len(), 2);
                        // Check that timed_choice annotation is present
                        assert!(annotations.has_timed_choice());
                        assert_eq!(
                            annotations.timed_choice(),
                            Some(std::time::Duration::from_secs(5))
                        );
                    }
                    _ => panic!("Expected Choice after Send"),
                }
            }
            _ => panic!("Expected Send as first protocol"),
        }
    }

    #[test]
    fn test_parse_timed_choice_milliseconds() {
        let input = r#"
protocol QuickTimeout =
  roles Client, Server
  timed_choice at Client(500ms) {
    Fast -> {
      Server -> Client : Data
    }
    Slow -> {
      Client -> Server : Abort
    }
  }
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse timed_choice with ms: {:?}",
            result.err()
        );

        let choreo = result.unwrap();
        match &choreo.protocol {
            Protocol::Choice { annotations, .. } => {
                assert!(annotations.has_timed_choice());
                assert_eq!(
                    annotations.timed_choice(),
                    Some(std::time::Duration::from_millis(500))
                );
            }
            _ => panic!("Expected Choice as first protocol"),
        }
    }

    #[test]
    fn test_parse_timed_choice_minutes() {
        let input = r#"
protocol LongTimeout =
  roles A, B
  timed_choice at A(2m) {
    Done -> {
      B -> A : Complete
    }
    Expired -> {
      A -> B : Timeout
    }
  }
"#;

        let result = parse_choreography_str(input);
        assert!(result.is_ok(), "Failed to parse: {:?}", result.err());

        let choreo = result.unwrap();
        match &choreo.protocol {
            Protocol::Choice { annotations, .. } => {
                // 2 minutes = 120000 ms
                assert!(annotations.has_timed_choice());
                assert_eq!(
                    annotations.timed_choice(),
                    Some(std::time::Duration::from_millis(120000))
                );
            }
            _ => panic!("Expected Choice"),
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

                // Inside: Sender -> Receiver: Heartbeat; choice at Receiver { ... }
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
  @runtime_timeout(5s) Client -> Server : Request
  Server -> Client : Response
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse @runtime_timeout: {:?}",
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
    fn test_parse_runtime_timeout_milliseconds() {
        let input = r#"
protocol QuickCheck =
  roles A, B
  @runtime_timeout(100ms) A -> B : Ping
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse @runtime_timeout with ms: {:?}",
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
  @parallel Coordinator -> Worker : Task
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse @parallel: {:?}",
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
    fn test_parse_ordered_annotation() {
        let input = r#"
protocol OrderedCollect =
  roles Coordinator, Worker
  @ordered Worker -> Coordinator : Result
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse @ordered: {:?}",
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

    #[test]
    fn test_parse_min_responses_annotation() {
        let input = r#"
protocol ThresholdSign =
  roles Coordinator, Signer
  @min_responses(3) Signer -> Coordinator : Signature
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse @min_responses: {:?}",
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
    fn test_parse_combined_annotations() {
        let input = r#"
protocol ParallelThreshold =
  roles Coordinator, Worker
  @parallel @min_responses(2) Worker -> Coordinator : Vote
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse combined annotations: {:?}",
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
                Protocol::Send { continuation, .. } | Protocol::Broadcast { continuation, .. } => {
                    collect_vm_ops(continuation, out);
                }
                Protocol::Choice { branches, .. } => {
                    for branch in branches {
                        collect_vm_ops(&branch.protocol, out);
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
  choice at A
    ok when (count + 1) ->
      A -> B : Ack
    no ->
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
  choice at A
    consume ->
      release guard using token
    keep ->
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
                Protocol::Send { continuation, .. } | Protocol::Broadcast { continuation, .. } => {
                    has_quorum_extension(continuation)
                }
                Protocol::Choice { branches, .. } => {
                    branches.iter().any(|b| has_quorum_extension(&b.protocol))
                }
                Protocol::Loop { body, .. } | Protocol::Rec { body, .. } => {
                    has_quorum_extension(body)
                }
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
  choice at A
    ok when (if ready { true } else { false }) ->
      A -> B : Accept
    no ->
      A -> B : Reject
"#;

        let err = parse_choreography_str(input).expect_err("parse should fail");
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
}
