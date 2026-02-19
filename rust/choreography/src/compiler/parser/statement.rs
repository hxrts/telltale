//! Statement parsing functions.
//!
//! This module handles parsing of all statement types in the choreography DSL,
//! including send, broadcast, choice, loop, branch, recursion, and more.

use crate::ast::Role;
use proc_macro2::TokenStream;
use quote::format_ident;
use std::collections::{HashMap, HashSet};

use super::error::{ErrorSpan, ParseError};
use super::stmt_parsers::{
    parse_branch_stmt, parse_broadcast_stmt, parse_call_stmt, parse_choice_stmt,
    parse_continue_stmt, parse_heartbeat_stmt, parse_loop_stmt, parse_rec_stmt, parse_send_stmt,
    parse_timed_choice_stmt, parse_vm_abort_stmt, parse_vm_acquire_stmt, parse_vm_check_stmt,
    parse_vm_fork_stmt, parse_vm_join_stmt, parse_vm_release_stmt, parse_vm_tag_stmt,
    parse_vm_transfer_stmt,
};
use super::types::{MessageSpec, ParsedBody, Statement};
use super::Rule;

/// Parse protocol body into statements
pub(crate) fn parse_protocol_body(
    pair: pest::iterators::Pair<Rule>,
    declared_roles_base: &HashSet<String>,
    input: &str,
    protocol_defs: &HashMap<String, Vec<Statement>>,
    allow_roles_decl: bool,
) -> std::result::Result<ParsedBody, ParseError> {
    use super::role::parse_roles_from_pair;

    let mut roles: Option<Vec<Role>> = None;
    let mut statements = Vec::new();
    let mut declared_roles = declared_roles_base.clone();

    let mut inner_pairs: Vec<pest::iterators::Pair<Rule>> = Vec::new();
    match pair.as_rule() {
        Rule::protocol_body => {
            if let Some(inner) = pair.into_inner().next() {
                inner_pairs = inner.into_inner().collect();
            }
        }
        Rule::block_protocol | Rule::block => {
            inner_pairs = pair.into_inner().collect();
        }
        _ => {
            inner_pairs = pair.into_inner().collect();
        }
    }

    for item in inner_pairs {
        match item.as_rule() {
            Rule::roles_decl => {
                if !allow_roles_decl {
                    return Err(ParseError::Syntax {
                        span: ErrorSpan::from_pest_span(item.as_span(), input),
                        message: "roles declaration is not allowed here".to_string(),
                    });
                }
                if roles.is_some() {
                    return Err(ParseError::Syntax {
                        span: ErrorSpan::from_pest_span(item.as_span(), input),
                        message: "duplicate roles declaration".to_string(),
                    });
                }
                let parsed_roles = parse_roles_from_pair(item, input)?;
                declared_roles = parsed_roles.iter().map(|r| r.name().to_string()).collect();
                roles = Some(parsed_roles);
            }
            _ => {
                let statement = parse_statement(item, &declared_roles, input, protocol_defs)?;
                statements.push(statement);
            }
        }
    }

    let statements = normalize_branches_to_parallel(statements, input)?;
    Ok(ParsedBody { roles, statements })
}

/// Parse a block of statements
pub(crate) fn parse_block(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
    protocol_defs: &HashMap<String, Vec<Statement>>,
) -> std::result::Result<Vec<Statement>, ParseError> {
    let span = pair.as_span();
    let ParsedBody { roles, statements } =
        parse_protocol_body(pair, declared_roles, input, protocol_defs, false)?;
    if roles.is_some() {
        return Err(ParseError::Syntax {
            span: ErrorSpan::from_pest_span(span, input),
            message: "roles declaration is not allowed in this block".to_string(),
        });
    }
    Ok(statements)
}

/// Normalize consecutive Branch statements into Parallel statements
pub(crate) fn normalize_branches_to_parallel(
    statements: Vec<Statement>,
    input: &str,
) -> std::result::Result<Vec<Statement>, ParseError> {
    let mut result = Vec::new();
    let mut i = 0usize;

    while i < statements.len() {
        match &statements[i] {
            Statement::Branch { .. } => {
                let mut branches = Vec::new();
                let mut span = None;
                while i < statements.len() {
                    if let Statement::Branch { body, span: s } = &statements[i] {
                        if span.is_none() {
                            span = Some(s.clone());
                        }
                        branches.push(body.clone());
                        i += 1;
                    } else {
                        break;
                    }
                }

                if branches.len() < 2 {
                    let err_span = span.unwrap_or_else(|| ErrorSpan::from_line_col(1, 1, input));
                    return Err(ParseError::Syntax {
                        span: err_span,
                        message: "parallel requires at least two adjacent branch blocks"
                            .to_string(),
                    });
                }

                result.push(Statement::Parallel { branches });
            }
            _ => {
                result.push(statements[i].clone());
                i += 1;
            }
        }
    }

    Ok(result)
}

/// Parse a single statement
pub(crate) fn parse_statement(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
    protocol_defs: &HashMap<String, Vec<Statement>>,
) -> std::result::Result<Statement, ParseError> {
    match pair.as_rule() {
        Rule::annotated_stmt => parse_annotated_stmt(pair, declared_roles, input, protocol_defs),
        _ => parse_statement_inner(pair, declared_roles, input, protocol_defs),
    }
}

/// Parse an annotated statement (e.g., @runtime_timeout(5s) Alice -> Bob: Msg)
fn parse_annotated_stmt(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
    protocol_defs: &HashMap<String, Vec<Statement>>,
) -> std::result::Result<Statement, ParseError> {
    let inner = pair.into_inner();
    let mut annotations: HashMap<String, String> = HashMap::new();

    // Parse all annotations
    for item in inner {
        match item.as_rule() {
            Rule::annotation => {
                let annotation_kind = item
                    .into_inner()
                    .next()
                    .expect("grammar: annotation must have kind");
                parse_annotation_kind(annotation_kind, &mut annotations, input)?;
            }
            _ => {
                // This should be the inner statement
                let mut stmt = parse_statement_inner(item, declared_roles, input, protocol_defs)?;
                // Apply collected annotations to the statement
                apply_annotations_to_statement(&mut stmt, annotations);
                return Ok(stmt);
            }
        }
    }

    // This shouldn't happen if grammar is correct
    Err(ParseError::Syntax {
        span: ErrorSpan::from_line_col(1, 1, input),
        message: "Annotated statement missing inner statement".to_string(),
    })
}

/// Parse an annotation kind and add to annotations map
fn parse_annotation_kind(
    pair: pest::iterators::Pair<Rule>,
    annotations: &mut HashMap<String, String>,
    input: &str,
) -> std::result::Result<(), ParseError> {
    let mut inner = pair.into_inner();
    if let Some(kind) = inner.next() {
        match kind.as_rule() {
            Rule::runtime_timeout_annotation => {
                // Parse @runtime_timeout(duration)
                let duration_pair = kind
                    .into_inner()
                    .next()
                    .expect("grammar: runtime_timeout must have duration");
                let duration_ms = parse_duration(duration_pair, input)?;
                annotations.insert("runtime_timeout".to_string(), duration_ms.to_string());
            }
            Rule::custom_annotation => {
                // Parse @custom_name(args)
                let mut custom_inner = kind.into_inner();
                if let Some(name_pair) = custom_inner.next() {
                    let name = name_pair.as_str().to_string();
                    let value = custom_inner
                        .next()
                        .map(|p| p.as_str().to_string())
                        .unwrap_or_default();
                    annotations.insert(name, value);
                }
            }
            _ => {}
        }
    }
    Ok(())
}

/// Apply parsed annotations to a statement
fn apply_annotations_to_statement(stmt: &mut Statement, annotations: HashMap<String, String>) {
    if annotations.is_empty() {
        return;
    }

    match stmt {
        Statement::Send {
            annotations: stmt_annotations,
            ..
        } => {
            stmt_annotations.extend(annotations);
        }
        Statement::Broadcast {
            annotations: stmt_annotations,
            ..
        } => {
            stmt_annotations.extend(annotations);
        }
        Statement::Choice {
            annotations: stmt_annotations,
            ..
        } => {
            stmt_annotations.extend(annotations);
        }
        // For statements without annotations field, we could wrap or extend
        // For now, these don't support annotations
        _ => {
            // Could log a warning here about unsupported annotation target
        }
    }
}

/// Parse the actual statement (without annotations)
fn parse_statement_inner(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
    protocol_defs: &HashMap<String, Vec<Statement>>,
) -> std::result::Result<Statement, ParseError> {
    match pair.as_rule() {
        Rule::send_stmt => parse_send_stmt(pair, declared_roles, input),
        Rule::broadcast_stmt => parse_broadcast_stmt(pair, declared_roles, input),
        Rule::heartbeat_stmt => parse_heartbeat_stmt(pair, declared_roles, input, protocol_defs),
        Rule::timed_choice_stmt => {
            parse_timed_choice_stmt(pair, declared_roles, input, protocol_defs)
        }
        Rule::choice_stmt => parse_choice_stmt(pair, declared_roles, input, protocol_defs),
        Rule::loop_stmt => parse_loop_stmt(pair, declared_roles, input, protocol_defs),
        Rule::branch_stmt => parse_branch_stmt(pair, declared_roles, input, protocol_defs),
        Rule::rec_stmt => parse_rec_stmt(pair, declared_roles, input, protocol_defs),
        Rule::continue_stmt => parse_continue_stmt(pair),
        Rule::call_stmt => parse_call_stmt(pair),
        Rule::vm_acquire_stmt => parse_vm_acquire_stmt(pair, input),
        Rule::vm_release_stmt => parse_vm_release_stmt(pair, input),
        Rule::vm_fork_stmt => parse_vm_fork_stmt(pair, input),
        Rule::vm_join_stmt => parse_vm_join_stmt(),
        Rule::vm_abort_stmt => parse_vm_abort_stmt(),
        Rule::vm_transfer_stmt => parse_vm_transfer_stmt(pair, input),
        Rule::vm_tag_stmt => parse_vm_tag_stmt(pair, input),
        Rule::vm_check_stmt => parse_vm_check_stmt(pair, declared_roles, input),
        _ => {
            let span = pair.as_span();
            Err(ParseError::Syntax {
                span: ErrorSpan::from_pest_span(span, input),
                message: format!("Unexpected statement type: {:?}", pair.as_rule()),
            })
        }
    }
}

/// Parse a duration specification (e.g., "5s", "100ms", "2m")
pub(crate) fn parse_duration(
    pair: pest::iterators::Pair<Rule>,
    input: &str,
) -> std::result::Result<u64, ParseError> {
    let span = pair.as_span();
    let mut value: Option<u64> = None;
    let mut unit: Option<&str> = None;

    for item in pair.into_inner() {
        match item.as_rule() {
            Rule::integer => {
                value = Some(item.as_str().parse().map_err(|_| ParseError::Syntax {
                    span: ErrorSpan::from_pest_span(span, input),
                    message: "Invalid duration value".to_string(),
                })?);
            }
            Rule::time_unit => {
                unit = Some(item.as_str());
            }
            _ => {}
        }
    }

    let value = value.ok_or_else(|| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "Duration missing numeric value".to_string(),
    })?;

    let unit = unit.ok_or_else(|| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "Duration missing time unit (ms, s, m, h)".to_string(),
    })?;

    // Convert to milliseconds
    let ms = match unit {
        "ms" => value,
        "s" => value.saturating_mul(1000),
        "m" => value.saturating_mul(60_000),
        "h" => value.saturating_mul(3_600_000),
        _ => {
            return Err(ParseError::Syntax {
                span: ErrorSpan::from_pest_span(span, input),
                message: format!("Unknown time unit: {}", unit),
            })
        }
    };

    Ok(ms)
}

/// Parse message specification
pub(crate) fn parse_message(
    pair: pest::iterators::Pair<Rule>,
    _input: &str,
) -> std::result::Result<MessageSpec, ParseError> {
    let _span = pair.as_span();
    let mut inner = pair.into_inner();

    let name = format_ident!(
        "{}",
        inner
            .next()
            .expect("grammar: message must have name")
            .as_str()
    );

    let mut type_annotation = None;
    let mut payload = None;

    for part in inner {
        match part.as_rule() {
            Rule::message_type => {
                // Parse the type annotation
                let type_str = part.as_str();
                // Remove angle brackets
                let type_str = type_str.trim_start_matches('<').trim_end_matches('>');
                type_annotation = syn::parse_str::<TokenStream>(type_str).ok();
            }
            Rule::payload => {
                // Parse the payload
                let payload_str = part.as_str();
                payload = syn::parse_str::<TokenStream>(payload_str).ok();
            }
            _ => {}
        }
    }

    Ok(MessageSpec {
        name,
        type_annotation,
        payload,
    })
}

/// Parse a local protocol declaration in a where block
pub(crate) fn parse_local_protocol_decl(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
    protocol_defs: &mut HashMap<String, Vec<Statement>>,
) -> std::result::Result<(), ParseError> {
    let mut inner = pair.into_inner();
    let name_pair = inner
        .next()
        .expect("grammar: local_protocol_decl must have name");
    let proto_name = name_pair.as_str().to_string();
    let span = name_pair.as_span();

    if protocol_defs.contains_key(&proto_name) {
        return Err(ParseError::DuplicateProtocol {
            protocol: proto_name,
            span: ErrorSpan::from_pest_span(span, input),
        });
    }

    let mut body_pair: Option<pest::iterators::Pair<Rule>> = None;
    for item in inner {
        match item.as_rule() {
            Rule::header_roles => {
                return Err(ParseError::Syntax {
                    span: ErrorSpan::from_pest_span(item.as_span(), input),
                    message: "local protocols cannot declare roles".to_string(),
                });
            }
            Rule::protocol_body => body_pair = Some(item),
            _ => {}
        }
    }

    let ParsedBody { roles, statements } = parse_protocol_body(
        body_pair.expect("grammar: local_protocol_decl must have body"),
        declared_roles,
        input,
        protocol_defs,
        false,
    )?;

    if roles.is_some() {
        return Err(ParseError::Syntax {
            span: ErrorSpan::from_pest_span(span, input),
            message: "local protocols cannot declare roles".to_string(),
        });
    }

    protocol_defs.insert(proto_name, statements);
    Ok(())
}
