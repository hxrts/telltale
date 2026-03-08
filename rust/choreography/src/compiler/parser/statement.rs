//! Statement parsing functions.
//!
//! This module handles parsing of all statement types in the choreography DSL,
//! including send, broadcast, choice, loop, parallel composition, recursion, and more.

use crate::ast::Role;
use proc_macro2::TokenStream;
use quote::format_ident;
use std::collections::{HashMap, HashSet};

use super::error::{ErrorSpan, ParseError};
use super::stmt_parsers::{
    parse_broadcast_stmt, parse_call_stmt, parse_choice_stmt, parse_continue_stmt,
    parse_handshake_stmt, parse_heartbeat_stmt, parse_loop_stmt, parse_par_stmt,
    parse_quorum_collect_stmt, parse_rec_stmt, parse_retry_stmt, parse_send_stmt,
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

/// Parse a single statement
pub(crate) fn parse_statement(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
    protocol_defs: &HashMap<String, Vec<Statement>>,
) -> std::result::Result<Statement, ParseError> {
    parse_statement_inner(pair, declared_roles, input, protocol_defs)
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
        Rule::par_stmt => parse_par_stmt(pair, declared_roles, input, protocol_defs),
        Rule::loop_stmt => parse_loop_stmt(pair, declared_roles, input, protocol_defs),
        Rule::rec_stmt => parse_rec_stmt(pair, declared_roles, input, protocol_defs),
        Rule::continue_stmt => parse_continue_stmt(pair, input),
        Rule::call_stmt => parse_call_stmt(pair, input),
        Rule::handshake_stmt => parse_handshake_stmt(pair, declared_roles, input),
        Rule::retry_stmt => parse_retry_stmt(pair, declared_roles, input, protocol_defs),
        Rule::quorum_collect_stmt => parse_quorum_collect_stmt(pair, declared_roles, input),
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
    input: &str,
) -> std::result::Result<MessageSpec, ParseError> {
    fn normalize_dsl_type_source(src: &str) -> String {
        src.replace('.', " :: ")
    }

    let span = pair.as_span();
    let mut inner = pair.into_inner();

    let name = format_ident!(
        "{}",
        inner
            .next()
            .ok_or_else(|| ParseError::Syntax {
                span: ErrorSpan::from_pest_span(span, input),
                message: "message is missing a name".to_string(),
            })?
            .as_str()
    );

    let type_annotation = None;
    let mut payload = None;

    for part in inner {
        match part.as_rule() {
            Rule::message_of => {
                let payload_type = part
                    .into_inner()
                    .next()
                    .ok_or_else(|| ParseError::Syntax {
                        span: ErrorSpan::from_pest_span(span, input),
                        message: "message `of` clause is missing a type".to_string(),
                    })?
                    .as_str()
                    .to_string();
                let payload_type = normalize_dsl_type_source(&payload_type);
                payload = syn::parse_str::<TokenStream>(&payload_type).ok();
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
    let span = pair.as_span();
    let mut inner = pair.into_inner();
    let name_pair = inner.next().ok_or_else(|| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "local protocol declaration is missing a name".to_string(),
    })?;
    let proto_name = name_pair.as_str().to_string();
    let name_span = name_pair.as_span();

    if protocol_defs.contains_key(&proto_name) {
        return Err(ParseError::DuplicateProtocol {
            protocol: proto_name,
            span: ErrorSpan::from_pest_span(name_span, input),
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
        body_pair.ok_or_else(|| ParseError::Syntax {
            span: ErrorSpan::from_pest_span(span, input),
            message: "local protocol declaration is missing a body".to_string(),
        })?,
        declared_roles,
        input,
        protocol_defs,
        false,
    )?;

    if roles.is_some() {
        return Err(ParseError::Syntax {
            span: ErrorSpan::from_pest_span(name_span, input),
            message: "local protocols cannot declare roles".to_string(),
        });
    }

    protocol_defs.insert(proto_name, statements);
    Ok(())
}
