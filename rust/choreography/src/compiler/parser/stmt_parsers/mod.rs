//! Individual statement parsers.
//!
//! This module contains parsers for each statement type in the choreography DSL.

use crate::ast::Role;
use proc_macro2::TokenStream;
use std::collections::{HashMap, HashSet};

use super::error::{ErrorSpan, ParseError};
use super::role::parse_role_ref;
use super::types::PredicateExpr;
use super::Rule;

mod branching;
mod control_flow;
mod looping;
mod send;
mod vm;
pub(crate) use branching::{parse_choice_stmt, parse_par_stmt, parse_timed_choice_stmt};
pub(super) use control_flow::{
    parse_call_stmt, parse_continue_stmt, parse_handshake_stmt, parse_quorum_collect_stmt,
    parse_rec_stmt, parse_retry_stmt,
};
pub(crate) use looping::{parse_heartbeat_stmt, parse_loop_stmt};
pub(crate) use send::{parse_broadcast_stmt, parse_send_stmt};
pub(super) use vm::{
    parse_vm_abort_stmt, parse_vm_acquire_stmt, parse_vm_check_stmt, parse_vm_fork_stmt,
    parse_vm_join_stmt, parse_vm_release_stmt, parse_vm_tag_stmt, parse_vm_transfer_stmt,
};

fn syntax_error(span: pest::Span<'_>, input: &str, message: impl Into<String>) -> ParseError {
    ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: message.into(),
    }
}

fn parse_role_annotation_value(pair: pest::iterators::Pair<Rule>) -> String {
    let value_pair = if pair.as_rule() == Rule::role_annotation_value {
        pair.into_inner().next()
    } else {
        Some(pair)
    };

    match value_pair.map(|p| (p.as_rule(), p.as_str().to_string())) {
        Some((Rule::string, raw)) => raw
            .strip_prefix('"')
            .and_then(|s| s.strip_suffix('"'))
            .unwrap_or(&raw)
            .to_string(),
        Some((Rule::duration, raw)) => raw.trim().to_string(),
        Some((_, raw)) => raw.trim().to_string(),
        None => String::new(),
    }
}

fn parse_role_annotation_block(
    pair: pest::iterators::Pair<Rule>,
    input: &str,
) -> std::result::Result<HashMap<String, String>, ParseError> {
    let mut annotations = HashMap::new();

    for item in pair.into_inner() {
        if item.as_rule() != Rule::role_annotation_entries {
            continue;
        }

        for entry in item.into_inner() {
            if entry.as_rule() != Rule::role_annotation_entry {
                continue;
            }

            let entry_span = entry.as_span();
            let mut parts = entry.into_inner();
            let key = next_required(
                &mut parts,
                entry_span,
                input,
                "role annotation entry is missing a key",
            )?
            .as_str()
            .to_string();
            let value_pair = next_required(
                &mut parts,
                entry_span,
                input,
                "role annotation entry is missing a value",
            )?;
            let value = parse_role_annotation_value(value_pair);
            annotations.insert(key, value);
        }
    }

    Ok(annotations)
}

fn is_statement_annotation_key(key: &str) -> bool {
    matches!(
        key,
        "runtime_timeout"
            | "parallel"
            | "ordered"
            | "min_responses"
            | "retry"
            | "idempotent"
            | "trace"
    )
}

fn extract_statement_annotations(
    annotations: &HashMap<String, String>,
) -> HashMap<String, String> {
    annotations
        .iter()
        .filter(|(key, _)| is_statement_annotation_key(key))
        .map(|(key, value)| (key.clone(), value.clone()))
        .collect()
}

fn parse_annotated_sender_ref(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
) -> std::result::Result<(Role, HashMap<String, String>), ParseError> {
    let span = pair.as_span();
    let mut role: Option<Role> = None;
    let mut annotations = HashMap::new();

    for item in pair.into_inner() {
        match item.as_rule() {
            Rule::role_ref => {
                role = Some(parse_role_ref(item, declared_roles, input)?);
            }
            Rule::role_metadata_record => {
                annotations = parse_role_annotation_block(item, input)?;
            }
            _ => {}
        }
    }

    let role =
        role.ok_or_else(|| syntax_error(span, input, "send is missing sender role".to_string()))?;

    Ok((role, annotations))
}

fn next_required<'i>(
    pairs: &mut pest::iterators::Pairs<'i, Rule>,
    span: pest::Span<'i>,
    input: &str,
    message: &str,
) -> std::result::Result<pest::iterators::Pair<'i, Rule>, ParseError> {
    pairs
        .next()
        .ok_or_else(|| syntax_error(span, input, message.to_string()))
}

fn parse_guard_predicate(
    expr_src: &str,
    span: pest::Span,
    input: &str,
) -> std::result::Result<TokenStream, ParseError> {
    let predicate = PredicateExpr::parse(expr_src).map_err(|e| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: format!("Invalid guard expression: {e}"),
    })?;
    Ok(predicate.to_token_stream())
}

fn parse_loop_predicate(
    expr_src: &str,
    span: pest::Span,
    input: &str,
) -> std::result::Result<TokenStream, ParseError> {
    let predicate = PredicateExpr::parse(expr_src).map_err(|e| ParseError::InvalidCondition {
        message: format!("Invalid loop condition: {e}"),
        span: ErrorSpan::from_pest_span(span, input),
    })?;
    Ok(predicate.to_token_stream())
}

#[cfg(test)]
mod tests {
    use super::*;
    use pest::Parser;

    use super::super::ChoreographyParser;

    #[test]
    fn parse_send_stmt_handles_malformed_pair_without_panicking() {
        let pair = ChoreographyParser::parse(Rule::role_ref, "A")
            .expect("parse role_ref")
            .next()
            .expect("role_ref pair");
        let mut declared = HashSet::new();
        declared.insert("A".to_string());
        declared.insert("B".to_string());
        let parsed = parse_send_stmt(pair, &declared, "A");
        assert!(parsed.is_err());
    }

    #[test]
    fn parse_broadcast_stmt_handles_malformed_pair_without_panicking() {
        let pair = ChoreographyParser::parse(Rule::role_ref, "A")
            .expect("parse role_ref")
            .next()
            .expect("role_ref pair");
        let mut declared = HashSet::new();
        declared.insert("A".to_string());
        let parsed = parse_broadcast_stmt(pair, &declared, "A");
        assert!(parsed.is_err());
    }
}
