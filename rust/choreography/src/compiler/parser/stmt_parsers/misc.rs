use super::super::error::{ErrorSpan, ParseError};
use super::super::role::parse_role_ref;
use super::super::statement::parse_block;
use super::super::types::Statement;
use super::super::Rule;
use crate::ast::Condition;
use proc_macro2::TokenStream;
use quote::format_ident;
use std::collections::{HashMap, HashSet};

/// Parse recursive statement
pub(crate) fn parse_rec_stmt(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
    protocol_defs: &HashMap<String, Vec<Statement>>,
) -> std::result::Result<Statement, ParseError> {
    let mut inner = pair.into_inner();

    let label = format_ident!(
        "{}",
        inner
            .next()
            .expect("grammar: rec_stmt must have label")
            .as_str()
    );
    let body = parse_block(
        inner.next().expect("grammar: rec_stmt must have body"),
        declared_roles,
        input,
        protocol_defs,
    )?;

    Ok(Statement::Rec { label, body })
}

/// Parse protocol call statement
pub(crate) fn parse_call_stmt(
    pair: pest::iterators::Pair<Rule>,
) -> std::result::Result<Statement, ParseError> {
    let mut inner = pair.into_inner();
    let proto_name_pair = inner
        .next()
        .expect("grammar: call_stmt must have protocol name");
    let proto_name = proto_name_pair.as_str();

    Ok(Statement::Call {
        name: format_ident!("{}", proto_name),
    })
}

pub(crate) fn parse_handshake_stmt(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
) -> std::result::Result<Statement, ParseError> {
    let span = pair.as_span();
    let mut inner = pair.into_inner();
    let initiator_pair = inner.next().ok_or_else(|| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "handshake is missing initiator role".to_string(),
    })?;
    let responder_pair = inner.next().ok_or_else(|| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "handshake is missing responder role".to_string(),
    })?;
    let label_pair = inner.next().ok_or_else(|| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "handshake is missing label".to_string(),
    })?;
    Ok(Statement::Handshake {
        initiator: parse_role_ref(initiator_pair, declared_roles, input)?,
        responder: parse_role_ref(responder_pair, declared_roles, input)?,
        label: format_ident!("{}", label_pair.as_str()),
    })
}

pub(crate) fn parse_retry_stmt(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
    protocol_defs: &HashMap<String, Vec<Statement>>,
) -> std::result::Result<Statement, ParseError> {
    let span = pair.as_span();
    let mut inner = pair.into_inner();
    let count_pair = inner.next().ok_or_else(|| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "retry is missing iteration count".to_string(),
    })?;
    let block_pair = inner.next().ok_or_else(|| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "retry is missing block body".to_string(),
    })?;
    let count_src = count_pair.as_str();
    let condition = if let Ok(count) = count_src.parse::<usize>() {
        Condition::Count(count)
    } else {
        Condition::Custom(syn::parse_str::<TokenStream>(count_src).map_err(|e| {
            ParseError::InvalidCondition {
                message: format!("Invalid retry count: {e}"),
                span: ErrorSpan::from_pest_span(span, input),
            }
        })?)
    };
    let body = parse_block(block_pair, declared_roles, input, protocol_defs)?;
    Ok(Statement::Loop {
        condition: Some(condition),
        body,
    })
}

pub(crate) fn parse_quorum_collect_stmt(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
) -> std::result::Result<Statement, ParseError> {
    let span = pair.as_span();
    let mut inner = pair.into_inner();
    let source_pair = inner.next().ok_or_else(|| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "quorum_collect is missing source role".to_string(),
    })?;
    let destination_pair = inner.next().ok_or_else(|| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "quorum_collect is missing destination role".to_string(),
    })?;
    let min_pair = inner.next().ok_or_else(|| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "quorum_collect is missing min count".to_string(),
    })?;
    let message_pair = inner.next().ok_or_else(|| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "quorum_collect is missing message".to_string(),
    })?;
    let min_responses = min_pair
        .as_str()
        .parse::<u32>()
        .map_err(|_| ParseError::Syntax {
            span: ErrorSpan::from_pest_span(span, input),
            message: "quorum_collect min count must be an integer".to_string(),
        })?;
    Ok(Statement::QuorumCollect {
        source: parse_role_ref(source_pair, declared_roles, input)?,
        destination: parse_role_ref(destination_pair, declared_roles, input)?,
        min_responses,
        message: super::super::statement::parse_message(message_pair, input)?,
    })
}

/// Parse continue statement (recursive back-reference)
pub(crate) fn parse_continue_stmt(
    pair: pest::iterators::Pair<Rule>,
) -> std::result::Result<Statement, ParseError> {
    let mut inner = pair.into_inner();
    let label_pair = inner
        .next()
        .expect("grammar: continue_stmt must have label");
    let label = label_pair.as_str();

    Ok(Statement::Continue {
        label: format_ident!("{}", label),
    })
}
