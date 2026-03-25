use super::super::error::{ErrorSpan, ParseError};
use super::super::statement::parse_block;
use super::super::types::Statement;
use super::super::Rule;
use quote::format_ident;
use std::collections::{HashMap, HashSet};

/// Parse recursive statement
pub(crate) fn parse_rec_stmt(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
    protocol_defs: &HashMap<String, Vec<Statement>>,
) -> std::result::Result<Statement, ParseError> {
    let span = pair.as_span();
    let mut inner = pair.into_inner();

    let label_pair = inner.next().ok_or_else(|| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "rec statement is missing a label".to_string(),
    })?;
    let label = format_ident!("{}", label_pair.as_str());
    let body = parse_block(
        inner.next().ok_or_else(|| ParseError::Syntax {
            span: ErrorSpan::from_pest_span(span, input),
            message: "rec statement is missing a body".to_string(),
        })?,
        declared_roles,
        input,
        protocol_defs,
    )?;

    Ok(Statement::Rec { label, body })
}

/// Parse protocol call statement
pub(crate) fn parse_call_stmt(
    pair: pest::iterators::Pair<Rule>,
    input: &str,
) -> std::result::Result<Statement, ParseError> {
    let span = pair.as_span();
    let mut inner = pair.into_inner();
    let proto_name_pair = inner.next().ok_or_else(|| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "call statement is missing protocol name".to_string(),
    })?;
    let proto_name = proto_name_pair.as_str();

    Ok(Statement::Call {
        name: format_ident!("{}", proto_name),
    })
}

/// Parse continue statement (recursive back-reference)
pub(crate) fn parse_continue_stmt(
    pair: pest::iterators::Pair<Rule>,
    input: &str,
) -> std::result::Result<Statement, ParseError> {
    let span = pair.as_span();
    let mut inner = pair.into_inner();
    let label_pair = inner.next().ok_or_else(|| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "continue statement is missing label".to_string(),
    })?;
    let label = label_pair.as_str();

    Ok(Statement::Continue {
        label: format_ident!("{}", label),
    })
}
