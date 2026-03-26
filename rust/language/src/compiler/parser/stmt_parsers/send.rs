use std::collections::{HashMap, HashSet};

use super::super::role::parse_role_ref;
use super::super::statement::parse_message;
use super::super::types::Statement;
use super::super::ParseError;
use super::super::Rule;
use super::{
    extract_statement_annotations, next_required, parse_annotated_sender_ref, syntax_error,
};

/// Parse send statement: A -> B: Message(payload)
pub(crate) fn parse_send_stmt(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
) -> std::result::Result<Statement, ParseError> {
    let span = pair.as_span();
    let mut inner = pair.into_inner();

    let from_pair = next_required(&mut inner, span, input, "send is missing sender role")?;
    let (from, from_annotations) = match from_pair.as_rule() {
        Rule::annotated_sender_ref => parse_annotated_sender_ref(from_pair, declared_roles, input)?,
        Rule::role_ref => (
            parse_role_ref(from_pair, declared_roles, input)?,
            HashMap::new(),
        ),
        _ => {
            return Err(syntax_error(
                span,
                input,
                "send is missing sender role".to_string(),
            ))
        }
    };

    let to_pair = next_required(&mut inner, span, input, "send is missing receiver role")?;
    let to = parse_role_ref(to_pair, declared_roles, input)?;

    let message_pair = next_required(&mut inner, span, input, "send is missing message payload")?;
    let message = parse_message(message_pair, input)?;
    let annotations = extract_statement_annotations(&from_annotations);

    Ok(Statement::Send {
        from,
        to,
        message,
        annotations,
        from_annotations,
        to_annotations: HashMap::new(),
    })
}

/// Parse broadcast statement: A ->* : Message(payload)
pub(crate) fn parse_broadcast_stmt(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
) -> std::result::Result<Statement, ParseError> {
    let span = pair.as_span();
    let mut inner = pair.into_inner();

    let from_pair = next_required(&mut inner, span, input, "broadcast is missing sender role")?;
    let (from, from_annotations) = match from_pair.as_rule() {
        Rule::annotated_sender_ref => parse_annotated_sender_ref(from_pair, declared_roles, input)?,
        Rule::role_ref => (
            parse_role_ref(from_pair, declared_roles, input)?,
            HashMap::new(),
        ),
        _ => {
            return Err(syntax_error(
                span,
                input,
                "broadcast is missing sender role".to_string(),
            ))
        }
    };

    let message_pair = next_required(&mut inner, span, input, "broadcast is missing message")?;
    let message = parse_message(message_pair, input)?;
    let annotations = extract_statement_annotations(&from_annotations);

    Ok(Statement::Broadcast {
        from,
        message,
        annotations,
        from_annotations,
    })
}
