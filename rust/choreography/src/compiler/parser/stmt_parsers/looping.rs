use std::collections::HashMap;

use crate::ast::Condition;

use super::super::error::{ErrorSpan, ParseError};
use super::super::role::parse_role_ref;
use super::super::statement::{parse_block, parse_duration};
use super::super::types::Statement;
use super::super::Rule;
use super::{next_required, parse_loop_predicate};

fn parse_loop_condition(
    spec: pest::iterators::Pair<Rule>,
    declared_roles: &std::collections::HashSet<String>,
    input: &str,
) -> Result<Option<Condition>, ParseError> {
    match spec.as_rule() {
        Rule::loop_decide => {
            let span = spec.as_span();
            let role_pair = spec
                .into_inner()
                .find(|p| p.as_rule() == Rule::role_ref)
                .ok_or_else(|| ParseError::Syntax {
                    span: ErrorSpan::from_pest_span(span, input),
                    message: "loop decide by is missing a role".to_string(),
                })?;
            let role = parse_role_ref(role_pair, declared_roles, input)?;
            Ok(Some(Condition::RoleDecides(role)))
        }
        Rule::loop_repeat => {
            let span = spec.as_span();
            let mut repeat_inner = spec.into_inner();
            let count_pair = next_required(
                &mut repeat_inner,
                span,
                input,
                "loop repeat is missing value",
            )?;
            let count_str = count_pair.as_str();
            if let Ok(count) = count_str.parse::<usize>() {
                Ok(Some(Condition::Count(count)))
            } else {
                let token_stream =
                    syn::parse_str::<proc_macro2::TokenStream>(count_str).map_err(|e| {
                        ParseError::InvalidCondition {
                            message: format!("Invalid repeat value: {e}"),
                            span: ErrorSpan::from_pest_span(span, input),
                        }
                    })?;
                Ok(Some(Condition::Custom(token_stream)))
            }
        }
        Rule::loop_while => {
            let span = spec.as_span();
            let mut while_inner = spec.into_inner();
            let cond_pair = next_required(
                &mut while_inner,
                span,
                input,
                "loop while is missing condition string",
            )?;
            let cond_lit = syn::parse_str::<syn::LitStr>(cond_pair.as_str()).map_err(|e| {
                ParseError::InvalidCondition {
                    message: format!("Invalid loop condition string: {e}"),
                    span: ErrorSpan::from_pest_span(span, input),
                }
            })?;
            Ok(Some(Condition::Custom(parse_loop_predicate(
                &cond_lit.value(),
                span,
                input,
            )?)))
        }
        Rule::loop_forever => Ok(None),
        _ => Ok(None),
    }
}

/// Parse heartbeat statement.
pub(crate) fn parse_heartbeat_stmt(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &std::collections::HashSet<String>,
    input: &str,
    protocol_defs: &HashMap<String, Vec<Statement>>,
) -> std::result::Result<Statement, ParseError> {
    let span = pair.as_span();
    let mut sender = None;
    let mut receiver = None;
    let mut interval_ms = None;
    let mut on_missing_count = None;
    let mut on_missing_body = Vec::new();
    let mut body = Vec::new();

    for item in pair.into_inner() {
        match item.as_rule() {
            Rule::role_ref => {
                let role = parse_role_ref(item, declared_roles, input)?;
                if sender.is_none() {
                    sender = Some(role);
                } else {
                    receiver = Some(role);
                }
            }
            Rule::duration => {
                interval_ms = Some(parse_duration(item, input)?);
            }
            Rule::heartbeat_on_missing => {
                for inner in item.into_inner() {
                    match inner.as_rule() {
                        Rule::integer => {
                            on_missing_count =
                                Some(inner.as_str().parse().map_err(|_| ParseError::Syntax {
                                    span: ErrorSpan::from_pest_span(span, input),
                                    message: "Invalid on_missing count".to_string(),
                                })?);
                        }
                        Rule::block => {
                            on_missing_body =
                                parse_block(inner, declared_roles, input, protocol_defs)?;
                        }
                        _ => {}
                    }
                }
            }
            Rule::heartbeat_body => {
                for inner in item.into_inner() {
                    if inner.as_rule() == Rule::block {
                        body = parse_block(inner, declared_roles, input, protocol_defs)?;
                    }
                }
            }
            _ => {}
        }
    }

    Ok(Statement::Heartbeat {
        sender: sender.ok_or_else(|| ParseError::Syntax {
            span: ErrorSpan::from_pest_span(span, input),
            message: "heartbeat is missing sender role".to_string(),
        })?,
        receiver: receiver.ok_or_else(|| ParseError::Syntax {
            span: ErrorSpan::from_pest_span(span, input),
            message: "heartbeat is missing receiver role".to_string(),
        })?,
        interval_ms: interval_ms.ok_or_else(|| ParseError::Syntax {
            span: ErrorSpan::from_pest_span(span, input),
            message: "heartbeat is missing interval duration".to_string(),
        })?,
        on_missing_count: on_missing_count.ok_or_else(|| ParseError::Syntax {
            span: ErrorSpan::from_pest_span(span, input),
            message: "heartbeat is missing on_missing count".to_string(),
        })?,
        on_missing_body,
        body,
    })
}

/// Parse loop statement.
pub(crate) fn parse_loop_stmt(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &std::collections::HashSet<String>,
    input: &str,
    protocol_defs: &HashMap<String, Vec<Statement>>,
) -> std::result::Result<Statement, ParseError> {
    let mut condition = None;
    let mut body = Vec::new();

    for item in pair.into_inner() {
        match item.as_rule() {
            Rule::loop_spec => {
                for spec in item.into_inner() {
                    if matches!(
                        spec.as_rule(),
                        Rule::loop_decide | Rule::loop_repeat | Rule::loop_while | Rule::loop_forever
                    ) {
                        condition = parse_loop_condition(spec, declared_roles, input)?;
                    }
                }
            }
            Rule::loop_decide | Rule::loop_repeat | Rule::loop_while | Rule::loop_forever => {
                condition = parse_loop_condition(item, declared_roles, input)?;
            }
            Rule::block => {
                body = parse_block(item, declared_roles, input, protocol_defs)?;
            }
            _ => {}
        }
    }

    Ok(Statement::Loop { condition, body })
}
