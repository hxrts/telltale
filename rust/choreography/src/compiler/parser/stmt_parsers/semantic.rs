use super::{next_required, parse_role_ref, syntax_error, ParseError, Rule};
use crate::compiler::parser::types::Statement;
use std::collections::HashSet;

pub(crate) fn parse_publish_stmt(
    pair: pest::iterators::Pair<Rule>,
    input: &str,
) -> std::result::Result<Statement, ParseError> {
    let span = pair.as_span();
    let mut inner = pair.into_inner();
    let event = next_required(
        &mut inner,
        span,
        input,
        "publish is missing an event constructor",
    )?
    .as_str()
    .to_string();
    let arg = inner
        .next()
        .map(|payload| payload.as_str().trim().to_string());
    Ok(Statement::Publish { event, arg })
}

pub(crate) fn parse_handoff_stmt(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
) -> std::result::Result<Statement, ParseError> {
    let span = pair.as_span();
    let mut inner = pair.into_inner();
    let operation = next_required(&mut inner, span, input, "handoff is missing an operation")?
        .as_str()
        .to_string();
    let role_pair = next_required(&mut inner, span, input, "handoff is missing a target role")?;
    let target = parse_role_ref(role_pair, declared_roles, input)?;
    let receipt = next_required(&mut inner, span, input, "handoff is missing a receipt")?
        .as_str()
        .to_string();
    Ok(Statement::Handoff {
        operation,
        target,
        receipt,
    })
}

pub(crate) fn parse_dependent_work_stmt(
    pair: pest::iterators::Pair<Rule>,
    input: &str,
) -> std::result::Result<Statement, ParseError> {
    let span = pair.as_span();
    let mut inner = pair.into_inner();
    let name = next_required(
        &mut inner,
        span,
        input,
        "dependent work is missing a work name",
    )?
    .as_str()
    .to_string();
    let mut arg = None;
    let mut required_for = None;
    for item in inner {
        match item.as_rule() {
            Rule::ctor_value_payload => {
                arg = Some(item.as_str().trim().to_string());
            }
            Rule::ident => {
                required_for = Some(item.as_str().to_string());
            }
            _ => {}
        }
    }

    Ok(Statement::DependentWork {
        name,
        arg,
        required_for: required_for.ok_or_else(|| {
            syntax_error(
                span,
                input,
                "dependent work is missing a required-for operation",
            )
        })?,
    })
}
