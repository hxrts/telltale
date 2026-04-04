//! Parsers for semantic protocol operations (begin, commit, etc.).

use super::{next_required, parse_role_ref, syntax_error, ParseError, Rule};
use crate::ast::CommitmentOutcome;
use crate::compiler::parser::declarations::parse_progress_attachment;
use crate::compiler::parser::types::Statement;
use std::collections::HashSet;

pub(crate) fn parse_begin_stmt(
    pair: pest::iterators::Pair<Rule>,
    input: &str,
) -> std::result::Result<Statement, ParseError> {
    let span = pair.as_span();
    let mut inner = pair.into_inner();
    let operation = next_required(
        &mut inner,
        span,
        input,
        "begin is missing an operation name",
    )?
    .as_str()
    .to_string();
    let mut args = Vec::new();
    let mut progress = None;
    for item in inner {
        match item.as_rule() {
            Rule::begin_args => {
                for arg in item.into_inner() {
                    if arg.as_rule() == Rule::argument_list {
                        args.extend(
                            arg.into_inner()
                                .map(|atom| atom.as_str().trim().to_string())
                                .collect::<Vec<_>>(),
                        );
                    }
                }
            }
            Rule::progress_attachment => {
                progress = Some(parse_progress_attachment(item, input)?);
            }
            _ => {}
        }
    }
    Ok(Statement::Begin {
        operation,
        args,
        progress,
    })
}

pub(crate) fn parse_await_stmt(
    pair: pest::iterators::Pair<Rule>,
    input: &str,
) -> std::result::Result<Statement, ParseError> {
    let span = pair.as_span();
    let mut inner = pair.into_inner();
    let operation = next_required(
        &mut inner,
        span,
        input,
        "await is missing an operation name",
    )?
    .as_str()
    .to_string();
    Ok(Statement::Await { operation })
}

pub(crate) fn parse_resolve_stmt(
    pair: pest::iterators::Pair<Rule>,
    input: &str,
) -> std::result::Result<Statement, ParseError> {
    let span = pair.as_span();
    let mut inner = pair.into_inner();
    let operation = next_required(
        &mut inner,
        span,
        input,
        "resolve is missing an operation name",
    )?
    .as_str()
    .to_string();
    let outcome_pair = next_required(&mut inner, span, input, "resolve is missing an outcome")?;
    let outcome = match outcome_pair.as_rule() {
        Rule::resolve_outcome => {
            let inner_outcome = outcome_pair.into_inner().next().ok_or_else(|| {
                syntax_error(
                    span,
                    input,
                    "resolve outcome is missing a variant".to_string(),
                )
            })?;
            match inner_outcome.as_rule() {
                Rule::resolve_success => CommitmentOutcome::Success(
                    inner_outcome
                        .into_inner()
                        .next()
                        .map(|payload| payload.as_str().trim().to_string()),
                ),
                Rule::resolve_failure => CommitmentOutcome::Failure(
                    inner_outcome
                        .into_inner()
                        .next()
                        .map(|payload| payload.as_str().trim().to_string()),
                ),
                Rule::resolve_timeout => CommitmentOutcome::Timeout(
                    inner_outcome
                        .into_inner()
                        .next()
                        .map(|payload| payload.as_str().trim().to_string()),
                ),
                Rule::resolve_cancelled => CommitmentOutcome::Cancelled,
                _ => {
                    return Err(syntax_error(
                        span,
                        input,
                        "resolve outcome variant is invalid".to_string(),
                    ));
                }
            }
        }
        _ => {
            return Err(syntax_error(
                span,
                input,
                "resolve outcome is invalid".to_string(),
            ));
        }
    };

    Ok(Statement::Resolve { operation, outcome })
}

pub(crate) fn parse_invalidate_stmt(
    pair: pest::iterators::Pair<Rule>,
    input: &str,
) -> std::result::Result<Statement, ParseError> {
    let span = pair.as_span();
    let mut inner = pair.into_inner();
    let operation = next_required(
        &mut inner,
        span,
        input,
        "invalidate is missing an operation name",
    )?
    .as_str()
    .to_string();
    Ok(Statement::Invalidate { operation })
}

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

pub(crate) fn parse_publish_authority_stmt(
    pair: pest::iterators::Pair<Rule>,
    input: &str,
) -> std::result::Result<Statement, ParseError> {
    let span = pair.as_span();
    let mut inner = pair.into_inner();
    let witness = next_required(
        &mut inner,
        span,
        input,
        "publish is missing a witness binding",
    )?
    .as_str()
    .to_string();
    let publication_name = next_required(
        &mut inner,
        span,
        input,
        "publish is missing a publication name after `as`",
    )?
    .as_str()
    .to_string();
    Ok(Statement::PublishAuthority {
        witness,
        publication_name,
    })
}

pub(crate) fn parse_materialize_stmt(
    pair: pest::iterators::Pair<Rule>,
    input: &str,
) -> std::result::Result<Statement, ParseError> {
    let span = pair.as_span();
    let mut inner = pair.into_inner();
    let proof = next_required(
        &mut inner,
        span,
        input,
        "materialize is missing a proof name",
    )?
    .as_str()
    .to_string();
    let publication = next_required(
        &mut inner,
        span,
        input,
        "materialize is missing a publication name after `from`",
    )?
    .as_str()
    .to_string();
    Ok(Statement::Materialize { proof, publication })
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
