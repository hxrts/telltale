//! Parsers for choice branches and guarded selection.

use std::collections::{HashMap, HashSet};

use crate::ast::Role;
use quote::format_ident;

use super::super::error::{ErrorSpan, ParseError};
use super::super::role::parse_role_ref;
use super::super::statement::{parse_block, parse_statement};
use super::super::types::{ChoiceBranch, ChoiceGuardSpec, Statement};
use super::super::Rule;
use super::authority::parse_effect_call;
use super::{next_required, parse_guard_predicate, syntax_error};

fn parse_choice_branch(
    item: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
    protocol_defs: &HashMap<String, Vec<Statement>>,
) -> Result<ChoiceBranch, ParseError> {
    let branch_span = item.as_span();
    let mut branch_inner = item.into_inner();
    let label_pair = next_required(
        &mut branch_inner,
        branch_span,
        input,
        "choice branch is missing label",
    )?;
    let label = format_ident!("{}", label_pair.as_str());

    let mut guard = None;
    let next_item = next_required(
        &mut branch_inner,
        branch_span,
        input,
        "choice branch is missing body",
    )?;
    let statements = if let Rule::guard = next_item.as_rule() {
        let guard_span = next_item.as_span();
        let mut guard_inner = next_item.into_inner();
        let guard_kind = next_required(
            &mut guard_inner,
            guard_span,
            input,
            "guard is missing expression",
        )?;
        guard = Some(match guard_kind.as_rule() {
            Rule::predicate_guard => {
                let mut predicate_inner = guard_kind.into_inner();
                let guard_expr_pair = next_required(
                    &mut predicate_inner,
                    guard_span,
                    input,
                    "guard is missing expression",
                )?;
                ChoiceGuardSpec::Predicate(parse_guard_predicate(
                    guard_expr_pair.as_str(),
                    guard_span,
                    input,
                )?)
            }
            Rule::evidence_guard => {
                let mut evidence_inner = guard_kind.into_inner();
                let call_pair = next_required(
                    &mut evidence_inner,
                    guard_span,
                    input,
                    "evidence guard is missing check call",
                )?;
                let (effect, operation, args) =
                    parse_effect_call(call_pair).map_err(|message| ParseError::Syntax {
                        span: ErrorSpan::from_pest_span(guard_span, input),
                        message,
                    })?;
                let binding = next_required(
                    &mut evidence_inner,
                    guard_span,
                    input,
                    "evidence guard is missing witness binding",
                )?
                .as_str()
                .to_string();
                ChoiceGuardSpec::Evidence {
                    effect,
                    operation,
                    args,
                    binding,
                }
            }
            _ => {
                return Err(ParseError::Syntax {
                    span: ErrorSpan::from_pest_span(guard_span, input),
                    message: "unsupported guard form".to_string(),
                })
            }
        });
        let body_pair = next_required(
            &mut branch_inner,
            branch_span,
            input,
            "choice branch with guard is missing body",
        )?;
        parse_branch_body(body_pair, declared_roles, input, protocol_defs)?
    } else {
        parse_branch_body(next_item, declared_roles, input, protocol_defs)?
    };

    Ok(ChoiceBranch {
        label,
        guard,
        statements,
    })
}

fn parse_branch_body(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
    protocol_defs: &HashMap<String, Vec<Statement>>,
) -> Result<Vec<Statement>, ParseError> {
    let pair = if pair.as_rule() == Rule::branch_body {
        let span = pair.as_span();
        pair.into_inner()
            .next()
            .ok_or_else(|| syntax_error(span, input, "branch body is empty".to_string()))?
    } else {
        pair
    };
    match pair.as_rule() {
        Rule::block => parse_block(pair, declared_roles, input, protocol_defs),
        Rule::statement => Ok(vec![parse_statement(
            pair,
            declared_roles,
            input,
            protocol_defs,
        )?]),
        _ => Err(syntax_error(
            pair.as_span(),
            input,
            "expected an indented branch body or compact statement body".to_string(),
        )),
    }
}

fn collect_choice_branches(
    branch_container: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
    protocol_defs: &HashMap<String, Vec<Statement>>,
    branches: &mut Vec<ChoiceBranch>,
) -> Result<(), ParseError> {
    for branch_item in branch_container.into_inner() {
        match branch_item.as_rule() {
            Rule::choice_branch => {
                branches.push(parse_choice_branch(
                    branch_item,
                    declared_roles,
                    input,
                    protocol_defs,
                )?);
            }
            Rule::block_choice => {
                for nested in branch_item.into_inner() {
                    if nested.as_rule() == Rule::choice_branch {
                        branches.push(parse_choice_branch(
                            nested,
                            declared_roles,
                            input,
                            protocol_defs,
                        )?);
                    }
                }
            }
            _ => {}
        }
    }
    Ok(())
}

/// Parse choice statement.
pub(crate) fn parse_choice_stmt(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
    protocol_defs: &HashMap<String, Vec<Statement>>,
) -> std::result::Result<Statement, ParseError> {
    let span = pair.as_span();
    let mut role: Option<Role> = None;
    let mut branches = Vec::new();

    for item in pair.into_inner() {
        match item.as_rule() {
            Rule::choice_head => {
                for head_item in item.into_inner() {
                    if head_item.as_rule() == Rule::role_ref {
                        role = Some(parse_role_ref(head_item, declared_roles, input)?);
                    }
                }
            }
            Rule::choice_block => {
                collect_choice_branches(item, declared_roles, input, protocol_defs, &mut branches)?;
            }
            Rule::role_ref => {
                role = Some(parse_role_ref(item, declared_roles, input)?);
            }
            Rule::choice_branch => {
                branches.push(parse_choice_branch(
                    item,
                    declared_roles,
                    input,
                    protocol_defs,
                )?);
            }
            _ => {}
        }
    }

    let role = role.ok_or_else(|| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "choice is missing a deciding role".to_string(),
    })?;

    Ok(Statement::Choice {
        role,
        branches,
        annotations: Vec::new(),
    })
}

/// Parse `par` statement with bar-prefixed branches.
pub(crate) fn parse_par_stmt(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
    protocol_defs: &HashMap<String, Vec<Statement>>,
) -> std::result::Result<Statement, ParseError> {
    let span = pair.as_span();
    let mut branches = Vec::new();

    for item in pair.into_inner() {
        if item.as_rule() != Rule::par_block {
            continue;
        }

        for branch_item in item.into_inner() {
            if branch_item.as_rule() != Rule::par_branch {
                continue;
            }

            let mut branch_statements = Vec::new();
            for branch_part in branch_item.into_inner() {
                match branch_part.as_rule() {
                    Rule::block => {
                        branch_statements =
                            parse_block(branch_part, declared_roles, input, protocol_defs)?;
                    }
                    _ => {
                        branch_statements.push(parse_statement(
                            branch_part,
                            declared_roles,
                            input,
                            protocol_defs,
                        )?);
                    }
                }
            }

            branches.push(branch_statements);
        }
    }

    if branches.len() < 2 {
        return Err(syntax_error(
            span,
            input,
            "`par` requires at least two `|` branches".to_string(),
        ));
    }

    Ok(Statement::Parallel { branches })
}
