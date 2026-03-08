use std::collections::{HashMap, HashSet};

use crate::ast::Role;
use quote::format_ident;

use super::super::error::{ErrorSpan, ParseError};
use super::super::role::parse_role_ref;
use super::super::statement::{parse_block, parse_statement};
use super::super::types::{ChoiceBranch, Statement};
use super::super::Rule;
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
        let guard_expr_pair = next_required(
            &mut guard_inner,
            guard_span,
            input,
            "guard is missing expression",
        )?;
        guard = Some(parse_guard_predicate(
            guard_expr_pair.as_str(),
            guard_span,
            input,
        )?);
        let body_pair = next_required(
            &mut branch_inner,
            branch_span,
            input,
            "choice branch with guard is missing body",
        )?;
        parse_block(body_pair, declared_roles, input, protocol_defs)?
    } else {
        parse_block(next_item, declared_roles, input, protocol_defs)?
    };

    Ok(ChoiceBranch {
        label,
        guard,
        statements,
    })
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
        annotations: HashMap::new(),
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

/// Parse timed choice statement.
pub(crate) fn parse_timed_choice_stmt(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
    protocol_defs: &HashMap<String, Vec<Statement>>,
) -> std::result::Result<Statement, ParseError> {
    let span = pair.as_span();
    let mut role: Option<Role> = None;
    let mut duration_ms: Option<u64> = None;
    let mut branches = Vec::new();

    for item in pair.into_inner() {
        match item.as_rule() {
            Rule::role_ref => {
                role = Some(parse_role_ref(item, declared_roles, input)?);
            }
            Rule::duration => {
                duration_ms = Some(super::super::statement::parse_duration(item, input)?);
            }
            Rule::choice_block => {
                collect_choice_branches(item, declared_roles, input, protocol_defs, &mut branches)?;
            }
            _ => {}
        }
    }

    let role = role.ok_or_else(|| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "timed_choice is missing a deciding role".to_string(),
    })?;

    let duration_ms = duration_ms.ok_or_else(|| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "timed_choice is missing a duration".to_string(),
    })?;

    Ok(Statement::TimedChoice {
        role,
        duration_ms,
        branches,
    })
}
