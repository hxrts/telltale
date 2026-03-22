use std::collections::{HashMap, HashSet};

use crate::ast::Role;

use super::super::role::parse_role_ref;
use super::super::statement::{parse_block, parse_duration, parse_statement};
use super::super::types::{AuthorityExprSpec, CaseBranchSpec, CasePatternSpec, Statement};
use super::super::Rule;
use super::{next_required, syntax_error};

fn parse_authority_expr(pair: pest::iterators::Pair<Rule>) -> Result<AuthorityExprSpec, String> {
    let pair = if pair.as_rule() == Rule::authority_expr {
        pair.into_inner()
            .next()
            .ok_or_else(|| "authority expression is empty".to_string())?
    } else {
        pair
    };

    match pair.as_rule() {
        Rule::check_expr => {
            let call = pair
                .into_inner()
                .next()
                .ok_or_else(|| "check is missing effect call".to_string())?;
            parse_effect_call(call).map(|(effect, operation, args)| AuthorityExprSpec::Check {
                effect,
                operation,
                args,
            })
        }
        Rule::observe_expr => {
            let call = pair
                .into_inner()
                .next()
                .ok_or_else(|| "observe is missing effect call".to_string())?;
            parse_effect_call(call).map(|(effect, operation, args)| AuthorityExprSpec::Observe {
                effect,
                operation,
                args,
            })
        }
        Rule::transfer_expr => {
            let span = pair.as_span();
            let mut inner = pair.into_inner();
            let subject = inner
                .next()
                .ok_or_else(|| "transfer is missing subject".to_string())?
                .as_str()
                .to_string();
            let from = inner
                .next()
                .ok_or_else(|| "transfer is missing source role".to_string())?
                .as_str()
                .to_string();
            let to = inner
                .next()
                .ok_or_else(|| "transfer is missing target role".to_string())?
                .as_str()
                .to_string();
            if span.as_str().trim().is_empty() {
                return Err("transfer expression is empty".to_string());
            }
            Ok(AuthorityExprSpec::Transfer { subject, from, to })
        }
        Rule::result_ctor_expr | Rule::maybe_ctor_expr => {
            let mut inner = pair.into_inner();
            let ctor = inner
                .next()
                .ok_or_else(|| "constructor expression is missing constructor".to_string())?
                .as_str()
                .to_string();
            let arg = inner.next().map(|arg| arg.as_str().trim().to_string());
            Ok(AuthorityExprSpec::Constructor { name: ctor, arg })
        }
        Rule::call_expr => {
            let mut inner = pair.into_inner();
            let name = inner
                .next()
                .ok_or_else(|| "call expression is missing name".to_string())?
                .as_str()
                .to_string();
            let args = inner
                .next()
                .map(parse_argument_list)
                .transpose()?
                .unwrap_or_default();
            Ok(AuthorityExprSpec::Call { name, args })
        }
        Rule::ident_expr | Rule::ident => {
            Ok(AuthorityExprSpec::Var(pair.as_str().trim().to_string()))
        }
        _ => Err(format!(
            "unsupported authority expression: {:?}",
            pair.as_rule()
        )),
    }
}

fn parse_argument_list(pair: pest::iterators::Pair<Rule>) -> Result<Vec<String>, String> {
    let mut args = Vec::new();
    for arg in pair.into_inner() {
        match arg.as_rule() {
            Rule::authority_atom
            | Rule::ident_expr
            | Rule::effect_call
            | Rule::string
            | Rule::integer => {
                args.push(arg.as_str().trim().to_string());
            }
            _ => {}
        }
    }
    Ok(args)
}

fn parse_branch_body(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
    protocol_defs: &HashMap<String, Vec<Statement>>,
) -> std::result::Result<Vec<Statement>, super::super::error::ParseError> {
    let pair = if pair.as_rule() == Rule::branch_body {
        let span = pair.as_span();
        pair.into_inner()
            .next()
            .ok_or_else(|| syntax_error(span, input, "branch body is empty"))?
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
            "expected an indented branch body or compact statement body",
        )),
    }
}

pub(crate) fn parse_effect_call(
    pair: pest::iterators::Pair<Rule>,
) -> Result<(String, String, Vec<String>), String> {
    let span = pair.as_span();
    let mut inner = pair.into_inner();
    let effect = inner
        .next()
        .ok_or_else(|| "effect call is missing interface".to_string())?
        .as_str()
        .to_string();
    let operation = inner
        .next()
        .ok_or_else(|| "effect call is missing operation".to_string())?
        .as_str()
        .to_string();
    let args = inner
        .next()
        .map(parse_argument_list)
        .transpose()?
        .unwrap_or_default();
    if span.as_str().trim().is_empty() {
        return Err("effect call is empty".to_string());
    }
    Ok((effect, operation, args))
}

pub(crate) fn parse_let_stmt(
    pair: pest::iterators::Pair<Rule>,
    _declared_roles: &HashSet<String>,
    input: &str,
) -> std::result::Result<Statement, super::super::error::ParseError> {
    let span = pair.as_span();
    let mut inner = pair.into_inner();
    let name = next_required(&mut inner, span, input, "let binding is missing name")?
        .as_str()
        .to_string();
    let expr = next_required(&mut inner, span, input, "let binding is missing expression")?;
    let expr = parse_authority_expr(expr).map_err(|message| syntax_error(span, input, message))?;
    Ok(Statement::Let {
        name,
        expr,
        body: None,
    })
}

pub(crate) fn parse_let_in_stmt(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
    protocol_defs: &HashMap<String, Vec<Statement>>,
) -> std::result::Result<Statement, super::super::error::ParseError> {
    let span = pair.as_span();
    let mut inner = pair.into_inner();
    let name = next_required(&mut inner, span, input, "let binding is missing name")?
        .as_str()
        .to_string();
    let expr = next_required(&mut inner, span, input, "let binding is missing expression")?;
    let expr = parse_authority_expr(expr).map_err(|message| syntax_error(span, input, message))?;
    let body_pair = next_required(&mut inner, span, input, "let ... in is missing body")?;
    let body = parse_block(body_pair, declared_roles, input, protocol_defs)?;
    Ok(Statement::Let {
        name,
        expr,
        body: Some(body),
    })
}

pub(crate) fn parse_case_stmt(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
    protocol_defs: &HashMap<String, Vec<Statement>>,
) -> std::result::Result<Statement, super::super::error::ParseError> {
    let span = pair.as_span();
    let mut inner = pair.into_inner();
    let expr_pair = next_required(&mut inner, span, input, "case is missing scrutinee")?;
    let expr =
        parse_authority_expr(expr_pair).map_err(|message| syntax_error(span, input, message))?;
    let block = next_required(&mut inner, span, input, "case is missing branches")?;
    let mut branches = Vec::new();
    for item in block.into_inner() {
        if item.as_rule() != Rule::case_branch {
            continue;
        }
        let branch_span = item.as_span();
        let mut branch_inner = item.into_inner();
        let pattern_pair = next_required(
            &mut branch_inner,
            branch_span,
            input,
            "case branch is missing pattern",
        )?;
        let pattern = parse_case_pattern(pattern_pair);
        let body_pair = next_required(
            &mut branch_inner,
            branch_span,
            input,
            "case branch is missing body",
        )?;
        let statements = parse_branch_body(body_pair, declared_roles, input, protocol_defs)?;
        branches.push(CaseBranchSpec {
            pattern,
            statements,
        });
    }
    if branches.is_empty() {
        return Err(syntax_error(
            span,
            input,
            "case/of requires at least one branch",
        ));
    }
    Ok(Statement::Case { expr, branches })
}

fn parse_case_pattern(pair: pest::iterators::Pair<Rule>) -> CasePatternSpec {
    let mut inner = pair.into_inner();
    let constructor = inner
        .next()
        .map(|p| p.as_str().to_string())
        .unwrap_or_default();
    let binders = inner
        .flat_map(|p| match p.as_rule() {
            Rule::match_pattern_payload => p
                .into_inner()
                .filter(|inner| inner.as_rule() == Rule::ident)
                .map(|ident| ident.as_str().to_string())
                .collect::<Vec<_>>(),
            Rule::ident => vec![p.as_str().to_string()],
            _ => Vec::new(),
        })
        .collect();
    CasePatternSpec {
        constructor,
        binders,
    }
}

pub(crate) fn parse_timeout_stmt(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
    protocol_defs: &HashMap<String, Vec<Statement>>,
) -> std::result::Result<Statement, super::super::error::ParseError> {
    let span = pair.as_span();
    let mut duration_ms = None;
    let mut role: Option<Role> = None;
    let mut blocks: Vec<Vec<Statement>> = Vec::new();
    for item in pair.into_inner() {
        match item.as_rule() {
            Rule::duration => duration_ms = Some(parse_duration(item, input)?),
            Rule::role_ref => role = Some(parse_role_ref(item, declared_roles, input)?),
            Rule::block | Rule::statement | Rule::branch_body => {
                blocks.push(parse_branch_body(item, declared_roles, input, protocol_defs)?)
            }
            _ => {}
        }
    }
    if blocks.len() < 2 {
        return Err(syntax_error(
            span,
            input,
            "timeout requires body and on timeout branch",
        ));
    }
    Ok(Statement::Timeout {
        role: role.ok_or_else(|| syntax_error(span, input, "timeout is missing deciding role"))?,
        duration_ms: duration_ms
            .ok_or_else(|| syntax_error(span, input, "timeout is missing duration"))?,
        body: blocks.remove(0),
        on_timeout: blocks.remove(0),
        on_cancel: blocks.pop(),
    })
}
