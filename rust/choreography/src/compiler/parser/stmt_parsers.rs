//! Individual statement parsers.
//!
//! This module contains parsers for each statement type in the choreography DSL.

use crate::ast::{Condition, Role};
use proc_macro2::TokenStream;
use quote::format_ident;
use std::collections::{HashMap, HashSet};

use super::error::{ErrorSpan, ParseError};
use super::role::parse_role_ref;
use super::statement::{parse_block, parse_duration};
use super::types::{ChoiceBranch, PredicateExpr, Statement};
use super::Rule;

mod control_flow;
mod vm;
pub(super) use control_flow::{
    parse_call_stmt, parse_continue_stmt, parse_handshake_stmt, parse_quorum_collect_stmt,
    parse_rec_stmt, parse_retry_stmt,
};
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

/// Parse send statement: A -> B: Message(payload)
pub(super) fn parse_send_stmt(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
) -> std::result::Result<Statement, ParseError> {
    let span = pair.as_span();
    let mut inner = pair.into_inner();

    let from_pair = next_required(&mut inner, span, input, "send is missing sender role")?;
    let from = parse_role_ref(from_pair, declared_roles, input)?;

    let to_pair = next_required(&mut inner, span, input, "send is missing receiver role")?;
    let to = parse_role_ref(to_pair, declared_roles, input)?;

    let message_pair = next_required(&mut inner, span, input, "send is missing message payload")?;
    let message = super::statement::parse_message(message_pair, input)?;

    Ok(Statement::Send {
        from,
        to,
        message,
        annotations: HashMap::new(),
        from_annotations: HashMap::new(),
        to_annotations: HashMap::new(),
    })
}

/// Parse broadcast statement: A ->* : Message(payload)
pub(super) fn parse_broadcast_stmt(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
) -> std::result::Result<Statement, ParseError> {
    let span = pair.as_span();
    let mut inner = pair.into_inner();

    let from_pair = next_required(&mut inner, span, input, "broadcast is missing sender role")?;
    let from = parse_role_ref(from_pair, declared_roles, input)?;

    let message_pair = next_required(&mut inner, span, input, "broadcast is missing message")?;
    let message = super::statement::parse_message(message_pair, input)?;

    Ok(Statement::Broadcast {
        from,
        message,
        annotations: HashMap::new(),
        from_annotations: HashMap::new(),
    })
}

/// Parse choice statement
pub(super) fn parse_choice_stmt(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
    protocol_defs: &HashMap<String, Vec<Statement>>,
) -> std::result::Result<Statement, ParseError> {
    let span = pair.as_span();
    let mut role: Option<Role> = None;
    let mut branches = Vec::new();

    let mut parse_branch = |item: pest::iterators::Pair<Rule>| -> Result<(), ParseError> {
        let branch_span = item.as_span();
        let mut branch_inner = item.into_inner();
        let label_pair = next_required(
            &mut branch_inner,
            branch_span,
            input,
            "choice branch is missing label",
        )?;
        let label = format_ident!("{}", label_pair.as_str());

        // Check for optional guard
        let mut guard = None;
        let next_item = next_required(
            &mut branch_inner,
            branch_span,
            input,
            "choice branch is missing body",
        )?;
        let body = if let Rule::guard = next_item.as_rule() {
            let guard_span = next_item.as_span();
            let mut guard_inner = next_item.into_inner();
            let guard_expr_pair = next_required(
                &mut guard_inner,
                guard_span,
                input,
                "guard is missing expression",
            )?;
            let guard_expr = guard_expr_pair.as_str();
            guard = Some(parse_guard_predicate(guard_expr, guard_span, input)?);
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

        branches.push(ChoiceBranch {
            label,
            guard,
            statements: body,
        });
        Ok(())
    };

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
                for branch_item in item.into_inner() {
                    match branch_item.as_rule() {
                        Rule::choice_branch => {
                            parse_branch(branch_item)?;
                        }
                        Rule::block_choice => {
                            for nested in branch_item.into_inner() {
                                if nested.as_rule() == Rule::choice_branch {
                                    parse_branch(nested)?;
                                }
                            }
                        }
                        _ => {}
                    }
                }
            }
            Rule::role_ref => {
                role = Some(parse_role_ref(item, declared_roles, input)?);
            }
            Rule::choice_branch => {
                parse_branch(item)?;
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

/// Parse timed choice statement
/// Syntax: timed_choice at Alice(5s) { OnTime { ... } TimedOut { ... } }
pub(super) fn parse_timed_choice_stmt(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
    protocol_defs: &HashMap<String, Vec<Statement>>,
) -> std::result::Result<Statement, ParseError> {
    let span = pair.as_span();
    let mut role: Option<Role> = None;
    let mut duration_ms: Option<u64> = None;
    let mut branches = Vec::new();

    let mut parse_branch = |item: pest::iterators::Pair<Rule>| -> Result<(), ParseError> {
        let branch_span = item.as_span();
        let mut branch_inner = item.into_inner();
        let label_pair = next_required(
            &mut branch_inner,
            branch_span,
            input,
            "timed_choice branch is missing label",
        )?;
        let label = format_ident!("{}", label_pair.as_str());

        // Check for optional guard
        let mut guard = None;
        let next_item = next_required(
            &mut branch_inner,
            branch_span,
            input,
            "timed_choice branch is missing body",
        )?;
        let body = if let Rule::guard = next_item.as_rule() {
            let guard_span = next_item.as_span();
            let mut guard_inner = next_item.into_inner();
            let guard_expr_pair = next_required(
                &mut guard_inner,
                guard_span,
                input,
                "guard is missing expression",
            )?;
            let guard_expr = guard_expr_pair.as_str();
            guard = Some(parse_guard_predicate(guard_expr, guard_span, input)?);
            let body_pair = next_required(
                &mut branch_inner,
                branch_span,
                input,
                "timed_choice branch with guard is missing body",
            )?;
            parse_block(body_pair, declared_roles, input, protocol_defs)?
        } else {
            parse_block(next_item, declared_roles, input, protocol_defs)?
        };

        branches.push(ChoiceBranch {
            label,
            guard,
            statements: body,
        });
        Ok(())
    };

    for item in pair.into_inner() {
        match item.as_rule() {
            Rule::role_ref => {
                role = Some(parse_role_ref(item, declared_roles, input)?);
            }
            Rule::duration => {
                duration_ms = Some(parse_duration(item, input)?);
            }
            Rule::choice_block => {
                for branch_item in item.into_inner() {
                    match branch_item.as_rule() {
                        Rule::choice_branch => {
                            parse_branch(branch_item)?;
                        }
                        Rule::block_choice => {
                            for nested in branch_item.into_inner() {
                                if nested.as_rule() == Rule::choice_branch {
                                    parse_branch(nested)?;
                                }
                            }
                        }
                        _ => {}
                    }
                }
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

/// Parse heartbeat statement
/// Syntax: heartbeat Sender -> Receiver every 1s on_missing(3) { timeout_body } body { normal_body }
pub(super) fn parse_heartbeat_stmt(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
    protocol_defs: &HashMap<String, Vec<Statement>>,
) -> std::result::Result<Statement, ParseError> {
    let span = pair.as_span();
    let mut sender: Option<Role> = None;
    let mut receiver: Option<Role> = None;
    let mut interval_ms: Option<u64> = None;
    let mut on_missing_count: Option<u32> = None;
    let mut on_missing_body: Vec<Statement> = Vec::new();
    let mut body: Vec<Statement> = Vec::new();

    for item in pair.into_inner() {
        match item.as_rule() {
            Rule::role_ref => {
                // First role_ref is sender, second is receiver
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

    let sender = sender.ok_or_else(|| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "heartbeat is missing sender role".to_string(),
    })?;

    let receiver = receiver.ok_or_else(|| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "heartbeat is missing receiver role".to_string(),
    })?;

    let interval_ms = interval_ms.ok_or_else(|| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "heartbeat is missing interval duration".to_string(),
    })?;

    let on_missing_count = on_missing_count.ok_or_else(|| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "heartbeat is missing on_missing count".to_string(),
    })?;

    Ok(Statement::Heartbeat {
        sender,
        receiver,
        interval_ms,
        on_missing_count,
        on_missing_body,
        body,
    })
}

/// Parse loop statement
#[allow(clippy::too_many_lines)]
pub(super) fn parse_loop_stmt(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
    protocol_defs: &HashMap<String, Vec<Statement>>,
) -> std::result::Result<Statement, ParseError> {
    let mut condition = None;
    let mut body = Vec::new();

    for item in pair.into_inner() {
        match item.as_rule() {
            Rule::loop_spec => {
                for spec in item.into_inner() {
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
                            condition = Some(Condition::RoleDecides(role));
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
                                condition = Some(Condition::Count(count));
                            } else {
                                let token_stream = syn::parse_str::<TokenStream>(count_str)
                                    .map_err(|e| ParseError::InvalidCondition {
                                        message: format!("Invalid repeat value: {e}"),
                                        span: ErrorSpan::from_pest_span(span, input),
                                    })?;
                                condition = Some(Condition::Custom(token_stream));
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
                            let cond_lit = syn::parse_str::<syn::LitStr>(cond_pair.as_str())
                                .map_err(|e| ParseError::InvalidCondition {
                                    message: format!("Invalid loop condition string: {e}"),
                                    span: ErrorSpan::from_pest_span(span, input),
                                })?;
                            let token_stream =
                                parse_loop_predicate(&cond_lit.value(), span, input)?;
                            condition = Some(Condition::Custom(token_stream));
                        }
                        Rule::loop_forever => {
                            condition = None;
                        }
                        _ => {}
                    }
                }
            }
            Rule::loop_decide | Rule::loop_repeat | Rule::loop_while | Rule::loop_forever => {
                // Fall back for grammars that expose loop spec directly.
                let spec = item;
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
                        condition = Some(Condition::RoleDecides(role));
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
                            condition = Some(Condition::Count(count));
                        } else {
                            let token_stream =
                                syn::parse_str::<TokenStream>(count_str).map_err(|e| {
                                    ParseError::InvalidCondition {
                                        message: format!("Invalid repeat value: {e}"),
                                        span: ErrorSpan::from_pest_span(span, input),
                                    }
                                })?;
                            condition = Some(Condition::Custom(token_stream));
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
                        let cond_lit =
                            syn::parse_str::<syn::LitStr>(cond_pair.as_str()).map_err(|e| {
                                ParseError::InvalidCondition {
                                    message: format!("Invalid loop condition string: {e}"),
                                    span: ErrorSpan::from_pest_span(span, input),
                                }
                            })?;
                        let token_stream = parse_loop_predicate(&cond_lit.value(), span, input)?;
                        condition = Some(Condition::Custom(token_stream));
                    }
                    Rule::loop_forever => {
                        condition = None;
                    }
                    _ => {}
                }
            }
            Rule::block => {
                body = parse_block(item, declared_roles, input, protocol_defs)?;
            }
            _ => {}
        }
    }

    Ok(Statement::Loop { condition, body })
}

/// Parse branch statement
pub(super) fn parse_branch_stmt(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
    protocol_defs: &HashMap<String, Vec<Statement>>,
) -> std::result::Result<Statement, ParseError> {
    let span = ErrorSpan::from_pest_span(pair.as_span(), input);
    let mut body = Vec::new();
    for item in pair.into_inner() {
        if item.as_rule() == Rule::block {
            body = parse_block(item, declared_roles, input, protocol_defs)?;
        }
    }
    Ok(Statement::Branch { body, span })
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
