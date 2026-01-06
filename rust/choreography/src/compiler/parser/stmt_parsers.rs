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
use super::types::{ChoiceBranch, Statement};
use super::Rule;

/// Parse send statement: A -> B: Message(payload)
pub(super) fn parse_send_stmt(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
) -> std::result::Result<Statement, ParseError> {
    let mut inner = pair.into_inner();

    let from_pair = inner
        .next()
        .expect("grammar: send_stmt must have sender role");
    let from = parse_role_ref(from_pair, declared_roles, input)?;

    let to_pair = inner
        .next()
        .expect("grammar: send_stmt must have receiver role");
    let to = parse_role_ref(to_pair, declared_roles, input)?;

    let message = super::statement::parse_message(
        inner.next().expect("grammar: send_stmt must have message"),
        input,
    )?;

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
    let mut inner = pair.into_inner();

    let from_pair = inner
        .next()
        .expect("grammar: broadcast_stmt must have sender role");
    let from = parse_role_ref(from_pair, declared_roles, input)?;

    let message = super::statement::parse_message(
        inner
            .next()
            .expect("grammar: broadcast_stmt must have message"),
        input,
    )?;

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
        let mut branch_inner = item.into_inner();
        let label = format_ident!(
            "{}",
            branch_inner
                .next()
                .expect("grammar: choice_branch must have label")
                .as_str()
        );

        // Check for optional guard
        let mut guard = None;
        let next_item = branch_inner
            .next()
            .expect("grammar: choice_branch must have body or guard");
        let body = if let Rule::guard = next_item.as_rule() {
            let guard_span = next_item.as_span();
            let guard_expr = next_item
                .into_inner()
                .next()
                .expect("grammar: guard must have expression")
                .as_str();
            guard = Some(syn::parse_str::<TokenStream>(guard_expr).map_err(|e| {
                ParseError::Syntax {
                    span: ErrorSpan::from_pest_span(guard_span, input),
                    message: format!("Invalid guard expression: {e}"),
                }
            })?);
            parse_block(
                branch_inner
                    .next()
                    .expect("grammar: choice_branch with guard must have body"),
                declared_roles,
                input,
                protocol_defs,
            )?
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
        let mut branch_inner = item.into_inner();
        let label = format_ident!(
            "{}",
            branch_inner
                .next()
                .expect("grammar: choice_branch must have label")
                .as_str()
        );

        // Check for optional guard
        let mut guard = None;
        let next_item = branch_inner
            .next()
            .expect("grammar: choice_branch must have body or guard");
        let body = if let Rule::guard = next_item.as_rule() {
            let guard_span = next_item.as_span();
            let guard_expr = next_item
                .into_inner()
                .next()
                .expect("grammar: guard must have expression")
                .as_str();
            guard = Some(syn::parse_str::<TokenStream>(guard_expr).map_err(|e| {
                ParseError::Syntax {
                    span: ErrorSpan::from_pest_span(guard_span, input),
                    message: format!("Invalid guard expression: {e}"),
                }
            })?);
            parse_block(
                branch_inner
                    .next()
                    .expect("grammar: choice_branch with guard must have body"),
                declared_roles,
                input,
                protocol_defs,
            )?
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
                            let count_pair = spec
                                .into_inner()
                                .next()
                                .expect("grammar: loop_repeat must have value");
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
                            let cond_pair = spec
                                .into_inner()
                                .next()
                                .expect("grammar: loop while must have string");
                            let cond_str = cond_pair.as_str();
                            let token_stream =
                                syn::parse_str::<TokenStream>(cond_str).map_err(|e| {
                                    ParseError::InvalidCondition {
                                        message: format!("Invalid loop condition: {e}"),
                                        span: ErrorSpan::from_pest_span(span, input),
                                    }
                                })?;
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
                        let count_pair = spec
                            .into_inner()
                            .next()
                            .expect("grammar: loop_repeat must have value");
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
                        let cond_pair = spec
                            .into_inner()
                            .next()
                            .expect("grammar: loop while must have string");
                        let cond_str = cond_pair.as_str();
                        let token_stream =
                            syn::parse_str::<TokenStream>(cond_str).map_err(|e| {
                                ParseError::InvalidCondition {
                                    message: format!("Invalid loop condition: {e}"),
                                    span: ErrorSpan::from_pest_span(span, input),
                                }
                            })?;
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

/// Parse recursive statement
pub(super) fn parse_rec_stmt(
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
pub(super) fn parse_call_stmt(
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

/// Parse continue statement (recursive back-reference)
pub(super) fn parse_continue_stmt(
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
