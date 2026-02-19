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
use super::types::{ChoiceBranch, PredicateExpr, Statement, VmCoreOp};
use super::Rule;

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
            guard = Some(parse_guard_predicate(guard_expr, guard_span, input)?);
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
            guard = Some(parse_guard_predicate(guard_expr, guard_span, input)?);
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

pub(super) fn parse_handshake_stmt(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
) -> std::result::Result<Statement, ParseError> {
    let span = pair.as_span();
    let mut inner = pair.into_inner();
    let initiator_pair = inner.next().ok_or_else(|| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "handshake is missing initiator role".to_string(),
    })?;
    let responder_pair = inner.next().ok_or_else(|| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "handshake is missing responder role".to_string(),
    })?;
    let label_pair = inner.next().ok_or_else(|| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "handshake is missing label".to_string(),
    })?;
    Ok(Statement::Handshake {
        initiator: parse_role_ref(initiator_pair, declared_roles, input)?,
        responder: parse_role_ref(responder_pair, declared_roles, input)?,
        label: format_ident!("{}", label_pair.as_str()),
    })
}

pub(super) fn parse_retry_stmt(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
    protocol_defs: &HashMap<String, Vec<Statement>>,
) -> std::result::Result<Statement, ParseError> {
    let span = pair.as_span();
    let mut inner = pair.into_inner();
    let count_pair = inner.next().ok_or_else(|| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "retry is missing iteration count".to_string(),
    })?;
    let block_pair = inner.next().ok_or_else(|| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "retry is missing block body".to_string(),
    })?;
    let count_src = count_pair.as_str();
    let condition = if let Ok(count) = count_src.parse::<usize>() {
        Condition::Count(count)
    } else {
        Condition::Custom(
            syn::parse_str::<TokenStream>(count_src).map_err(|e| ParseError::InvalidCondition {
                message: format!("Invalid retry count: {e}"),
                span: ErrorSpan::from_pest_span(span, input),
            })?,
        )
    };
    let body = parse_block(block_pair, declared_roles, input, protocol_defs)?;
    Ok(Statement::Loop {
        condition: Some(condition),
        body,
    })
}

pub(super) fn parse_quorum_collect_stmt(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
) -> std::result::Result<Statement, ParseError> {
    let span = pair.as_span();
    let mut inner = pair.into_inner();
    let source_pair = inner.next().ok_or_else(|| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "quorum_collect is missing source role".to_string(),
    })?;
    let destination_pair = inner.next().ok_or_else(|| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "quorum_collect is missing destination role".to_string(),
    })?;
    let min_pair = inner.next().ok_or_else(|| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "quorum_collect is missing min count".to_string(),
    })?;
    let message_pair = inner.next().ok_or_else(|| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "quorum_collect is missing message".to_string(),
    })?;
    let min_responses = min_pair.as_str().parse::<u32>().map_err(|_| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "quorum_collect min count must be an integer".to_string(),
    })?;
    Ok(Statement::QuorumCollect {
        source: parse_role_ref(source_pair, declared_roles, input)?,
        destination: parse_role_ref(destination_pair, declared_roles, input)?,
        min_responses,
        message: super::statement::parse_message(message_pair, input)?,
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

fn parse_vm_layer(
    pair: pest::iterators::Pair<Rule>,
    input: &str,
) -> std::result::Result<String, ParseError> {
    let span = pair.as_span();
    let value = match pair.as_rule() {
        Rule::vm_layer => {
            let inner = pair
                .into_inner()
                .next()
                .ok_or_else(|| ParseError::Syntax {
                    span: ErrorSpan::from_pest_span(span, input),
                    message: "vm layer is missing name".to_string(),
                })?;
            inner.as_str().to_string()
        }
        Rule::ident | Rule::string => pair.as_str().to_string(),
        _ => {
            return Err(ParseError::Syntax {
                span: ErrorSpan::from_pest_span(span, input),
                message: "invalid vm layer".to_string(),
            });
        }
    };
    if value.starts_with('\"') && value.ends_with('\"') && value.len() >= 2 {
        Ok(value[1..value.len() - 1].to_string())
    } else {
        Ok(value)
    }
}

pub(super) fn parse_vm_acquire_stmt(
    pair: pest::iterators::Pair<Rule>,
    input: &str,
) -> std::result::Result<Statement, ParseError> {
    let span = pair.as_span();
    let mut inner = pair.into_inner();
    let layer_pair = inner.next().ok_or_else(|| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "acquire is missing layer".to_string(),
    })?;
    let dst_pair = inner.next().ok_or_else(|| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "acquire is missing destination token".to_string(),
    })?;
    Ok(Statement::VmCoreOp {
        op: VmCoreOp::Acquire {
            layer: parse_vm_layer(layer_pair, input)?,
            dst: dst_pair.as_str().to_string(),
        },
    })
}

pub(super) fn parse_vm_release_stmt(
    pair: pest::iterators::Pair<Rule>,
    input: &str,
) -> std::result::Result<Statement, ParseError> {
    let span = pair.as_span();
    let mut inner = pair.into_inner();
    let layer_pair = inner.next().ok_or_else(|| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "release is missing layer".to_string(),
    })?;
    let evidence_pair = inner.next().ok_or_else(|| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "release is missing evidence token".to_string(),
    })?;
    Ok(Statement::VmCoreOp {
        op: VmCoreOp::Release {
            layer: parse_vm_layer(layer_pair, input)?,
            evidence: evidence_pair.as_str().to_string(),
        },
    })
}

pub(super) fn parse_vm_fork_stmt(
    pair: pest::iterators::Pair<Rule>,
    input: &str,
) -> std::result::Result<Statement, ParseError> {
    let span = pair.as_span();
    let mut inner = pair.into_inner();
    let ghost_pair = inner.next().ok_or_else(|| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "fork is missing ghost token".to_string(),
    })?;
    Ok(Statement::VmCoreOp {
        op: VmCoreOp::Fork {
            ghost: ghost_pair.as_str().to_string(),
        },
    })
}

pub(super) fn parse_vm_join_stmt() -> std::result::Result<Statement, ParseError> {
    Ok(Statement::VmCoreOp { op: VmCoreOp::Join })
}

pub(super) fn parse_vm_abort_stmt() -> std::result::Result<Statement, ParseError> {
    Ok(Statement::VmCoreOp {
        op: VmCoreOp::Abort,
    })
}

pub(super) fn parse_vm_transfer_stmt(
    pair: pest::iterators::Pair<Rule>,
    input: &str,
) -> std::result::Result<Statement, ParseError> {
    let span = pair.as_span();
    let mut inner = pair.into_inner();
    let endpoint_pair = inner.next().ok_or_else(|| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "transfer is missing endpoint token".to_string(),
    })?;
    let target_pair = inner.next().ok_or_else(|| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "transfer is missing target token".to_string(),
    })?;
    let bundle = inner.next().map(|p| p.as_str().to_string());

    Ok(Statement::VmCoreOp {
        op: VmCoreOp::Transfer {
            endpoint: endpoint_pair.as_str().to_string(),
            target: target_pair.as_str().to_string(),
            bundle,
        },
    })
}

pub(super) fn parse_vm_tag_stmt(
    pair: pest::iterators::Pair<Rule>,
    input: &str,
) -> std::result::Result<Statement, ParseError> {
    let span = pair.as_span();
    let mut inner = pair.into_inner();
    let fact_pair = inner.next().ok_or_else(|| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "tag is missing fact token".to_string(),
    })?;
    let dst_pair = inner.next().ok_or_else(|| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "tag is missing destination token".to_string(),
    })?;

    Ok(Statement::VmCoreOp {
        op: VmCoreOp::Tag {
            fact: fact_pair.as_str().to_string(),
            dst: dst_pair.as_str().to_string(),
        },
    })
}

pub(super) fn parse_vm_check_stmt(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
) -> std::result::Result<Statement, ParseError> {
    let span = pair.as_span();
    let mut inner = pair.into_inner();
    let knowledge_pair = inner.next().ok_or_else(|| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "check is missing knowledge token".to_string(),
    })?;
    let target_pair = inner.next().ok_or_else(|| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "check is missing target role".to_string(),
    })?;
    let dst_pair = inner.next().ok_or_else(|| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "check is missing destination token".to_string(),
    })?;
    let target_role = parse_role_ref(target_pair, declared_roles, input)?;

    Ok(Statement::VmCoreOp {
        op: VmCoreOp::Check {
            knowledge: knowledge_pair.as_str().to_string(),
            target_role: target_role.name().to_string(),
            dst: dst_pair.as_str().to_string(),
        },
    })
}
