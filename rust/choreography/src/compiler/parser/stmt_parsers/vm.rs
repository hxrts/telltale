use super::super::error::{ErrorSpan, ParseError};
use super::super::role::parse_role_ref;
use super::super::types::{Statement, VmCoreOp};
use super::super::Rule;
use std::collections::HashSet;

fn parse_vm_layer(
    pair: pest::iterators::Pair<Rule>,
    input: &str,
) -> std::result::Result<String, ParseError> {
    let span = pair.as_span();
    let value = match pair.as_rule() {
        Rule::vm_layer => {
            let inner = pair.into_inner().next().ok_or_else(|| ParseError::Syntax {
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
    if value.starts_with('"') && value.ends_with('"') && value.len() >= 2 {
        Ok(value[1..value.len() - 1].to_string())
    } else {
        Ok(value)
    }
}

pub(crate) fn parse_vm_acquire_stmt(
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

pub(crate) fn parse_vm_release_stmt(
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

pub(crate) fn parse_vm_fork_stmt(
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

pub(crate) fn parse_vm_join_stmt() -> std::result::Result<Statement, ParseError> {
    Ok(Statement::VmCoreOp { op: VmCoreOp::Join })
}

pub(crate) fn parse_vm_abort_stmt() -> std::result::Result<Statement, ParseError> {
    Ok(Statement::VmCoreOp {
        op: VmCoreOp::Abort,
    })
}

pub(crate) fn parse_vm_transfer_stmt(
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

pub(crate) fn parse_vm_tag_stmt(
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

pub(crate) fn parse_vm_check_stmt(
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
