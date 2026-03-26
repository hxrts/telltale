//! Role parsing utilities.
//!
//! This module handles parsing of role declarations, role references,
//! role parameters, role indices, and range expressions.

use crate::ast::{RangeExpr, Role, RoleIndex, RoleParam};
use quote::format_ident;
use std::collections::HashSet;

use super::error::{ErrorSpan, ParseError};
use super::Rule;

/// Parse a role parameter using enhanced syntax
pub(crate) fn parse_role_param(
    pair: pest::iterators::Pair<Rule>,
    _role_name: &str,
    input: &str,
) -> std::result::Result<RoleParam, ParseError> {
    let span = pair.as_span();
    let mut inner = pair.into_inner();
    let param_expr = inner.next().ok_or_else(|| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "Invalid role parameter: missing parameter expression".to_string(),
    })?;

    match param_expr.as_rule() {
        Rule::role_param_expr => {
            // Check the content of the param_expr directly
            let param_content_str = param_expr.as_str().trim();

            if param_content_str == "*" {
                // Runtime parameter
                Ok(RoleParam::Runtime)
            } else if let Ok(count) = param_content_str.parse::<u32>() {
                // Static count parameter
                RoleParam::safe_static(count).map_err(|e| ParseError::Syntax {
                    span: ErrorSpan::from_pest_span(param_expr.as_span(), input),
                    message: format!("Role parameter validation failed: {}", e),
                })
            } else {
                // Symbolic parameter (identifier)
                Ok(RoleParam::Symbolic(param_content_str.to_string()))
            }
        }
        _ => Err(ParseError::Syntax {
            span: ErrorSpan::from_pest_span(param_expr.as_span(), input),
            message: "Invalid role parameter expression".to_string(),
        }),
    }
}

/// Create a role validation error from a Pest span
pub(crate) fn role_validation_error(
    span: pest::Span<'_>,
    input: &str,
    error: crate::ast::RoleValidationError,
) -> ParseError {
    ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: format!("Role validation failed: {}", error),
    }
}

/// Parse a role index using enhanced syntax
pub(crate) fn parse_role_index(
    pair: pest::iterators::Pair<Rule>,
    _role_name: &str,
    input: &str,
) -> std::result::Result<RoleIndex, ParseError> {
    let span = pair.as_span();
    let mut inner = pair.into_inner();
    let index_expr = inner.next().ok_or_else(|| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "Invalid role index: missing index expression".to_string(),
    })?;

    match index_expr.as_rule() {
        Rule::role_index_expr => {
            let index_content_str = index_expr.as_str().trim();
            let index_span = index_expr.as_span();
            if let Some(index_content) = index_expr.into_inner().next() {
                match index_content.as_rule() {
                    Rule::integer => {
                        let index = index_content.as_str().parse::<u32>().map_err(|_| {
                            ParseError::Syntax {
                                span: ErrorSpan::from_pest_span(index_content.as_span(), input),
                                message: "Invalid integer in role index".to_string(),
                            }
                        })?;

                        // Use safe constructor with overflow checking
                        RoleIndex::safe_concrete(index).map_err(|e| ParseError::Syntax {
                            span: ErrorSpan::from_pest_span(index_content.as_span(), input),
                            message: format!("Role index validation failed: {}", e),
                        })
                    }
                    Rule::ident => {
                        // Symbolic index like Worker[i]
                        let symbolic_name = index_content.as_str().to_string();
                        Ok(RoleIndex::Symbolic(symbolic_name))
                    }
                    Rule::range_expr => parse_range_expr(index_content, input),
                    _ => {
                        // Check for "*" wildcard
                        let content_str = index_content.as_str();
                        if content_str == "*" {
                            Ok(RoleIndex::Wildcard)
                        } else {
                            Err(ParseError::Syntax {
                                span: ErrorSpan::from_pest_span(index_content.as_span(), input),
                                message: format!("Invalid role index: {}", content_str),
                            })
                        }
                    }
                }
            } else {
                // Handle terminal rules like "*" by checking the content directly
                if index_content_str == "*" {
                    Ok(RoleIndex::Wildcard)
                } else {
                    Err(ParseError::Syntax {
                        span: ErrorSpan::from_pest_span(index_span, input),
                        message: format!("Invalid role index: {}", index_content_str),
                    })
                }
            }
        }
        _ => Err(ParseError::Syntax {
            span: ErrorSpan::from_pest_span(index_expr.as_span(), input),
            message: "Invalid role index expression".to_string(),
        }),
    }
}

/// Parse a range expression (e.g., 0..3, i..N)
pub(crate) fn parse_range_expr(
    pair: pest::iterators::Pair<Rule>,
    input: &str,
) -> std::result::Result<RoleIndex, ParseError> {
    use crate::ast::RoleRange;

    let pair_span = pair.as_span();
    let mut inner = pair.into_inner();
    let start_expr = inner.next().ok_or_else(|| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(pair_span, input),
        message: "Invalid range expression: missing start expression".to_string(),
    })?;
    let end_expr = inner.next().ok_or_else(|| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(pair_span, input),
        message: "Invalid range expression: missing end expression".to_string(),
    })?;

    let start = match start_expr.as_rule() {
        Rule::integer => {
            let value = start_expr
                .as_str()
                .parse::<u32>()
                .map_err(|_| ParseError::Syntax {
                    span: ErrorSpan::from_pest_span(start_expr.as_span(), input),
                    message: "Invalid integer in range start".to_string(),
                })?;
            RangeExpr::Concrete(value)
        }
        Rule::ident => RangeExpr::Symbolic(start_expr.as_str().to_string()),
        _ => {
            return Err(ParseError::Syntax {
                span: ErrorSpan::from_pest_span(start_expr.as_span(), input),
                message: "Invalid range start expression".to_string(),
            })
        }
    };

    let end = match end_expr.as_rule() {
        Rule::integer => {
            let value = end_expr
                .as_str()
                .parse::<u32>()
                .map_err(|_| ParseError::Syntax {
                    span: ErrorSpan::from_pest_span(end_expr.as_span(), input),
                    message: "Invalid integer in range end".to_string(),
                })?;
            RangeExpr::Concrete(value)
        }
        Rule::ident => RangeExpr::Symbolic(end_expr.as_str().to_string()),
        _ => {
            return Err(ParseError::Syntax {
                span: ErrorSpan::from_pest_span(end_expr.as_span(), input),
                message: "Invalid range end expression".to_string(),
            })
        }
    };

    let range = RoleRange { start, end };

    // Validate the range
    range.validate().map_err(|e| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(pair_span, input),
        message: format!("Range validation failed: {}", e),
    })?;

    Ok(RoleIndex::Range(range))
}

/// Parse a role reference (e.g., A, Worker[0], Worker[i])
pub(crate) fn parse_role_ref(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
) -> std::result::Result<Role, ParseError> {
    let span = pair.as_span();
    let mut inner = pair.into_inner();

    let role_ident = inner.next().ok_or_else(|| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "Invalid role reference: missing role identifier".to_string(),
    })?;
    let role_name = role_ident.as_str().trim();

    // Check if the base role name is declared
    if !declared_roles.contains(role_name) {
        return Err(ParseError::UndefinedRole {
            role: role_name.to_string(),
            span: ErrorSpan::from_pest_span(span, input),
        });
    }

    // Check if there's an index
    if let Some(index_pair) = inner.next() {
        if index_pair.as_rule() == Rule::role_index {
            // Parse the enhanced index syntax
            let index = parse_role_index(index_pair, role_name, input)?;
            return Role::with_index(format_ident!("{}", role_name), index)
                .map_err(|error| role_validation_error(span, input, error));
        }
    }

    // Simple role without index
    Role::new(format_ident!("{}", role_name))
        .map_err(|error| role_validation_error(span, input, error))
}

/// Parse roles from a Pest pair (roles_decl, header_roles, or role_list)
pub(crate) fn parse_roles_from_pair(
    pair: pest::iterators::Pair<Rule>,
    input: &str,
) -> std::result::Result<Vec<Role>, ParseError> {
    let mut roles = Vec::new();
    let mut declared = HashSet::new();

    let mut role_list_pairs: Vec<pest::iterators::Pair<Rule>> = Vec::new();
    match pair.as_rule() {
        Rule::roles_decl | Rule::header_roles => {
            for inner in pair.into_inner() {
                if inner.as_rule() == Rule::role_list {
                    role_list_pairs.push(inner);
                }
            }
        }
        Rule::role_list => role_list_pairs.push(pair),
        _ => {}
    }

    for role_list in role_list_pairs {
        for role_decl in role_list.into_inner() {
            if let Rule::role_decl = role_decl.as_rule() {
                let role_span = role_decl.as_span();
                let mut inner_role = role_decl.into_inner();
                let role_ident = inner_role.next().ok_or_else(|| ParseError::Syntax {
                    span: ErrorSpan::from_pest_span(role_span, input),
                    message: "Invalid role declaration: missing role identifier".to_string(),
                })?;
                let role_name = role_ident.as_str().trim();
                let span = role_ident.as_span();

                let role = if let Some(param_pair) = inner_role.next() {
                    if param_pair.as_rule() == Rule::role_param {
                        let param = parse_role_param(param_pair, role_name, input)?;
                        Role::with_param(format_ident!("{}", role_name), param)
                    } else {
                        Role::new(format_ident!("{}", role_name))
                    }
                } else {
                    Role::new(format_ident!("{}", role_name))
                }
                .map_err(|error| role_validation_error(span, input, error))?;

                if !declared.insert(role_name.to_string()) {
                    return Err(ParseError::DuplicateRole {
                        role: role_name.to_string(),
                        span: ErrorSpan::from_pest_span(span, input),
                    });
                }

                roles.push(role);
            }
        }
    }

    Ok(roles)
}

#[cfg(test)]
mod tests {
    use super::*;
    use pest::Parser;

    use super::super::ChoreographyParser;

    #[test]
    fn parse_role_param_handles_malformed_pair_without_panicking() {
        let pair = ChoreographyParser::parse(Rule::role_decl, "Worker")
            .expect("parse role_decl")
            .next()
            .expect("role_decl pair");
        let parsed = parse_role_param(pair, "Worker", "Worker");
        assert!(parsed.is_err());
    }

    #[test]
    fn parse_role_ref_handles_non_role_pair_without_panicking() {
        let pair = ChoreographyParser::parse(Rule::role_index, "[0]")
            .expect("parse role_index")
            .next()
            .expect("role_index pair");
        let declared = HashSet::new();
        let parsed = parse_role_ref(pair, &declared, "[0]");
        assert!(parsed.is_err());
    }

    #[test]
    fn parse_range_expr_handles_non_range_pair_without_panicking() {
        let pair = ChoreographyParser::parse(Rule::integer, "7")
            .expect("parse integer")
            .next()
            .expect("integer pair");
        let parsed = parse_range_expr(pair, "7");
        assert!(parsed.is_err());
    }
}
