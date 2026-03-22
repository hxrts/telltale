use super::*;
use crate::ast::{EffectOpAuthorityClass, EffectOpDecl, TypeConstructorDecl};

pub(super) fn parse_protocol_uses(pair: pest::iterators::Pair<Rule>) -> Vec<String> {
    pair.into_inner()
        .filter(|p| p.as_rule() == Rule::ident)
        .map(|p| p.as_str().to_string())
        .collect()
}

pub(super) fn parse_module_decl(
    pair: pest::iterators::Pair<Rule>,
    input: &str,
) -> std::result::Result<String, ParseError> {
    let span = pair.as_span();
    let mut inner = pair.into_inner();
    if let Some(ident) = inner.next() {
        if ident.as_rule() == Rule::ident {
            return Ok(ident.as_str().to_string());
        }
    }
    Err(ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "Invalid module declaration".to_string(),
    })
}

/// Parse a proof-bundle declaration from the AST.
pub(super) fn parse_proof_bundle_decl(
    pair: pest::iterators::Pair<Rule>,
    input: &str,
) -> std::result::Result<ProofBundleDecl, ParseError> {
    let span = pair.as_span();
    let mut inner = pair.into_inner();
    let Some(name_pair) = inner.next() else {
        return Err(ParseError::Syntax {
            span: ErrorSpan::from_pest_span(span, input),
            message: "Invalid proof_bundle declaration".to_string(),
        });
    };
    if name_pair.as_rule() != Rule::ident {
        return Err(ParseError::Syntax {
            span: ErrorSpan::from_pest_span(span, input),
            message: "Invalid proof_bundle name".to_string(),
        });
    }

    let mut capabilities = Vec::new();
    let mut version = None;
    let mut issuer = None;
    let mut constraints = Vec::new();

    for item in inner {
        match item.as_rule() {
            Rule::proof_bundle_meta => {
                let Some(meta) = item.into_inner().next() else {
                    continue;
                };
                match meta.as_rule() {
                    Rule::proof_bundle_version => {
                        let value = meta.into_inner().next().ok_or_else(|| ParseError::Syntax {
                            span: ErrorSpan::from_pest_span(span, input),
                            message: "proof_bundle version is missing value".to_string(),
                        })?;
                        version = Some(parse_quoted_string(value.as_str()).map_err(|message| {
                            ParseError::Syntax {
                                span: ErrorSpan::from_pest_span(span, input),
                                message,
                            }
                        })?);
                    }
                    Rule::proof_bundle_issuer => {
                        let value = meta.into_inner().next().ok_or_else(|| ParseError::Syntax {
                            span: ErrorSpan::from_pest_span(span, input),
                            message: "proof_bundle issuer is missing value".to_string(),
                        })?;
                        issuer = Some(parse_quoted_string(value.as_str()).map_err(|message| {
                            ParseError::Syntax {
                                span: ErrorSpan::from_pest_span(span, input),
                                message,
                            }
                        })?);
                    }
                    Rule::proof_bundle_constraint => {
                        let value = meta.into_inner().next().ok_or_else(|| ParseError::Syntax {
                            span: ErrorSpan::from_pest_span(span, input),
                            message: "proof_bundle constraint is missing value".to_string(),
                        })?;
                        constraints.push(parse_quoted_string(value.as_str()).map_err(
                            |message| ParseError::Syntax {
                                span: ErrorSpan::from_pest_span(span, input),
                                message,
                            },
                        )?);
                    }
                    _ => {}
                }
            }
            Rule::proof_bundle_requires => {
                for requires_item in item.into_inner() {
                    if requires_item.as_rule() == Rule::capability_list {
                        for cap in requires_item.into_inner() {
                            if cap.as_rule() == Rule::ident {
                                capabilities.push(cap.as_str().to_string());
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }

    Ok(ProofBundleDecl {
        name: name_pair.as_str().to_string(),
        capabilities,
        version,
        issuer,
        constraints,
    })
}

fn parse_quoted_string(value: &str) -> Result<String, String> {
    if value.starts_with('\"') && value.ends_with('\"') && value.len() >= 2 {
        Ok(value[1..value.len() - 1].to_string())
    } else {
        Err("expected quoted string literal".to_string())
    }
}

/// Parse protocol-level required proof bundles.
pub(super) fn parse_protocol_requires(pair: pest::iterators::Pair<Rule>) -> Vec<String> {
    pair.into_inner()
        .filter(|p| p.as_rule() == Rule::ident)
        .map(|p| p.as_str().to_string())
        .collect()
}

pub(super) fn parse_role_set_decl(
    pair: pest::iterators::Pair<Rule>,
    input: &str,
) -> std::result::Result<RoleSetDecl, ParseError> {
    let span = pair.as_span();
    let mut inner = pair.into_inner();
    let name = inner
        .next()
        .ok_or_else(|| ParseError::Syntax {
            span: ErrorSpan::from_pest_span(span, input),
            message: "role_set is missing name".to_string(),
        })?
        .as_str()
        .to_string();
    let expr = inner.next().ok_or_else(|| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "role_set is missing expression".to_string(),
    })?;

    let mut decl = RoleSetDecl {
        name,
        members: Vec::new(),
        subset_of: None,
        subset_start: None,
        subset_end: None,
    };

    for expr_item in expr.into_inner() {
        match expr_item.as_rule() {
            Rule::role_set_members => {
                decl.members = expr_item
                    .into_inner()
                    .filter(|p| p.as_rule() == Rule::ident)
                    .map(|p| p.as_str().to_string())
                    .collect();
            }
            Rule::role_set_subset => {
                let mut subset_inner = expr_item.into_inner();
                let source = subset_inner.next().ok_or_else(|| ParseError::Syntax {
                    span: ErrorSpan::from_pest_span(span, input),
                    message: "role_set subset is missing source".to_string(),
                })?;
                let start = subset_inner.next().ok_or_else(|| ParseError::Syntax {
                    span: ErrorSpan::from_pest_span(span, input),
                    message: "role_set subset is missing start".to_string(),
                })?;
                let end = subset_inner.next().ok_or_else(|| ParseError::Syntax {
                    span: ErrorSpan::from_pest_span(span, input),
                    message: "role_set subset is missing end".to_string(),
                })?;
                decl.subset_of = Some(source.as_str().to_string());
                decl.subset_start =
                    Some(
                        start
                            .as_str()
                            .parse::<u32>()
                            .map_err(|_| ParseError::Syntax {
                                span: ErrorSpan::from_pest_span(span, input),
                                message: "role_set subset start must be an integer".to_string(),
                            })?,
                    );
                decl.subset_end =
                    Some(
                        end.as_str()
                            .parse::<u32>()
                            .map_err(|_| ParseError::Syntax {
                                span: ErrorSpan::from_pest_span(span, input),
                                message: "role_set subset end must be an integer".to_string(),
                            })?,
                    );
            }
            _ => {}
        }
    }

    Ok(decl)
}

pub(super) fn parse_topology_decl(
    pair: pest::iterators::Pair<Rule>,
    input: &str,
) -> std::result::Result<TopologyDecl, ParseError> {
    let span = pair.as_span();
    let mut inner = pair.into_inner();
    let kind = inner
        .next()
        .ok_or_else(|| ParseError::Syntax {
            span: ErrorSpan::from_pest_span(span, input),
            message: "topology declaration is missing kind".to_string(),
        })?
        .as_str()
        .to_string();
    let name = inner
        .next()
        .ok_or_else(|| ParseError::Syntax {
            span: ErrorSpan::from_pest_span(span, input),
            message: "topology declaration is missing name".to_string(),
        })?
        .as_str()
        .to_string();
    let members_pair = inner.next().ok_or_else(|| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "topology declaration is missing members".to_string(),
    })?;
    let members = members_pair
        .into_inner()
        .filter(|p| p.as_rule() == Rule::ident)
        .map(|p| p.as_str().to_string())
        .collect();
    Ok(TopologyDecl {
        kind,
        name,
        members,
    })
}

pub(super) fn parse_type_decl(
    pair: pest::iterators::Pair<Rule>,
    input: &str,
) -> std::result::Result<TypeDecl, ParseError> {
    let span = pair.as_span();
    let inner = pair.into_inner().next().ok_or_else(|| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "type declaration is empty".to_string(),
    })?;
    match inner.as_rule() {
        Rule::type_alias_decl => {
            let mut alias_inner = inner.into_inner();
            let name = alias_inner
                .next()
                .ok_or_else(|| ParseError::Syntax {
                    span: ErrorSpan::from_pest_span(span, input),
                    message: "type alias is missing name".to_string(),
                })?
                .as_str()
                .to_string();
            let alias_of = alias_inner
                .next()
                .ok_or_else(|| ParseError::Syntax {
                    span: ErrorSpan::from_pest_span(span, input),
                    message: "type alias is missing right-hand side".to_string(),
                })?
                .as_str()
                .trim()
                .to_string();
            Ok(TypeDecl {
                name,
                is_alias: true,
                alias_of: Some(alias_of),
                constructors: Vec::new(),
            })
        }
        Rule::union_type_decl => {
            let mut union_inner = inner.into_inner();
            let name = union_inner
                .next()
                .ok_or_else(|| ParseError::Syntax {
                    span: ErrorSpan::from_pest_span(span, input),
                    message: "type declaration is missing name".to_string(),
                })?
                .as_str()
                .to_string();
            let constructors = union_inner
                .filter(|p| p.as_rule() == Rule::union_ctor_decl)
                .map(|ctor| {
                    let mut ctor_inner = ctor.into_inner();
                    let name = ctor_inner
                        .next()
                        .map(|p| p.as_str().to_string())
                        .unwrap_or_default();
                    let payload_type = ctor_inner.next().map(|p| p.as_str().trim().to_string());
                    TypeConstructorDecl { name, payload_type }
                })
                .collect();
            Ok(TypeDecl {
                name,
                is_alias: false,
                alias_of: None,
                constructors,
            })
        }
        _ => Err(ParseError::Syntax {
            span: ErrorSpan::from_pest_span(span, input),
            message: "unsupported type declaration".to_string(),
        }),
    }
}

pub(super) fn parse_effect_decl(
    pair: pest::iterators::Pair<Rule>,
    input: &str,
) -> std::result::Result<EffectDecl, ParseError> {
    let span = pair.as_span();
    let mut inner = pair.into_inner();
    let name = inner
        .next()
        .ok_or_else(|| ParseError::Syntax {
            span: ErrorSpan::from_pest_span(span, input),
            message: "effect declaration is missing name".to_string(),
        })?
        .as_str()
        .to_string();
    let mut operations = Vec::new();
    for op in inner {
        let op_pairs: Vec<_> = match op.as_rule() {
            Rule::effect_op_decl => vec![op],
            Rule::effect_body => op
                .into_inner()
                .filter(|p| p.as_rule() == Rule::effect_op_decl)
                .collect(),
            _ => Vec::new(),
        };
        for op in op_pairs {
            let mut op_inner = op.into_inner();
            let first = op_inner.next().ok_or_else(|| ParseError::Syntax {
                span: ErrorSpan::from_pest_span(span, input),
                message: "effect operation is missing name".to_string(),
            })?;
            let (authority_class, op_name_pair) =
                if first.as_rule() == Rule::effect_op_authority_class {
                    let authority_class = match first.as_str() {
                        "authoritative" => EffectOpAuthorityClass::Authoritative,
                        "observe" => EffectOpAuthorityClass::Observe,
                        _ => EffectOpAuthorityClass::Command,
                    };
                    let op_name = op_inner.next().ok_or_else(|| ParseError::Syntax {
                        span: ErrorSpan::from_pest_span(span, input),
                        message: "effect operation is missing name".to_string(),
                    })?;
                    (authority_class, op_name)
                } else {
                    (EffectOpAuthorityClass::Command, first)
                };
            let op_name = op_name_pair.as_str().to_string();
            let input_type = op_inner
                .next()
                .ok_or_else(|| ParseError::Syntax {
                    span: ErrorSpan::from_pest_span(span, input),
                    message: "effect operation is missing input type".to_string(),
                })?
                .as_str()
                .trim()
                .to_string();
            let output_type = op_inner
                .next()
                .ok_or_else(|| ParseError::Syntax {
                    span: ErrorSpan::from_pest_span(span, input),
                    message: "effect operation is missing output type".to_string(),
                })?
                .as_str()
                .trim()
                .to_string();
            operations.push(EffectOpDecl {
                name: op_name,
                authority_class,
                input_type,
                output_type,
            });
        }
    }
    Ok(EffectDecl { name, operations })
}
