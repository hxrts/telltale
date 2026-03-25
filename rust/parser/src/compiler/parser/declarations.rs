use super::*;
use crate::ast::{
    EffectAuthorityClass, EffectInterfaceDeclaration, EffectOperationDeclaration,
    ExecutionProfileDeclaration, GuestRuntimeDeclaration, OperationDeclaration,
    OperationParameterDeclaration, ProgressAttachment, RegionDeclaration, RoleSetDeclaration,
    TheoremPackDeclaration, TopologyDeclaration, TypeConstructorDeclaration, TypeDeclaration,
};

pub(super) fn enforce_same_line_equals(
    src: &str,
    span: pest::Span<'_>,
    input: &str,
    kind: &str,
) -> std::result::Result<(), ParseError> {
    if let Some(eq_index) = src.find('=') {
        if src[..eq_index].contains('\n') {
            return Err(ParseError::Syntax {
                span: ErrorSpan::from_pest_span(span, input),
                message: format!("{kind} must keep `=` on the same line as the declaration head"),
            });
        }
    }
    Ok(())
}

pub(super) fn parse_protocol_uses(pair: pest::iterators::Pair<Rule>) -> Vec<String> {
    parse_declared_name_list(pair)
}

pub(super) fn parse_protocol_profiles(pair: pest::iterators::Pair<Rule>) -> Vec<String> {
    parse_declared_name_list(pair)
}

fn parse_declared_name_list(pair: pest::iterators::Pair<Rule>) -> Vec<String> {
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
) -> std::result::Result<TheoremPackDeclaration, ParseError> {
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

    Ok(TheoremPackDeclaration {
        name: name_pair.as_str().to_string(),
        capabilities,
        version,
        issuer,
        constraints,
    })
}

pub(super) fn parse_profile_decl(
    pair: pest::iterators::Pair<Rule>,
    input: &str,
) -> std::result::Result<ExecutionProfileDeclaration, ParseError> {
    let span = pair.as_span();
    let mut inner = pair.into_inner();
    let name = inner
        .next()
        .ok_or_else(|| ParseError::Syntax {
            span: ErrorSpan::from_pest_span(span, input),
            message: "profile declaration is missing name".to_string(),
        })?
        .as_str()
        .to_string();
    let mut fairness = None;
    let mut admissibility = None;
    let mut escalation_window = None;

    for item in inner {
        if item.as_rule() != Rule::profile_meta {
            continue;
        }
        let Some(meta) = item.into_inner().next() else {
            continue;
        };
        let rule = meta.as_rule();
        let value = meta
            .into_inner()
            .next()
            .ok_or_else(|| ParseError::Syntax {
                span: ErrorSpan::from_pest_span(span, input),
                message: "profile metadata is missing value".to_string(),
            })?
            .as_str()
            .to_string();
        match rule {
            Rule::profile_fairness => fairness = Some(value),
            Rule::profile_admissibility => admissibility = Some(value),
            Rule::profile_escalation_window => escalation_window = Some(value),
            _ => {}
        }
    }

    Ok(ExecutionProfileDeclaration {
        name,
        fairness,
        admissibility,
        escalation_window,
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
) -> std::result::Result<RoleSetDeclaration, ParseError> {
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

    let mut decl = RoleSetDeclaration {
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
) -> std::result::Result<TopologyDeclaration, ParseError> {
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
    Ok(TopologyDeclaration {
        kind,
        name,
        members,
    })
}

pub(super) fn parse_type_decl(
    pair: pest::iterators::Pair<Rule>,
    input: &str,
) -> std::result::Result<TypeDeclaration, ParseError> {
    let span = pair.as_span();
    enforce_same_line_equals(pair.as_str(), span, input, "type declaration")?;
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
            Ok(TypeDeclaration {
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
                .flat_map(|p| match p.as_rule() {
                    Rule::union_ctor_decl => vec![p],
                    Rule::union_ctor_block => p
                        .into_inner()
                        .filter(|inner| inner.as_rule() == Rule::union_ctor_decl)
                        .collect(),
                    _ => Vec::new(),
                })
                .map(|ctor| {
                    let mut ctor_inner = ctor.into_inner();
                    let name = ctor_inner
                        .next()
                        .map(|p| p.as_str().to_string())
                        .unwrap_or_default();
                    let payload_type = ctor_inner.next().map(|p| {
                        p.into_inner()
                            .next()
                            .map(|inner| inner.as_str().trim().to_string())
                            .unwrap_or_default()
                    });
                    TypeConstructorDeclaration { name, payload_type }
                })
                .collect();
            Ok(TypeDeclaration {
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
) -> std::result::Result<EffectInterfaceDeclaration, ParseError> {
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
                        "authoritative" => EffectAuthorityClass::Authoritative,
                        "observe" => EffectAuthorityClass::Observe,
                        _ => EffectAuthorityClass::Command,
                    };
                    let op_name = op_inner.next().ok_or_else(|| ParseError::Syntax {
                        span: ErrorSpan::from_pest_span(span, input),
                        message: "effect operation is missing name".to_string(),
                    })?;
                    (authority_class, op_name)
                } else {
                    (EffectAuthorityClass::Command, first)
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
            operations.push(EffectOperationDeclaration {
                name: op_name,
                authority_class,
                input_type,
                output_type,
            });
        }
    }
    Ok(EffectInterfaceDeclaration { name, operations })
}

pub(super) fn parse_fragment_decl(
    pair: pest::iterators::Pair<Rule>,
    input: &str,
) -> std::result::Result<RegionDeclaration, ParseError> {
    let span = pair.as_span();
    let mut inner = pair.into_inner();
    let name = inner
        .next()
        .ok_or_else(|| ParseError::Syntax {
            span: ErrorSpan::from_pest_span(span, input),
            message: "fragment declaration is missing name".to_string(),
        })?
        .as_str()
        .to_string();
    let params = inner
        .next()
        .map(|p| {
            p.into_inner()
                .filter(|item| item.as_rule() == Rule::ident)
                .map(|item| item.as_str().to_string())
                .collect()
        })
        .unwrap_or_default();
    Ok(RegionDeclaration { name, params })
}

pub(super) fn parse_progress_attachment(
    pair: pest::iterators::Pair<Rule>,
    input: &str,
) -> std::result::Result<ProgressAttachment, ParseError> {
    let span = pair.as_span();
    let pair = if pair.as_rule() == Rule::operation_progress {
        pair.into_inner().next().ok_or_else(|| ParseError::Syntax {
            span: ErrorSpan::from_pest_span(span, input),
            message: "progress attachment is missing content".to_string(),
        })?
    } else {
        pair
    };
    let span = pair.as_span();
    let mut inner = pair.into_inner();
    let contract_name = inner
        .next()
        .ok_or_else(|| ParseError::Syntax {
            span: ErrorSpan::from_pest_span(span, input),
            message: "progress attachment is missing contract name".to_string(),
        })?
        .as_str()
        .to_string();
    let mut requires_profile = None;
    let mut within_window = None;
    let mut on_timeout = None;
    let mut on_stall = None;

    for item in inner {
        match item.as_rule() {
            Rule::progress_requires => {
                requires_profile = Some(
                    item.into_inner()
                        .next()
                        .ok_or_else(|| ParseError::Syntax {
                            span: ErrorSpan::from_pest_span(span, input),
                            message: "progress requires clause is missing profile name".to_string(),
                        })?
                        .as_str()
                        .to_string(),
                );
            }
            Rule::progress_within => {
                within_window = Some(
                    item.into_inner()
                        .next()
                        .ok_or_else(|| ParseError::Syntax {
                            span: ErrorSpan::from_pest_span(span, input),
                            message: "progress within clause is missing window name".to_string(),
                        })?
                        .as_str()
                        .to_string(),
                );
            }
            Rule::progress_on_timeout => {
                on_timeout = Some(
                    item.into_inner()
                        .next()
                        .ok_or_else(|| ParseError::Syntax {
                            span: ErrorSpan::from_pest_span(span, input),
                            message: "progress on timeout clause is missing branch name"
                                .to_string(),
                        })?
                        .as_str()
                        .to_string(),
                );
            }
            Rule::progress_on_stall => {
                on_stall = Some(
                    item.into_inner()
                        .next()
                        .ok_or_else(|| ParseError::Syntax {
                            span: ErrorSpan::from_pest_span(span, input),
                            message: "progress on stall clause is missing branch name".to_string(),
                        })?
                        .as_str()
                        .to_string(),
                );
            }
            _ => {}
        }
    }

    Ok(ProgressAttachment {
        contract_name,
        requires_profile,
        within_window,
        on_timeout,
        on_stall,
    })
}

pub(super) fn parse_operation_decl(
    pair: pest::iterators::Pair<Rule>,
    input: &str,
) -> std::result::Result<OperationDeclaration, ParseError> {
    let span = pair.as_span();
    enforce_same_line_equals(pair.as_str(), span, input, "operation declaration")?;
    let mut inner = pair.into_inner();
    let name = inner
        .next()
        .ok_or_else(|| ParseError::Syntax {
            span: ErrorSpan::from_pest_span(span, input),
            message: "operation declaration is missing name".to_string(),
        })?
        .as_str()
        .to_string();

    let mut params = Vec::new();
    let mut owner_role = None;
    let mut within = None;
    let mut progress_contract = None;
    let mut composition_policy = None;
    let mut body_source = None;

    for item in inner {
        match item.as_rule() {
            Rule::operation_params => {
                for param in item.into_inner() {
                    if param.as_rule() != Rule::operation_param_decl {
                        continue;
                    }
                    let mut param_inner = param.into_inner();
                    let param_name = param_inner
                        .next()
                        .ok_or_else(|| ParseError::Syntax {
                            span: ErrorSpan::from_pest_span(span, input),
                            message: "operation parameter is missing a name".to_string(),
                        })?
                        .as_str()
                        .to_string();
                    let type_name = param_inner
                        .next()
                        .ok_or_else(|| ParseError::Syntax {
                            span: ErrorSpan::from_pest_span(span, input),
                            message: "operation parameter is missing a type".to_string(),
                        })?
                        .as_str()
                        .trim()
                        .to_string();
                    params.push(OperationParameterDeclaration {
                        name: param_name,
                        type_name,
                    });
                }
            }
            Rule::role_ref => {
                owner_role = Some(item.as_str().trim().to_string());
            }
            Rule::operation_within => {
                let mut within_inner = item.into_inner();
                let fragment_name = within_inner
                    .next()
                    .ok_or_else(|| ParseError::Syntax {
                        span: ErrorSpan::from_pest_span(span, input),
                        message: "operation within clause is missing fragment name".to_string(),
                    })?
                    .as_str()
                    .to_string();
                let args: Vec<String> = within_inner
                    .next()
                    .map(|p| {
                        p.into_inner()
                            .filter(|arg| arg.as_rule() == Rule::ident)
                            .map(|arg| arg.as_str().to_string())
                            .collect()
                    })
                    .unwrap_or_default();
                within = Some(if args.is_empty() {
                    fragment_name
                } else {
                    format!("{}({})", fragment_name, args.join(", "))
                });
            }
            Rule::operation_progress => {
                progress_contract = Some(parse_progress_attachment(item, input)?);
            }
            Rule::operation_compose => {
                composition_policy = Some(
                    item.into_inner()
                        .next()
                        .ok_or_else(|| ParseError::Syntax {
                            span: ErrorSpan::from_pest_span(span, input),
                            message: "operation compose clause is missing policy".to_string(),
                        })?
                        .as_str()
                        .to_string(),
                );
            }
            Rule::protocol_body => {
                body_source = Some(item.as_str().trim().to_string());
            }
            _ => {}
        }
    }

    Ok(OperationDeclaration {
        name,
        params,
        owner_role: owner_role.ok_or_else(|| ParseError::Syntax {
            span: ErrorSpan::from_pest_span(span, input),
            message: "operation declaration is missing owner role".to_string(),
        })?,
        within,
        progress_contract,
        composition_policy,
        body_source: body_source.ok_or_else(|| ParseError::Syntax {
            span: ErrorSpan::from_pest_span(span, input),
            message: "operation declaration is missing body".to_string(),
        })?,
    })
}

pub(super) fn parse_guest_runtime_decl(
    pair: pest::iterators::Pair<Rule>,
    input: &str,
) -> std::result::Result<GuestRuntimeDeclaration, ParseError> {
    let span = pair.as_span();
    enforce_same_line_equals(pair.as_str(), span, input, "guest runtime declaration")?;
    let mut inner = pair.into_inner();
    let name = inner
        .next()
        .ok_or_else(|| ParseError::Syntax {
            span: ErrorSpan::from_pest_span(span, input),
            message: "guest runtime declaration is missing name".to_string(),
        })?
        .as_str()
        .to_string();
    let body = inner.next().ok_or_else(|| ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "guest runtime declaration is missing body".to_string(),
    })?;

    let mut uses = Vec::new();
    let mut entry = None;
    for stmt in body.into_inner() {
        match stmt.as_rule() {
            Rule::guest_runtime_stmt => {
                for inner_stmt in stmt.into_inner() {
                    match inner_stmt.as_rule() {
                        Rule::guest_runtime_uses => {
                            uses = inner_stmt
                                .into_inner()
                                .filter(|p| p.as_rule() == Rule::ident)
                                .map(|p| p.as_str().to_string())
                                .collect();
                        }
                        Rule::guest_runtime_entry => {
                            entry = inner_stmt
                                .into_inner()
                                .find(|p| p.as_rule() == Rule::ident)
                                .map(|p| p.as_str().to_string());
                        }
                        _ => {}
                    }
                }
            }
            Rule::guest_runtime_uses => {
                uses = stmt
                    .into_inner()
                    .filter(|p| p.as_rule() == Rule::ident)
                    .map(|p| p.as_str().to_string())
                    .collect();
            }
            Rule::guest_runtime_entry => {
                entry = stmt
                    .into_inner()
                    .find(|p| p.as_rule() == Rule::ident)
                    .map(|p| p.as_str().to_string());
            }
            _ => {}
        }
    }

    Ok(GuestRuntimeDeclaration {
        name,
        uses,
        entry: entry.ok_or_else(|| ParseError::Syntax {
            span: ErrorSpan::from_pest_span(span, input),
            message: "guest runtime declaration is missing entry".to_string(),
        })?,
    })
}
