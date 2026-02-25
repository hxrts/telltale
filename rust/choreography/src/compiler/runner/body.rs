use super::*;

#[path = "core.rs"]
mod core;
pub(crate) use core::generate_runner_body;

/// Context for tracking recursion during code generation.
///
/// Used internally to track which recursive labels are currently in scope
/// when generating loop/continue statements.
pub(crate) struct RecursionContext {
    /// Current recursion depth
    depth: usize,
    /// Labels of active recursion points
    labels: Vec<String>,
}

impl RecursionContext {
    /// Create a new empty recursion context.
    pub(crate) fn new() -> Self {
        Self {
            depth: 0,
            labels: Vec::new(),
        }
    }

    fn enter_rec(&mut self, label: &str) {
        self.depth += 1;
        self.labels.push(label.to_string());
    }

    fn exit_rec(&mut self) {
        self.depth -= 1;
        self.labels.pop();
    }

    fn is_in_rec(&self, label: &str) -> bool {
        self.labels.contains(&label.to_string())
    }
}

/// Counters for tracking operation indices during hint-aware code generation.
#[derive(Default)]
pub(crate) struct HintCounters {
    send_count: usize,
    recv_count: usize,
}

/// Generate the body of a runner function from a local type with execution hints.
///
/// This is the hints-aware version that can generate parallel broadcast/collect code.
pub(crate) fn generate_runner_body_with_hints(
    local_type: &LocalType,
    ctx: &mut RecursionContext,
    hints: Option<&ExecutionHints>,
    path: &OperationPath,
    counters: &mut HintCounters,
) -> TokenStream {
    match local_type {
        LocalType::Send {
            to,
            message,
            continuation,
        } => {
            let msg_type = &message.name;
            let current_path = path.push(OperationStep::Send(counters.send_count));
            counters.send_count += 1;

            // Check for parallel hint
            let is_parallel = hints.map(|h| h.is_parallel(&current_path)).unwrap_or(false);

            let cont =
                generate_runner_body_with_hints(continuation, ctx, hints, &current_path, counters);

            // Check if destination is a wildcard or range (multi-destination)
            if let Some(index) = to.index() {
                match index {
                    crate::ast::role::RoleIndex::Wildcard => {
                        let family_name = to.name().to_string();
                        return if is_parallel {
                            // Parallel broadcast using join_all
                            quote! {
                                // Parallel broadcast to all #family_name instances
                                let roles = adapter.resolve_family(#family_name)?;
                                if roles.is_empty() {
                                    return Err(::telltale_choreography::ChoreographyError::EmptyRoleFamily(
                                        #family_name.to_string()
                                    ).into());
                                }
                                let msg: #msg_type = adapter.provide_message(roles[0]).await?;
                                {
                                    use ::futures::future::join_all;
                                    let futures: Vec<_> = roles.iter()
                                        .map(|r| adapter.send(r.clone(), msg.clone()))
                                        .collect();
                                    let results = join_all(futures).await;
                                    for result in results {
                                        result?;
                                    }
                                }
                                #cont
                            }
                        } else {
                            // Sequential broadcast
                            quote! {
                                // Broadcast to all #family_name instances
                                let roles = adapter.resolve_family(#family_name)?;
                                if roles.is_empty() {
                                    return Err(::telltale_choreography::ChoreographyError::EmptyRoleFamily(
                                        #family_name.to_string()
                                    ).into());
                                }
                                let msg: #msg_type = adapter.provide_message(roles[0]).await?;
                                adapter.broadcast(&roles, msg).await?;
                                #cont
                            }
                        };
                    }
                    crate::ast::role::RoleIndex::Range(range) => {
                        let family_name = to.name().to_string();
                        let (start_expr, end_expr) = generate_range_exprs(range);
                        return if is_parallel {
                            // Parallel broadcast to range using join_all
                            quote! {
                                // Parallel broadcast to #family_name range
                                let roles = adapter.resolve_range(#family_name, #start_expr, #end_expr)?;
                                if roles.is_empty() {
                                    return Err(::telltale_choreography::ChoreographyError::EmptyRoleFamily(
                                        #family_name.to_string()
                                    ).into());
                                }
                                let msg: #msg_type = adapter.provide_message(roles[0]).await?;
                                {
                                    use ::futures::future::join_all;
                                    let futures: Vec<_> = roles.iter()
                                        .map(|r| adapter.send(r.clone(), msg.clone()))
                                        .collect();
                                    let results = join_all(futures).await;
                                    for result in results {
                                        result?;
                                    }
                                }
                                #cont
                            }
                        } else {
                            // Sequential broadcast
                            quote! {
                                // Broadcast to #family_name range
                                let roles = adapter.resolve_range(#family_name, #start_expr, #end_expr)?;
                                if roles.is_empty() {
                                    return Err(::telltale_choreography::ChoreographyError::EmptyRoleFamily(
                                        #family_name.to_string()
                                    ).into());
                                }
                                let msg: #msg_type = adapter.provide_message(roles[0]).await?;
                                adapter.broadcast(&roles, msg).await?;
                                #cont
                            }
                        };
                    }
                    _ => {} // Fall through to normal send
                }
            }

            // Normal single-destination send
            let to_role = generate_role_id(to);
            quote! {
                // Send to #to
                let msg: #msg_type = adapter.provide_message(#to_role).await?;
                output.metadata.messages_sent += 1;
                adapter.send(#to_role, msg).await?;
                #cont
            }
        }

        LocalType::Receive {
            from,
            message,
            continuation,
        } => {
            let msg_type = &message.name;
            let current_path = path.push(OperationStep::Recv(counters.recv_count));
            counters.recv_count += 1;

            // Check for parallel and min_responses hints
            let is_parallel = hints.map(|h| h.is_parallel(&current_path)).unwrap_or(false);
            let min_responses = hints.and_then(|h| h.min_responses(&current_path));

            let cont =
                generate_runner_body_with_hints(continuation, ctx, hints, &current_path, counters);

            // Check if source is a wildcard or range (multi-source collect)
            if let Some(index) = from.index() {
                match index {
                    crate::ast::role::RoleIndex::Wildcard => {
                        let family_name = from.name().to_string();
                        return if is_parallel {
                            if let Some(min) = min_responses {
                                // Parallel collect with threshold
                                quote! {
                                    // Parallel collect from all #family_name instances (min: #min)
                                    let roles = adapter.resolve_family(#family_name)?;
                                    if roles.is_empty() {
                                        return Err(::telltale_choreography::ChoreographyError::EmptyRoleFamily(
                                            #family_name.to_string()
                                        ).into());
                                    }
                                    let _msgs: Vec<#msg_type> = {
                                        use ::futures::future::join_all;
                                        let futures: Vec<_> = roles.iter()
                                            .map(|r| adapter.recv::<#msg_type>(r.clone()))
                                            .collect();
                                        let results = join_all(futures).await;
                                        let mut collected = Vec::new();
                                        for result in results {
                                            if let Ok(msg) = result {
                                                collected.push(msg);
                                            }
                                        }
                                        if collected.len() < #min as usize {
                                            return Err(::telltale_choreography::ChoreographyError::InsufficientResponses {
                                                expected: #min as usize,
                                                received: collected.len(),
                                            }.into());
                                        }
                                        collected
                                    };
                                    #cont
                                }
                            } else {
                                // Parallel collect all
                                quote! {
                                    // Parallel collect from all #family_name instances
                                    let roles = adapter.resolve_family(#family_name)?;
                                    if roles.is_empty() {
                                        return Err(::telltale_choreography::ChoreographyError::EmptyRoleFamily(
                                            #family_name.to_string()
                                        ).into());
                                    }
                                    let _msgs: Vec<#msg_type> = {
                                        use ::futures::future::join_all;
                                        let futures: Vec<_> = roles.iter()
                                            .map(|r| adapter.recv::<#msg_type>(r.clone()))
                                            .collect();
                                        let results = join_all(futures).await;
                                        results.into_iter().collect::<Result<Vec<_>, _>>()?
                                    };
                                    #cont
                                }
                            }
                        } else {
                            // Sequential collect
                            quote! {
                                // Collect from all #family_name instances
                                let roles = adapter.resolve_family(#family_name)?;
                                if roles.is_empty() {
                                    return Err(::telltale_choreography::ChoreographyError::EmptyRoleFamily(
                                        #family_name.to_string()
                                    ).into());
                                }
                                let _msgs: Vec<#msg_type> = adapter.collect(&roles).await?;
                                #cont
                            }
                        };
                    }
                    crate::ast::role::RoleIndex::Range(range) => {
                        let family_name = from.name().to_string();
                        let (start_expr, end_expr) = generate_range_exprs(range);
                        return if is_parallel {
                            // Parallel collect from range
                            quote! {
                                // Parallel collect from #family_name range
                                let roles = adapter.resolve_range(#family_name, #start_expr, #end_expr)?;
                                if roles.is_empty() {
                                    return Err(::telltale_choreography::ChoreographyError::EmptyRoleFamily(
                                        #family_name.to_string()
                                    ).into());
                                }
                                let _msgs: Vec<#msg_type> = {
                                    use ::futures::future::join_all;
                                    let futures: Vec<_> = roles.iter()
                                        .map(|r| adapter.recv::<#msg_type>(r.clone()))
                                        .collect();
                                    let results = join_all(futures).await;
                                    results.into_iter().collect::<Result<Vec<_>, _>>()?
                                };
                                #cont
                            }
                        } else {
                            // Sequential collect
                            quote! {
                                // Collect from #family_name range
                                let roles = adapter.resolve_range(#family_name, #start_expr, #end_expr)?;
                                if roles.is_empty() {
                                    return Err(::telltale_choreography::ChoreographyError::EmptyRoleFamily(
                                        #family_name.to_string()
                                    ).into());
                                }
                                let _msgs: Vec<#msg_type> = adapter.collect(&roles).await?;
                                #cont
                            }
                        };
                    }
                    _ => {} // Fall through to normal receive
                }
            }

            // Normal single-source receive
            let from_role = generate_role_id(from);
            quote! {
                // Receive from #from
                let _msg: #msg_type = adapter.recv(#from_role).await?;
                #cont
            }
        }

        // For other cases, delegate to the non-hints version
        _ => generate_runner_body(local_type, ctx),
    }
}

/// Generate the body of a runner function from a local type.
///
/// This produces a `TokenStream` containing the async code that executes
/// the protocol by walking the local type and calling adapter methods
/// (send, recv, choose, offer) as appropriate.
///
/// Used by both `generate_runner_fn` and `typed_runner::generate_typed_runner`.
/// Returns a tuple of (start_expr, end_expr) TokenStreams.
pub(crate) fn generate_range_exprs(
    range: &crate::ast::role::RoleRange,
) -> (TokenStream, TokenStream) {
    use crate::ast::role::RangeExpr;

    let start_expr = match &range.start {
        RangeExpr::Concrete(n) => quote! { #n },
        RangeExpr::Symbolic(var) => {
            let var_ident = format_ident!("{}", var);
            quote! { #var_ident }
        }
    };

    let end_expr = match &range.end {
        RangeExpr::Concrete(n) => quote! { #n },
        RangeExpr::Symbolic(var) => {
            let var_ident = format_ident!("{}", var);
            quote! { #var_ident }
        }
    };

    (start_expr, end_expr)
}

/// Generate a runtime Role expression for a role.
///
/// Converts an AST `Role` to a `TokenStream` that constructs the
/// corresponding runtime role value (e.g., `Role::Alice` or `Role::Worker(0)`).
pub(crate) fn generate_role_id(role: &Role) -> TokenStream {
    use crate::ast::role::RoleIndex;

    let name = role.name();

    if let Some(index) = role.index() {
        match index {
            RoleIndex::Concrete(n) => {
                quote! {
                    Role::#name(#n)
                }
            }
            RoleIndex::Symbolic(var) => {
                // Use a runtime variable
                let var_ident = format_ident!("{}", var);
                quote! {
                    Role::#name(#var_ident)
                }
            }
            RoleIndex::Wildcard => {
                // This should be handled at the Send/Receive level, not here
                // If we reach here, it's a context where wildcards aren't supported
                quote! {{
                    return Err(::telltale_choreography::ChoreographyError::ExecutionError(
                        "wildcard roles in this context should use resolve_family() instead".to_string()
                    ).into());
                }}
            }
            RoleIndex::Range(_) => {
                // This should be handled at the Send/Receive level, not here
                // If we reach here, it's a context where ranges aren't supported
                quote! {{
                    return Err(::telltale_choreography::ChoreographyError::ExecutionError(
                        "range roles in this context should use resolve_range() instead".to_string()
                    ).into());
                }}
            }
        }
    } else if role.param().is_some() {
        // Parameterized role - use the index parameter
        quote! {
            Role::#name(index)
        }
    } else {
        quote! {
            Role::#name
        }
    }
}
