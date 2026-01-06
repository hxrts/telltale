//! Runner Function Code Generation
//!
//! This module generates `run_{role}` async functions from local type projections.
//! These functions use the `ChoreographicAdapter` trait to execute protocol logic.
//!
//! # Generated Code Structure
//!
//! For a protocol with roles `Client` and `Server`, this generates:
//!
//! ```ignore
//! pub async fn run_client<A: ChoreographicAdapter<Role = Role>>(
//!     adapter: &mut A,
//! ) -> Result<ClientOutput, A::Error> {
//!     // Generated from Client's local type projection
//! }
//!
//! pub async fn run_server<A: ChoreographicAdapter<Role = Role>>(
//!     adapter: &mut A,
//! ) -> Result<ServerOutput, A::Error> {
//!     // Generated from Server's local type projection
//! }
//!
//! pub async fn execute_as<A: ChoreographicAdapter<Role = Role>>(
//!     role: Role,
//!     adapter: &mut A,
//! ) -> Result<ProtocolOutput, A::Error> {
//!     match role {
//!         Role::Client => run_client(adapter).await,
//!         Role::Server => run_server(adapter).await,
//!     }
//! }
//! ```

use crate::ast::{ExecutionHints, LocalType, OperationPath, OperationStep, Role};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use std::collections::BTreeSet;

/// Generate a runner function for a single role.
///
/// # Arguments
///
/// * `protocol_name` - Name of the protocol
/// * `role` - The role to generate a runner for
/// * `local_type` - The projected local type for this role
///
/// # Returns
///
/// A TokenStream containing the `run_{role}` function.
#[must_use]
pub fn generate_runner_fn(protocol_name: &str, role: &Role, local_type: &LocalType) -> TokenStream {
    generate_runner_fn_with_hints(protocol_name, role, local_type, None)
}

/// Generate a runner function for a single role with optional execution hints.
///
/// # Arguments
///
/// * `protocol_name` - Name of the protocol
/// * `role` - The role to generate a runner for
/// * `local_type` - The projected local type for this role
/// * `hints` - Optional execution hints for controlling broadcast/collect behavior
///
/// # Returns
///
/// A TokenStream containing the `run_{role}` function.
#[must_use]
pub fn generate_runner_fn_with_hints(
    protocol_name: &str,
    role: &Role,
    local_type: &LocalType,
    hints: Option<&ExecutionHints>,
) -> TokenStream {
    let role_name = role.name();
    let fn_name = format_ident!("run_{}", role_name.to_string().to_lowercase());
    let output_type = format_ident!("{}Output", role_name);
    let protocol_str = protocol_name;
    let role_variant = if role.index().is_some() || role.param().is_some() {
        quote! { Role::#role_name(index) }
    } else {
        quote! { Role::#role_name }
    };

    // Generate the function body from local type
    let body = generate_runner_body_with_hints(
        local_type,
        &mut RecursionContext::new(),
        hints,
        &OperationPath::new(),
        &mut HintCounters::default(),
    );

    // Determine if this role is indexed
    let (fn_signature, ctx_creation) = if role.index().is_some() || role.param().is_some() {
        // Indexed role - add index parameter
        (
            quote! {
                pub async fn #fn_name<A: ChoreographicAdapter<Role = Role>>(
                    adapter: &mut A,
                    index: u32,
                ) -> Result<#output_type, A::Error>
                where
                    A::Error: From<::rumpsteak_aura_choreography::ChoreographyError>
            },
            quote! {
                let _ctx = ProtocolContext::for_role(#protocol_str, #role_variant);
            },
        )
    } else {
        // Static role
        (
            quote! {
                pub async fn #fn_name<A: ChoreographicAdapter<Role = Role>>(
                    adapter: &mut A,
                ) -> Result<#output_type, A::Error>
                where
                    A::Error: From<::rumpsteak_aura_choreography::ChoreographyError>
            },
            quote! {
                let _ctx = ProtocolContext::for_role(#protocol_str, #role_variant);
            },
        )
    };

    quote! {
        #fn_signature {
            #ctx_creation

            #body

            Ok(#output_type::default())
        }
    }
}

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
struct HintCounters {
    send_count: usize,
    recv_count: usize,
}

/// Generate the body of a runner function from a local type with execution hints.
///
/// This is the hints-aware version that can generate parallel broadcast/collect code.
fn generate_runner_body_with_hints(
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
                                    return Err(::rumpsteak_aura_choreography::ChoreographyError::EmptyRoleFamily(
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
                                    return Err(::rumpsteak_aura_choreography::ChoreographyError::EmptyRoleFamily(
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
                                    return Err(::rumpsteak_aura_choreography::ChoreographyError::EmptyRoleFamily(
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
                                    return Err(::rumpsteak_aura_choreography::ChoreographyError::EmptyRoleFamily(
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
                                        return Err(::rumpsteak_aura_choreography::ChoreographyError::EmptyRoleFamily(
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
                                            return Err(::rumpsteak_aura_choreography::ChoreographyError::InsufficientResponses {
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
                                        return Err(::rumpsteak_aura_choreography::ChoreographyError::EmptyRoleFamily(
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
                                    return Err(::rumpsteak_aura_choreography::ChoreographyError::EmptyRoleFamily(
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
                                    return Err(::rumpsteak_aura_choreography::ChoreographyError::EmptyRoleFamily(
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
                                    return Err(::rumpsteak_aura_choreography::ChoreographyError::EmptyRoleFamily(
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
pub(crate) fn generate_runner_body(
    local_type: &LocalType,
    ctx: &mut RecursionContext,
) -> TokenStream {
    match local_type {
        LocalType::Send {
            to,
            message,
            continuation,
        } => {
            let msg_type = &message.name;
            let cont = generate_runner_body(continuation, ctx);

            // Check if destination is a wildcard or range (multi-destination)
            if let Some(index) = to.index() {
                match index {
                    crate::ast::role::RoleIndex::Wildcard => {
                        // Generate broadcast to all instances of the role family
                        let family_name = to.name().to_string();
                        return quote! {
                            // Broadcast to all #family_name instances
                            let roles = adapter.resolve_family(#family_name)?;
                            if roles.is_empty() {
                                return Err(::rumpsteak_aura_choreography::ChoreographyError::EmptyRoleFamily(
                                    #family_name.to_string()
                                ).into());
                            }
                            let msg: #msg_type = adapter.provide_message(roles[0]).await?;
                            adapter.broadcast(&roles, msg).await?;
                            #cont
                        };
                    }
                    crate::ast::role::RoleIndex::Range(range) => {
                        // Generate broadcast to a range of role instances
                        let family_name = to.name().to_string();
                        let (start_expr, end_expr) = generate_range_exprs(range);
                        return quote! {
                            // Broadcast to #family_name range
                            let roles = adapter.resolve_range(#family_name, #start_expr, #end_expr)?;
                            if roles.is_empty() {
                                return Err(::rumpsteak_aura_choreography::ChoreographyError::EmptyRoleFamily(
                                    #family_name.to_string()
                                ).into());
                            }
                            let msg: #msg_type = adapter.provide_message(roles[0]).await?;
                            adapter.broadcast(&roles, msg).await?;
                            #cont
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
            let cont = generate_runner_body(continuation, ctx);

            // Check if source is a wildcard or range (multi-source collect)
            if let Some(index) = from.index() {
                match index {
                    crate::ast::role::RoleIndex::Wildcard => {
                        // Generate collect from all instances of the role family
                        let family_name = from.name().to_string();
                        return quote! {
                            // Collect from all #family_name instances
                            let roles = adapter.resolve_family(#family_name)?;
                            if roles.is_empty() {
                                return Err(::rumpsteak_aura_choreography::ChoreographyError::EmptyRoleFamily(
                                    #family_name.to_string()
                                ).into());
                            }
                            let _msgs: Vec<#msg_type> = adapter.collect(&roles).await?;
                            #cont
                        };
                    }
                    crate::ast::role::RoleIndex::Range(range) => {
                        // Generate collect from a range of role instances
                        let family_name = from.name().to_string();
                        let (start_expr, end_expr) = generate_range_exprs(range);
                        return quote! {
                            // Collect from #family_name range
                            let roles = adapter.resolve_range(#family_name, #start_expr, #end_expr)?;
                            if roles.is_empty() {
                                return Err(::rumpsteak_aura_choreography::ChoreographyError::EmptyRoleFamily(
                                    #family_name.to_string()
                                ).into());
                            }
                            let _msgs: Vec<#msg_type> = adapter.collect(&roles).await?;
                            #cont
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

        LocalType::Select { to, branches } => {
            let to_role = generate_role_id(to);

            // Generate match arms for each branch
            let match_arms: Vec<TokenStream> = branches
                .iter()
                .map(|(label, cont_type)| {
                    let cont = generate_runner_body(cont_type, ctx);
                    quote! {
                        BranchLabel::#label => {
                            adapter.choose(#to_role, BranchLabel::#label).await?;
                            #cont
                        }
                    }
                })
                .collect();

            let choice_variants: Vec<TokenStream> = branches
                .iter()
                .map(|(label, _)| {
                    quote! { BranchLabel::#label }
                })
                .collect();

            quote! {
                // Internal choice - select branch to send to #to
                let choice = adapter.select_branch(&[#(#choice_variants),*]).await?;
                match choice {
                    #(#match_arms)*
                }
            }
        }

        LocalType::Branch { from, branches } => {
            let from_role = generate_role_id(from);

            // Generate match arms for each branch
            let match_arms: Vec<TokenStream> = branches
                .iter()
                .map(|(label, cont_type)| {
                    let cont = generate_runner_body(cont_type, ctx);
                    quote! {
                        BranchLabel::#label => {
                            #cont
                        }
                    }
                })
                .collect();

            quote! {
                // External choice - receive branch selection from #from
                let label = adapter.offer(#from_role).await?;
                match label {
                    #(#match_arms)*
                }
            }
        }

        LocalType::LocalChoice { branches } => {
            // Generate match arms for each branch
            let match_arms: Vec<TokenStream> = branches
                .iter()
                .map(|(label, cont_type)| {
                    let cont = generate_runner_body(cont_type, ctx);
                    quote! {
                        BranchLabel::#label => {
                            #cont
                        }
                    }
                })
                .collect();

            let choice_variants: Vec<TokenStream> = branches
                .iter()
                .map(|(label, _)| {
                    quote! { BranchLabel::#label }
                })
                .collect();

            quote! {
                // Local choice - no communication
                let choice = adapter.select_branch(&[#(#choice_variants),*]).await?;
                match choice {
                    #(#match_arms)*
                }
            }
        }

        LocalType::Loop { condition, body } => {
            let loop_body = generate_runner_body(body, ctx);

            match condition {
                Some(crate::ast::Condition::Count(n)) => {
                    quote! {
                        // Bounded loop (max #n iterations)
                        for _i in 0..#n {
                            #loop_body
                        }
                    }
                }
                Some(crate::ast::Condition::RoleDecides(role)) => {
                    // Note: RoleDecides loops are normally desugared to choice+rec at parse time.
                    // This case is only reached if someone constructs a LocalType::Loop with
                    // RoleDecides directly, bypassing the normal parse/desugar path.
                    let role_str = role.name().to_string();
                    quote! {
                        return Err(::rumpsteak_aura_choreography::ChoreographyError::ExecutionError(
                            format!(
                                "role-decided loops are not supported directly in generated runners. \
                                 The parser should desugar 'loop decide by {}' to a choice+rec pattern. \
                                 If you see this error, the LocalType was constructed without going \
                                 through the normal parse path.",
                                #role_str
                            )
                        ).into());
                    }
                }
                Some(crate::ast::Condition::Custom(expr)) => {
                    quote! {
                        // Loop with custom condition
                        while #expr {
                            #loop_body
                        }
                    }
                }
                Some(crate::ast::Condition::Fuel(n)) => {
                    quote! {
                        // Fuel-bounded loop (max #n iterations)
                        for _fuel in 0..#n {
                            #loop_body
                        }
                    }
                }
                Some(crate::ast::Condition::YieldAfter(n)) => {
                    quote! {
                        // Yield-after-N loop (max #n steps then yield)
                        for _step in 0..#n {
                            #loop_body
                        }
                        // Yield control after N steps
                    }
                }
                Some(crate::ast::Condition::YieldWhen(condition)) => {
                    quote! {
                        // Yield-when loop
                        loop {
                            #loop_body
                            // Check yield condition
                            let _condition = #condition;
                            break; // Yield when condition met
                        }
                    }
                }
                None => {
                    quote! {
                        return Err(::rumpsteak_aura_choreography::ChoreographyError::ExecutionError(
                            "unbounded loops are not supported in generated runners. \
                             Use a bounded loop condition like: \
                             'loop decide by Role' (desugars to choice), \
                             'loop repeat N' (fixed iterations), \
                             'loop fuel N' (max iterations), or \
                             'loop yield_after N' (bounded steps)".to_string()
                        ).into());
                    }
                }
            }
        }

        LocalType::Rec { label, body } => {
            let label_str = label.to_string();

            // Track recursion
            ctx.enter_rec(&label_str);
            let rec_body = generate_runner_body(body, ctx);
            ctx.exit_rec();

            let loop_label = syn::Lifetime::new(
                &format!("'rec_{}", label_str),
                proc_macro2::Span::call_site(),
            );

            quote! {
                // Recursive type
                #loop_label: loop {
                    #rec_body
                    break #loop_label;
                }
            }
        }

        LocalType::Var(label) => {
            let label_str = label.to_string();
            let loop_label = syn::Lifetime::new(
                &format!("'rec_{}", label_str),
                proc_macro2::Span::call_site(),
            );

            if ctx.is_in_rec(&label_str) {
                quote! {
                    // Continue recursive loop
                    continue #loop_label;
                }
            } else {
                quote! {
                    // Recursive variable (unbound) - this indicates a code generator bug
                    // The variable should have been bound by a Mu construct
                    return Err(::rumpsteak_aura_choreography::ChoreographyError::ExecutionError(
                        format!(
                            "unbound recursive variable '{}'; this indicates a code generator bug",
                            #label_str
                        )
                    ).into());
                }
            }
        }

        LocalType::Timeout { duration, body } => {
            let timeout_ms = duration.as_millis() as u64;
            let timeout_body = generate_runner_body(body, ctx);

            quote! {
                // Timeout after #duration ms
                let timeout_result = tokio::time::timeout(
                    std::time::Duration::from_millis(#timeout_ms),
                    async {
                        #timeout_body
                        Ok::<_, A::Error>(())
                    }
                ).await;

                match timeout_result {
                    Ok(inner_result) => inner_result?,
                    Err(_elapsed) => {
                        return Err(::rumpsteak_aura_choreography::ChoreographyError::Timeout(
                            std::time::Duration::from_millis(#timeout_ms),
                        )
                        .into());
                    }
                }
            }
        }

        LocalType::End => {
            quote! {
                // End of protocol
            }
        }
    }
}

/// Generate TokenStream expressions for a role range.
///
/// Returns a tuple of (start_expr, end_expr) TokenStreams.
fn generate_range_exprs(range: &crate::ast::role::RoleRange) -> (TokenStream, TokenStream) {
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
                    return Err(::rumpsteak_aura_choreography::ChoreographyError::ExecutionError(
                        "wildcard roles in this context should use resolve_family() instead".to_string()
                    ).into());
                }}
            }
            RoleIndex::Range(_) => {
                // This should be handled at the Send/Receive level, not here
                // If we reach here, it's a context where ranges aren't supported
                quote! {{
                    return Err(::rumpsteak_aura_choreography::ChoreographyError::ExecutionError(
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

/// Generate the `execute_as` dispatch function.
///
/// This function routes execution to the appropriate `run_{role}` function
/// based on a runtime role value.
#[must_use]
pub fn generate_execute_as(
    _protocol_name: &str,
    roles: &[Role],
    _local_types: &[(Role, LocalType)],
) -> TokenStream {
    // Generate match arms
    let match_arms: Vec<TokenStream> = roles
        .iter()
        .map(|role| {
            let name = role.name();
            let fn_name = format_ident!("run_{}", name.to_string().to_lowercase());

            if role.index().is_some() || role.param().is_some() {
                quote! {
                    Role::#name(index) => {
                        #fn_name(adapter, index).await?;
                    }
                }
            } else {
                quote! {
                    Role::#name => {
                        #fn_name(adapter).await?;
                    }
                }
            }
        })
        .collect();

    quote! {
        /// Execute the protocol as a specific role.
        ///
        /// This function dispatches to the appropriate `run_{role}` function
        /// based on the provided role.
        pub async fn execute_as<A: ChoreographicAdapter<Role = Role>>(
            role: Role,
            adapter: &mut A,
        ) -> Result<(), A::Error>
        where
            A::Error: From<::rumpsteak_aura_choreography::ChoreographyError>
        {
            match role {
                #(#match_arms)*
            }

            Ok(())
        }
    }
}

/// Generate output type structs for each role.
#[must_use]
pub fn generate_output_types(roles: &[Role]) -> TokenStream {
    let output_structs: Vec<TokenStream> = roles
        .iter()
        .map(|role| {
            let name = role.name();
            let output_name = format_ident!("{}Output", name);

            // TODO(output-fields): Output structs should contain fields for:
            // - Final values of received messages
            // - Computed results from protocol execution
            // - Choice paths taken (for protocols with branching)
            // Currently empty - users get no data back from protocol execution.
            quote! {
                /// Output from running the #name role
                #[derive(Debug, Default)]
                pub struct #output_name {
                    // Fields will be added based on protocol structure
                }
            }
        })
        .collect();

    quote! {
        #(#output_structs)*
    }
}

/// Generate all runner code for a choreography.
///
/// This includes:
/// - Output types for each role
/// - `run_{role}` functions for each role
/// - `execute_as` dispatch function
/// - Role enum for runtime dispatch
#[must_use]
pub fn generate_all_runners(
    protocol_name: &str,
    roles: &[Role],
    local_types: &[(Role, LocalType)],
) -> TokenStream {
    let mut label_names = BTreeSet::new();
    for (_, local_type) in local_types {
        collect_branch_labels(local_type, &mut label_names);
    }

    let branch_label_enum = generate_branch_label_enum(&label_names);
    let role_enum = generate_runtime_role_enum(roles);
    let output_types = generate_output_types(roles);

    let runner_fns: Vec<TokenStream> = local_types
        .iter()
        .map(|(role, local_type)| generate_runner_fn(protocol_name, role, local_type))
        .collect();

    let execute_as = generate_execute_as(protocol_name, roles, local_types);

    quote! {
        #branch_label_enum
        #role_enum

        /// Generated runner functions for protocol execution
        #[allow(dead_code, unused_imports, unused_variables)]
        pub mod runners {
            use super::*;
            use ::rumpsteak_aura_choreography::{ChoreographicAdapter, LabelId, ProtocolContext};

            #output_types

            #(#runner_fns)*

            #execute_as
        }
    }
}

fn collect_branch_labels(local_type: &LocalType, labels: &mut BTreeSet<String>) {
    match local_type {
        LocalType::Select { branches, .. }
        | LocalType::Branch { branches, .. }
        | LocalType::LocalChoice { branches } => {
            for (label, branch) in branches {
                labels.insert(label.to_string());
                collect_branch_labels(branch, labels);
            }
        }
        LocalType::Send { continuation, .. }
        | LocalType::Receive { continuation, .. }
        | LocalType::Loop {
            body: continuation, ..
        }
        | LocalType::Rec {
            body: continuation, ..
        }
        | LocalType::Timeout {
            body: continuation, ..
        } => {
            collect_branch_labels(continuation, labels);
        }
        LocalType::Var(_) | LocalType::End => {}
    }
}

fn generate_branch_label_enum(labels: &BTreeSet<String>) -> TokenStream {
    if labels.is_empty() {
        return quote! {
            #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
            pub enum BranchLabel {}

            impl ::rumpsteak_aura_choreography::LabelId for BranchLabel {
                fn as_str(&self) -> &'static str {
                    match *self {}
                }

                fn from_str(_label: &str) -> Option<Self> {
                    None
                }
            }
        };
    }

    let variants = labels.iter().map(|label| {
        let ident = format_ident!("{}", label);
        quote! { #ident }
    });

    let as_str_arms = labels.iter().map(|label| {
        let ident = format_ident!("{}", label);
        quote! { BranchLabel::#ident => #label }
    });

    let from_str_arms = labels.iter().map(|label| {
        let ident = format_ident!("{}", label);
        quote! { #label => Some(BranchLabel::#ident) }
    });

    quote! {
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
        pub enum BranchLabel {
            #(#variants),*
        }

        impl ::rumpsteak_aura_choreography::LabelId for BranchLabel {
            fn as_str(&self) -> &'static str {
                match self {
                    #(#as_str_arms),*
                }
            }

            fn from_str(label: &str) -> Option<Self> {
                match label {
                    #(#from_str_arms),*,
                    _ => None,
                }
            }
        }
    }
}

fn generate_runtime_role_enum(roles: &[Role]) -> TokenStream {
    let role_variants: Vec<TokenStream> = roles
        .iter()
        .map(|role| {
            let name = role.name();
            if role.index().is_some() || role.param().is_some() {
                quote! { #name(u32) }
            } else {
                quote! { #name }
            }
        })
        .collect();

    let role_name_arms: Vec<TokenStream> = roles
        .iter()
        .map(|role| {
            let name = role.name();
            let role_str = role.name().to_string();
            if role.index().is_some() || role.param().is_some() {
                quote! {
                    Role::#name(_) => ::rumpsteak_aura_choreography::RoleName::from_static(#role_str)
                }
            } else {
                quote! {
                    Role::#name => ::rumpsteak_aura_choreography::RoleName::from_static(#role_str)
                }
            }
        })
        .collect();

    let role_index_arms: Vec<TokenStream> = roles
        .iter()
        .map(|role| {
            let name = role.name();
            if role.index().is_some() || role.param().is_some() {
                quote! { Role::#name(index) => Some(*index) }
            } else {
                quote! { Role::#name => None }
            }
        })
        .collect();

    quote! {
        /// Runtime role identifier for protocol dispatch and adapters.
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
        pub enum Role {
            #(#role_variants),*
        }

        impl ::rumpsteak_aura_choreography::RoleId for Role {
            type Label = BranchLabel;

            fn role_name(&self) -> ::rumpsteak_aura_choreography::RoleName {
                match self {
                    #(#role_name_arms),*
                }
            }

            fn role_index(&self) -> Option<u32> {
                match self {
                    #(#role_index_arms),*
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::Role;

    fn make_role(name: &str) -> Role {
        Role::new(format_ident!("{}", name)).unwrap()
    }

    #[test]
    fn test_generate_role_id_static() {
        let role = make_role("Client");
        let tokens = generate_role_id(&role);
        let expected = quote! { Role::Client };
        assert_eq!(tokens.to_string(), expected.to_string());
    }

    #[test]
    fn test_generate_output_types() {
        let roles = vec![make_role("Client"), make_role("Server")];
        let tokens = generate_output_types(&roles);

        let output = tokens.to_string();
        assert!(output.contains("ClientOutput"));
        assert!(output.contains("ServerOutput"));
    }

    #[test]
    fn test_generate_runner_body_send_wildcard() {
        use crate::ast::{role::RoleIndex, LocalType, MessageType};

        // Create a role with wildcard index: Worker[*]
        let worker = Role::with_index(format_ident!("Worker"), RoleIndex::Wildcard).unwrap();
        let msg = MessageType {
            name: format_ident!("Task"),
            type_annotation: None,
            payload: None,
        };
        let local_type = LocalType::Send {
            to: worker,
            message: msg,
            continuation: Box::new(LocalType::End),
        };

        let tokens = generate_runner_body(&local_type, &mut RecursionContext::new());
        let output = tokens.to_string();

        // Check that we generate resolve_family and broadcast calls
        assert!(
            output.contains("resolve_family"),
            "Should use resolve_family for wildcard"
        );
        assert!(
            output.contains("broadcast"),
            "Should use broadcast for wildcard send"
        );
    }

    #[test]
    fn test_generate_runner_body_send_range() {
        use crate::ast::{
            role::{RangeExpr, RoleIndex, RoleRange},
            LocalType, MessageType,
        };

        // Create a role with range index: Worker[0..3]
        let range = RoleRange {
            start: RangeExpr::Concrete(0),
            end: RangeExpr::Concrete(3),
        };
        let worker = Role::with_index(format_ident!("Worker"), RoleIndex::Range(range)).unwrap();
        let msg = MessageType {
            name: format_ident!("Task"),
            type_annotation: None,
            payload: None,
        };
        let local_type = LocalType::Send {
            to: worker,
            message: msg,
            continuation: Box::new(LocalType::End),
        };

        let tokens = generate_runner_body(&local_type, &mut RecursionContext::new());
        let output = tokens.to_string();

        // Check that we generate resolve_range and broadcast calls
        assert!(
            output.contains("resolve_range"),
            "Should use resolve_range for range"
        );
        assert!(
            output.contains("broadcast"),
            "Should use broadcast for range send"
        );
    }

    #[test]
    fn test_generate_runner_body_recv_wildcard() {
        use crate::ast::{role::RoleIndex, LocalType, MessageType};

        // Create a role with wildcard index: Worker[*]
        let worker = Role::with_index(format_ident!("Worker"), RoleIndex::Wildcard).unwrap();
        let msg = MessageType {
            name: format_ident!("Result"),
            type_annotation: None,
            payload: None,
        };
        let local_type = LocalType::Receive {
            from: worker,
            message: msg,
            continuation: Box::new(LocalType::End),
        };

        let tokens = generate_runner_body(&local_type, &mut RecursionContext::new());
        let output = tokens.to_string();

        // Check that we generate resolve_family and collect calls
        assert!(
            output.contains("resolve_family"),
            "Should use resolve_family for wildcard"
        );
        assert!(
            output.contains("collect"),
            "Should use collect for wildcard receive"
        );
    }

    #[test]
    fn test_generate_range_exprs_concrete() {
        use crate::ast::role::{RangeExpr, RoleRange};

        let range = RoleRange {
            start: RangeExpr::Concrete(1),
            end: RangeExpr::Concrete(5),
        };

        let (start, end) = generate_range_exprs(&range);
        assert_eq!(start.to_string(), "1u32");
        assert_eq!(end.to_string(), "5u32");
    }

    #[test]
    fn test_generate_range_exprs_symbolic() {
        use crate::ast::role::{RangeExpr, RoleRange};

        let range = RoleRange {
            start: RangeExpr::Symbolic("start".to_string()),
            end: RangeExpr::Symbolic("end".to_string()),
        };

        let (start, end) = generate_range_exprs(&range);
        assert_eq!(start.to_string(), "start");
        assert_eq!(end.to_string(), "end");
    }
}
