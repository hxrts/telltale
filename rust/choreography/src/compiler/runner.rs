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
//! pub async fn run_client<A: ChoreographicAdapter>(
//!     adapter: &mut A,
//!     ctx: &ProtocolContext,
//! ) -> Result<ClientOutput, A::Error> {
//!     // Generated from Client's local type projection
//! }
//!
//! pub async fn run_server<A: ChoreographicAdapter>(
//!     adapter: &mut A,
//!     ctx: &ProtocolContext,
//! ) -> Result<ServerOutput, A::Error> {
//!     // Generated from Server's local type projection
//! }
//!
//! pub async fn execute_as<A: ChoreographicAdapter>(
//!     role: Role,
//!     adapter: &mut A,
//! ) -> Result<ProtocolOutput, A::Error> {
//!     match role {
//!         Role::Client => run_client(adapter, &ProtocolContext::new("Protocol", "Client")).await,
//!         Role::Server => run_server(adapter, &ProtocolContext::new("Protocol", "Server")).await,
//!     }
//! }
//! ```

use crate::ast::{LocalType, Role};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};

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
    let role_name = &role.name;
    let fn_name = format_ident!("run_{}", role_name.to_string().to_lowercase());
    let output_type = format_ident!("{}Output", role_name);
    let protocol_str = protocol_name;
    let role_str = role_name.to_string();

    // Generate the function body from local type
    let body = generate_runner_body(local_type, &mut RecursionContext::new());

    // Determine if this role is indexed
    let (fn_signature, ctx_creation) = if role.index.is_some() || role.param.is_some() {
        // Indexed role - add index parameter
        (
            quote! {
                pub async fn #fn_name<A: ChoreographicAdapter>(
                    adapter: &mut A,
                    index: u32,
                ) -> Result<#output_type, A::Error>
            },
            quote! {
                let _ctx = ProtocolContext::indexed(#protocol_str, #role_str, index);
            },
        )
    } else {
        // Static role
        (
            quote! {
                pub async fn #fn_name<A: ChoreographicAdapter>(
                    adapter: &mut A,
                ) -> Result<#output_type, A::Error>
            },
            quote! {
                let _ctx = ProtocolContext::new(#protocol_str, #role_str);
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
struct RecursionContext {
    /// Current recursion depth
    depth: usize,
    /// Labels of active recursion points
    labels: Vec<String>,
}

impl RecursionContext {
    fn new() -> Self {
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

/// Generate the body of a runner function from a local type.
fn generate_runner_body(local_type: &LocalType, ctx: &mut RecursionContext) -> TokenStream {
    match local_type {
        LocalType::Send {
            to,
            message,
            continuation,
        } => {
            let to_role = generate_role_id(to);
            let msg_type = &message.name;
            let cont = generate_runner_body(continuation, ctx);

            quote! {
                // Send to #to
                // TODO(message-provisioning): Currently uses Default::default() for message values.
                // Users should provide actual message content through a callback or builder pattern.
                // See: protocol state machine should call user-provided message factory.
                let msg: #msg_type = Default::default();
                adapter.send(#to_role, msg).await?;
                #cont
            }
        }

        LocalType::Receive {
            from,
            message,
            continuation,
        } => {
            let from_role = generate_role_id(from);
            let msg_type = &message.name;
            let cont = generate_runner_body(continuation, ctx);

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
                    let label_str = label.to_string();
                    let cont = generate_runner_body(cont_type, ctx);
                    quote! {
                        Choice::#label => {
                            adapter.choose(#to_role, #label_str).await?;
                            #cont
                        }
                    }
                })
                .collect();

            // Generate the Choice enum for this select
            let choice_variants: Vec<TokenStream> = branches
                .iter()
                .map(|(label, _)| {
                    quote! { #label }
                })
                .collect();

            // Get the first variant for default choice
            let first_variant = branches.first().map(|(label, _)| label.clone());

            quote! {
                // Internal choice - select branch to send to #to
                #[derive(Debug, Clone, Copy)]
                enum Choice {
                    #(#choice_variants),*
                }

                // Default to first variant. Override this logic in production code.
                // Consider using a ChoiceProvider callback for runtime decisions.
                let choice: Choice = Choice::#first_variant;
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
                    let label_str = label.to_string();
                    let cont = generate_runner_body(cont_type, ctx);
                    quote! {
                        #label_str => {
                            #cont
                        }
                    }
                })
                .collect();

            quote! {
                // External choice - receive branch selection from #from
                // TODO(protocol-errors): Replace panic with proper error type
                // See: https://github.com/aura-project/rumpsteak-aura/issues/new
                let label = adapter.offer(#from_role).await?;
                match label {
                    #(#match_arms)*
                    _ => panic!("Protocol violation: unexpected branch label '{}' from {}", label, stringify!(#from_role)),
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
                        LocalChoice::#label => {
                            #cont
                        }
                    }
                })
                .collect();

            // Generate the LocalChoice enum
            let choice_variants: Vec<TokenStream> = branches
                .iter()
                .map(|(label, _)| {
                    quote! { #label }
                })
                .collect();

            // Get the first variant for default choice
            let first_variant = branches.first().map(|(label, _)| label.clone());

            quote! {
                // Local choice - no communication
                #[derive(Debug, Clone, Copy)]
                enum LocalChoice {
                    #(#choice_variants),*
                }

                // Default to first variant. Override this logic in production code.
                let choice: LocalChoice = LocalChoice::#first_variant;
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
                    let role_str = role.name.to_string();
                    quote! {
                        // Loop controlled by role
                        loop {
                            #loop_body
                            // Check if role signals continuation
                            let _ = #role_str; // Role that decides: role_str
                            // TODO(loop-choice): Role-controlled loops need integration with the
                            // choice mechanism. The controlling role should send a "continue/break"
                            // choice that other participants observe to decide loop termination.
                            break;
                        }
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
                        // Unbounded loop - runs until explicitly broken
                        // TODO(loop-termination): Unbounded loops currently break immediately.
                        // For correct semantics, loops need a termination condition from:
                        // - A controlling role's choice (see TODO(loop-choice))
                        // - A user-provided predicate function
                        // - Protocol-level termination signals
                        loop {
                            #loop_body
                            break; // Placeholder: should check termination condition
                        }
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
                    panic!("Internal error: unbound recursive variable '{}'. \
                           This is a bug in the protocol code generator.", #label_str);
                }
            }
        }

        LocalType::Timeout { duration, body } => {
            let timeout_ms = duration.as_millis() as u64;
            let timeout_body = generate_runner_body(body, ctx);

            quote! {
                // Timeout after #duration ms
                // TODO(protocol-errors): Replace panic with proper timeout error
                // The adapter error type should implement From<TimeoutError> for production use
                // See: https://github.com/aura-project/rumpsteak-aura/issues/new
                let timeout_result = tokio::time::timeout(
                    std::time::Duration::from_millis(#timeout_ms),
                    async {
                        #timeout_body
                        Ok::<_, A::Error>(())
                    }
                ).await;

                match timeout_result {
                    Ok(inner_result) => inner_result?,
                    Err(_elapsed) => panic!(
                        "Protocol timeout: operation exceeded {} ms. \
                         To handle timeouts gracefully, implement From<tokio::time::error::Elapsed> \
                         for your adapter's error type.",
                        #timeout_ms
                    ),
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

/// Generate a RoleId expression for a role.
fn generate_role_id(role: &Role) -> TokenStream {
    use crate::ast::role::RoleIndex;

    let name = role.name.to_string();

    if let Some(ref index) = role.index {
        match index {
            RoleIndex::Concrete(n) => {
                quote! {
                    RoleId::indexed(#name, #n)
                }
            }
            RoleIndex::Symbolic(var) => {
                // Use a runtime variable
                let var_ident = format_ident!("{}", var);
                quote! {
                    RoleId::indexed(#name, #var_ident)
                }
            }
            RoleIndex::Wildcard => {
                // TODO(wildcard-roles): Wildcard roles (e.g., "Worker[*]") should be expanded
                // at code generation time to handle all matching participants. Currently
                // falls back to a simple RoleId which won't correctly broadcast/multicast.
                quote! {
                    RoleId::new(#name) // Placeholder: wildcards need expansion to role set
                }
            }
            RoleIndex::Range(_) => {
                // TODO(range-roles): Range roles (e.g., "Worker[0..n]") should be expanded
                // to iterate over the specified range. Currently falls back to a simple
                // RoleId which won't correctly handle the range semantics.
                quote! {
                    RoleId::new(#name) // Placeholder: ranges need iteration loop
                }
            }
        }
    } else if role.param.is_some() {
        // Parameterized role - use the index parameter
        quote! {
            RoleId::indexed(#name, index)
        }
    } else {
        quote! {
            RoleId::new(#name)
        }
    }
}

/// Generate the `execute_as` dispatch function.
///
/// This function routes execution to the appropriate `run_{role}` function
/// based on a runtime role value.
#[must_use]
pub fn generate_execute_as(
    protocol_name: &str,
    roles: &[Role],
    _local_types: &[(Role, LocalType)],
) -> TokenStream {
    let protocol_str = protocol_name;
    let role_enum_name = format_ident!("{}Role", protocol_name);

    // Generate role enum variants
    let role_variants: Vec<TokenStream> = roles
        .iter()
        .map(|role| {
            let name = &role.name;
            if role.index.is_some() || role.param.is_some() {
                quote! { #name(u32) }
            } else {
                quote! { #name }
            }
        })
        .collect();

    // Generate match arms
    let match_arms: Vec<TokenStream> = roles
        .iter()
        .map(|role| {
            let name = &role.name;
            let fn_name = format_ident!("run_{}", name.to_string().to_lowercase());

            if role.index.is_some() || role.param.is_some() {
                quote! {
                    #role_enum_name::#name(index) => {
                        #fn_name(adapter, index).await?;
                    }
                }
            } else {
                quote! {
                    #role_enum_name::#name => {
                        #fn_name(adapter).await?;
                    }
                }
            }
        })
        .collect();

    quote! {
        /// Role enum for runtime dispatch
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
        pub enum #role_enum_name {
            #(#role_variants),*
        }

        /// Execute the protocol as a specific role.
        ///
        /// This function dispatches to the appropriate `run_{role}` function
        /// based on the provided role.
        pub async fn execute_as<A: ChoreographicAdapter>(
            role: #role_enum_name,
            adapter: &mut A,
        ) -> Result<(), A::Error> {
            let _protocol = #protocol_str;

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
            let name = &role.name;
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
    let output_types = generate_output_types(roles);

    let runner_fns: Vec<TokenStream> = local_types
        .iter()
        .map(|(role, local_type)| generate_runner_fn(protocol_name, role, local_type))
        .collect();

    let execute_as = generate_execute_as(protocol_name, roles, local_types);

    quote! {
        /// Generated runner functions for protocol execution
        #[allow(dead_code, unused_imports, unused_variables)]
        pub mod runners {
            use super::*;
            use ::rumpsteak_aura_choreography::runtime::{ChoreographicAdapter, ProtocolContext, RoleId};

            #output_types

            #(#runner_fns)*

            #execute_as
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::Role;

    fn make_role(name: &str) -> Role {
        Role::new(format_ident!("{}", name))
    }

    #[test]
    fn test_generate_role_id_static() {
        let role = make_role("Client");
        let tokens = generate_role_id(&role);
        let expected = quote! { RoleId::new("Client") };
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
}
