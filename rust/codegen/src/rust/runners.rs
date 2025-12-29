//! Runner Function Code Generation
//!
//! This module generates `run_{role}` async functions from local type projections.
//! Uses `rumpsteak_types::LocalTypeR` as input.
//!
//! # Generated Code Structure
//!
//! For a protocol with roles `Client` and `Server`, this generates:
//!
//! ```ignore
//! pub async fn run_client<A: Adapter>(
//!     adapter: &mut A,
//! ) -> Result<ClientOutput, A::Error> {
//!     // Generated from Client's LocalTypeR projection
//! }
//!
//! pub async fn run_server<A: Adapter>(
//!     adapter: &mut A,
//! ) -> Result<ServerOutput, A::Error> {
//!     // Generated from Server's LocalTypeR projection
//! }
//! ```

use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use rumpsteak_types::LocalTypeR;

/// Generate a runner function for a single role.
///
/// # Arguments
///
/// * `protocol_name` - Name of the protocol
/// * `role_name` - Name of the role
/// * `local_type` - The projected local type for this role
///
/// # Returns
///
/// A TokenStream containing the `run_{role}` function.
#[must_use]
pub fn generate_runner_fn(
    protocol_name: &str,
    role_name: &str,
    local_type: &LocalTypeR,
) -> TokenStream {
    let fn_name = format_ident!("run_{}", role_name.to_lowercase());
    let output_type = format_ident!("{}Output", role_name);
    let protocol_str = protocol_name;
    let role_str = role_name;

    // Generate the function body from local type
    let body = generate_runner_body(local_type, &mut RecursionContext::new());

    quote! {
        pub async fn #fn_name<A: Adapter>(
            adapter: &mut A,
        ) -> Result<#output_type, A::Error> {
            let _ctx = ProtocolContext::new(#protocol_str, #role_str);

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
fn generate_runner_body(local_type: &LocalTypeR, ctx: &mut RecursionContext) -> TokenStream {
    match local_type {
        LocalTypeR::End => {
            quote! {
                // End of protocol
            }
        }

        LocalTypeR::Send { partner, branches } => {
            let partner_str = partner.as_str();

            if branches.len() == 1 {
                // Single branch - simple send
                let (label, continuation) = &branches[0];
                let _label_str = &label.name;
                let cont = generate_runner_body(continuation, ctx);

                quote! {
                    // Send #label_str to #partner
                    let msg = Default::default(); // TODO: user provides message
                    adapter.send(RoleId::new(#partner_str), msg).await?;
                    #cont
                }
            } else {
                // Multiple branches - internal choice (Select)
                let match_arms: Vec<TokenStream> = branches
                    .iter()
                    .map(|(label, cont_type)| {
                        let label_name = &label.name;
                        let label_ident = format_ident!("{}", label_name);
                        let cont = generate_runner_body(cont_type, ctx);
                        quote! {
                            Choice::#label_ident => {
                                adapter.choose(RoleId::new(#partner_str), #label_name).await?;
                                #cont
                            }
                        }
                    })
                    .collect();

                let choice_variants: Vec<TokenStream> = branches
                    .iter()
                    .map(|(label, _)| {
                        let label_ident = format_ident!("{}", &label.name);
                        quote! { #label_ident }
                    })
                    .collect();

                quote! {
                    // Internal choice - select branch to send to #partner
                    #[derive(Debug)]
                    enum Choice {
                        #(#choice_variants),*
                    }

                    // User must provide choice selection logic
                    let choice: Choice = todo!("User provides choice selection");
                    match choice {
                        #(#match_arms)*
                    }
                }
            }
        }

        LocalTypeR::Recv { partner, branches } => {
            let partner_str = partner.as_str();

            if branches.len() == 1 {
                // Single branch - simple receive
                let (label, continuation) = &branches[0];
                let _label_str = &label.name;
                let cont = generate_runner_body(continuation, ctx);

                quote! {
                    // Receive #label_str from #partner
                    let _msg = adapter.recv(RoleId::new(#partner_str)).await?;
                    #cont
                }
            } else {
                // Multiple branches - external choice (Branch/Offer)
                let match_arms: Vec<TokenStream> = branches
                    .iter()
                    .map(|(label, cont_type)| {
                        let label_str = &label.name;
                        let cont = generate_runner_body(cont_type, ctx);
                        quote! {
                            #label_str => {
                                #cont
                            }
                        }
                    })
                    .collect();

                quote! {
                    // External choice - receive branch selection from #partner
                    let label = adapter.offer(RoleId::new(#partner_str)).await?;
                    match label {
                        #(#match_arms)*
                        _ => panic!("Unexpected branch label: {}", label),
                    }
                }
            }
        }

        LocalTypeR::Mu { var, body } => {
            let var_str = var.as_str();

            // Track recursion
            ctx.enter_rec(var_str);
            let rec_body = generate_runner_body(body, ctx);
            ctx.exit_rec();

            let loop_label =
                syn::Lifetime::new(&format!("'rec_{}", var_str), proc_macro2::Span::call_site());

            quote! {
                // Recursive type
                #loop_label: loop {
                    #rec_body
                    break #loop_label;
                }
            }
        }

        LocalTypeR::Var(var) => {
            let var_str = var.as_str();
            let loop_label =
                syn::Lifetime::new(&format!("'rec_{}", var_str), proc_macro2::Span::call_site());

            if ctx.is_in_rec(var_str) {
                quote! {
                    // Continue recursive loop
                    continue #loop_label;
                }
            } else {
                quote! {
                    // Recursive variable (unbound)
                    panic!("Unbound recursive variable: {}", #var_str);
                }
            }
        }
    }
}

/// Generate output type structs for each role.
#[must_use]
pub fn generate_output_types(role_names: &[&str]) -> TokenStream {
    let output_structs: Vec<TokenStream> = role_names
        .iter()
        .map(|name| {
            let output_name = format_ident!("{}Output", name);

            quote! {
                /// Output from running the role
                #[derive(Debug, Default)]
                pub struct #output_name {
                    // TODO: Add fields based on protocol structure
                }
            }
        })
        .collect();

    quote! {
        #(#output_structs)*
    }
}

/// Generate role enum for runtime dispatch.
#[must_use]
pub fn generate_role_enum(protocol_name: &str, role_names: &[&str]) -> TokenStream {
    let role_enum_name = format_ident!("{}Role", protocol_name);

    let role_variants: Vec<TokenStream> = role_names
        .iter()
        .map(|name| {
            let name_ident = format_ident!("{}", name);
            quote! { #name_ident }
        })
        .collect();

    quote! {
        /// Role enum for runtime dispatch
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
        pub enum #role_enum_name {
            #(#role_variants),*
        }
    }
}

/// Generate the `execute_as` dispatch function.
#[must_use]
pub fn generate_execute_as(protocol_name: &str, role_names: &[&str]) -> TokenStream {
    let protocol_str = protocol_name;
    let role_enum_name = format_ident!("{}Role", protocol_name);

    let match_arms: Vec<TokenStream> = role_names
        .iter()
        .map(|name| {
            let name_ident = format_ident!("{}", name);
            let fn_name = format_ident!("run_{}", name.to_lowercase());

            quote! {
                #role_enum_name::#name_ident => {
                    #fn_name(adapter).await?;
                }
            }
        })
        .collect();

    quote! {
        /// Execute the protocol as a specific role.
        pub async fn execute_as<A: Adapter>(
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

/// Generate all runner code for a protocol.
///
/// This includes:
/// - Output types for each role
/// - `run_{role}` functions for each role
/// - `execute_as` dispatch function
/// - Role enum for runtime dispatch
#[must_use]
pub fn generate_all_runners(
    protocol_name: &str,
    local_types: &[(&str, &LocalTypeR)],
) -> TokenStream {
    let role_names: Vec<&str> = local_types.iter().map(|(name, _)| *name).collect();

    let output_types = generate_output_types(&role_names);
    let role_enum = generate_role_enum(protocol_name, &role_names);

    let runner_fns: Vec<TokenStream> = local_types
        .iter()
        .map(|(role_name, local_type)| generate_runner_fn(protocol_name, role_name, local_type))
        .collect();

    let execute_as = generate_execute_as(protocol_name, &role_names);

    quote! {
        /// Generated runner functions for protocol execution
        pub mod runners {
            use super::*;

            // Required traits and types
            pub trait Adapter {
                type Error;
                async fn send<M>(&mut self, to: RoleId, msg: M) -> Result<(), Self::Error>;
                async fn recv<M>(&mut self, from: RoleId) -> Result<M, Self::Error>;
                async fn choose(&mut self, to: RoleId, label: &str) -> Result<(), Self::Error>;
                async fn offer(&mut self, from: RoleId) -> Result<String, Self::Error>;
            }

            #[derive(Debug, Clone)]
            pub struct RoleId(String);

            impl RoleId {
                pub fn new(name: &str) -> Self {
                    Self(name.to_string())
                }
            }

            #[derive(Debug)]
            pub struct ProtocolContext {
                protocol: String,
                role: String,
            }

            impl ProtocolContext {
                pub fn new(protocol: &str, role: &str) -> Self {
                    Self {
                        protocol: protocol.to_string(),
                        role: role.to_string(),
                    }
                }
            }

            #output_types

            #role_enum

            #(#runner_fns)*

            #execute_as
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rumpsteak_types::Label;

    #[test]
    fn test_generate_output_types() {
        let role_names = vec!["Client", "Server"];
        let tokens = generate_output_types(&role_names);

        let output = tokens.to_string();
        assert!(output.contains("ClientOutput"));
        assert!(output.contains("ServerOutput"));
    }

    #[test]
    fn test_generate_role_enum() {
        let tokens = generate_role_enum("TestProtocol", &["Client", "Server"]);
        let output = tokens.to_string();
        assert!(output.contains("TestProtocolRole"));
        assert!(output.contains("Client"));
        assert!(output.contains("Server"));
    }

    #[test]
    fn test_generate_runner_end() {
        let lt = LocalTypeR::End;
        let tokens = generate_runner_fn("Test", "Client", &lt);
        let output = tokens.to_string();
        assert!(output.contains("run_client"));
        assert!(output.contains("ClientOutput"));
    }

    #[test]
    fn test_generate_runner_send_recv() {
        let lt = LocalTypeR::send("Server", Label::new("msg"), LocalTypeR::End);
        let tokens = generate_runner_fn("Test", "Client", &lt);
        let output = tokens.to_string();
        assert!(output.contains("send"));
        assert!(output.contains("Server"));
    }

    #[test]
    fn test_generate_runner_recursive() {
        let lt = LocalTypeR::mu(
            "loop1",
            LocalTypeR::send("B", Label::new("ping"), LocalTypeR::var("loop1")),
        );
        let tokens = generate_runner_fn("Test", "A", &lt);
        let output = tokens.to_string();
        assert!(output.contains("'rec_loop1"));
        assert!(output.contains("continue"));
    }
}
