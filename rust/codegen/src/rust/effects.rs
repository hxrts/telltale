//! Effects-Based Code Generation
//!
//! This module generates protocol implementations that build
//! effect programs using a free algebra approach.
//!
//! Uses `rumpsteak_types::LocalTypeR` as input.

use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use rumpsteak_types::LocalTypeR;

/// Generate effect-based protocol implementation from LocalTypeR.
#[must_use]
pub fn generate_effects_protocol(
    protocol_name: &str,
    role_names: &[&str],
    local_types: &[(&str, &LocalTypeR)],
) -> TokenStream {
    let protocol_ident = format_ident!("{}", protocol_name);
    let roles = generate_role_enum(role_names);
    let endpoint_type = generate_endpoint_type(protocol_name);
    let role_functions = generate_role_functions(protocol_name, local_types);

    quote! {
        use serde::{Serialize, Deserialize};

        // Common message trait for this protocol
        #[derive(Clone, Debug, Serialize, Deserialize)]
        pub enum Message {
            // Generated message variants
            Default,
        }

        /// Protocol endpoint
        pub struct #protocol_ident;

        #roles

        #endpoint_type

        #role_functions
    }
}

fn generate_role_enum(role_names: &[&str]) -> TokenStream {
    let role_variants: Vec<_> = role_names
        .iter()
        .map(|name| format_ident!("{}", name))
        .collect();

    quote! {
        #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
        pub enum Role {
            #(#role_variants),*
        }
    }
}

fn generate_endpoint_type(protocol_name: &str) -> TokenStream {
    let ep_name = format_ident!("{}Endpoint", protocol_name);

    quote! {
        pub struct #ep_name {
            // Protocol-specific endpoint state
        }

        impl Default for #ep_name {
            fn default() -> Self {
                Self {}
            }
        }
    }
}

fn generate_role_functions(
    protocol_name: &str,
    local_types: &[(&str, &LocalTypeR)],
) -> TokenStream {
    local_types
        .iter()
        .map(|(role_name, local_type)| {
            let role_name_str = role_name.to_lowercase();
            let program_fn_name = format_ident!("{}_program", role_name_str);
            let run_fn_name = format_ident!("run_{}", role_name_str);
            let endpoint_type = format_ident!("{}Endpoint", protocol_name);

            let body = generate_role_body(local_type, role_name);

            quote! {
                /// Generate the effect program for this role
                pub fn #program_fn_name() -> Program<Role, Message> {
                    #body
                }

                /// Run the effect program for this role using a handler
                pub async fn #run_fn_name<H: Handler<Role = Role, Endpoint = #endpoint_type>>(
                    handler: &mut H,
                    endpoint: &mut #endpoint_type,
                ) -> Result<InterpretResult<Message>, H::Error> {
                    let program = #program_fn_name();
                    interpret(handler, endpoint, program).await
                }
            }
        })
        .collect()
}

fn generate_role_body(local_type: &LocalTypeR, _role: &str) -> TokenStream {
    generate_program_builder(local_type)
}

/// Generate program builder code for a local type
fn generate_program_builder(local_type: &LocalTypeR) -> TokenStream {
    let program_effects = generate_program_effects(local_type);

    quote! {
        Program::new()
            #program_effects
            .end()
    }
}

/// Generate effect builder calls for a local type
fn generate_program_effects(local_type: &LocalTypeR) -> TokenStream {
    match local_type {
        LocalTypeR::End => {
            quote! {}
        }

        LocalTypeR::Send { partner, branches } => {
            let partner_ident = format_ident!("{}", partner);

            if branches.len() == 1 {
                // Simple send
                let (label, continuation) = &branches[0];
                let label_str = &label.name;
                let continuation_effects = generate_program_effects(continuation);

                quote! {
                    .send(Role::#partner_ident, Message::Default) // TODO: proper message type
                    .with_label(Label(#label_str))
                    #continuation_effects
                }
            } else {
                // Internal choice - generate Choose effect
                let branch_programs: Vec<_> = branches
                    .iter()
                    .map(|(label, cont)| {
                        let label_str = &label.name;
                        let branch_effects = generate_program_effects(cont);

                        quote! {
                            (Label(#label_str), Program::new()#branch_effects)
                        }
                    })
                    .collect();

                let first_label = branches
                    .first()
                    .map(|(l, _)| l.name.clone())
                    .unwrap_or_default();

                quote! {
                    .choose(Role::#partner_ident, Label(#first_label))
                    .branch(Role::#partner_ident, vec![#(#branch_programs),*])
                }
            }
        }

        LocalTypeR::Recv { partner, branches } => {
            let partner_ident = format_ident!("{}", partner);

            if branches.len() == 1 {
                // Simple receive
                let (label, continuation) = &branches[0];
                let label_str = &label.name;
                let continuation_effects = generate_program_effects(continuation);

                quote! {
                    .recv::<Message>(Role::#partner_ident)
                    .with_label(Label(#label_str))
                    #continuation_effects
                }
            } else {
                // External choice - generate Offer effect
                let branch_programs: Vec<_> = branches
                    .iter()
                    .map(|(label, cont)| {
                        let label_str = &label.name;
                        let branch_effects = generate_program_effects(cont);

                        quote! {
                            (Label(#label_str), Program::new()#branch_effects)
                        }
                    })
                    .collect();

                quote! {
                    .offer(Role::#partner_ident)
                    .branch(Role::#partner_ident, vec![#(#branch_programs),*])
                }
            }
        }

        LocalTypeR::Mu { var: _, body } => {
            // Generate recursive effect - for now, just inline the body once
            let body_effects = generate_program_effects(body);
            quote! {
                .loop_n(1, Program::new()#body_effects)
            }
        }

        LocalTypeR::Var(_var) => {
            // Variable reference - in effect programs, this is handled by the containing Mu
            quote! {
                // Recursion handled by containing loop
            }
        }
    }
}

/// Effect program types (minimal stubs for codegen)
#[allow(dead_code)]
pub struct Program<R, M> {
    _phantom: std::marker::PhantomData<(R, M)>,
}

#[allow(dead_code)]
impl<R, M> Program<R, M> {
    pub fn new() -> Self {
        Self {
            _phantom: std::marker::PhantomData,
        }
    }
}

impl<R, M> Default for Program<R, M> {
    fn default() -> Self {
        Self::new()
    }
}

/// Label wrapper for branch selection
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Label(pub String);

impl Label {
    pub fn new(name: &str) -> Self {
        Self(name.to_string())
    }
}

/// Result of interpreting an effect program
#[derive(Debug)]
pub struct InterpretResult<M> {
    pub messages: Vec<M>,
}

/// Handler trait for effect interpretation
pub trait Handler {
    type Role;
    type Endpoint;
    type Error;
}

/// Interpret an effect program using a handler
pub async fn interpret<H: Handler, M>(
    _handler: &mut H,
    _endpoint: &mut H::Endpoint,
    _program: Program<H::Role, M>,
) -> Result<InterpretResult<M>, H::Error> {
    todo!("interpret effect program")
}

#[cfg(test)]
mod tests {
    use super::*;
    use rumpsteak_types::Label as TypesLabel;

    #[test]
    fn test_generate_simple_protocol() {
        let local_types = vec![("Client", &LocalTypeR::End), ("Server", &LocalTypeR::End)];

        let code = generate_effects_protocol("SimpleProtocol", &["Client", "Server"], &local_types);
        let code_str = code.to_string();

        assert!(code_str.contains("enum Role"));
        assert!(code_str.contains("Client"));
        assert!(code_str.contains("Server"));
        assert!(code_str.contains("run_client"));
        assert!(code_str.contains("run_server"));
    }

    #[test]
    fn test_generate_send_recv() {
        let client_type = LocalTypeR::send("Server", TypesLabel::new("Request"), LocalTypeR::End);
        let server_type = LocalTypeR::recv("Client", TypesLabel::new("Request"), LocalTypeR::End);

        let local_types = vec![("Client", &client_type), ("Server", &server_type)];

        let code = generate_effects_protocol("Echo", &["Client", "Server"], &local_types);
        let code_str = code.to_string();

        assert!(code_str.contains("send"));
        assert!(code_str.contains("recv"));
    }

    #[test]
    fn test_generate_choice() {
        let client_type = LocalTypeR::Send {
            partner: "Server".to_string(),
            branches: vec![
                (TypesLabel::new("Add"), LocalTypeR::End),
                (TypesLabel::new("Quit"), LocalTypeR::End),
            ],
        };

        let local_types = vec![("Client", &client_type)];

        let code = generate_effects_protocol("Calc", &["Client"], &local_types);
        let code_str = code.to_string();

        assert!(code_str.contains("choose"));
        assert!(code_str.contains("branch"));
    }
}
