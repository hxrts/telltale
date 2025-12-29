//! Choreographic protocol definition macro implementation.
//!
//! This module provides the implementation of the `choreography!` macro,
//! which allows defining multiparty protocols from a global viewpoint.

use proc_macro2::{Ident, TokenStream};
use quote::quote;
use syn::{
    braced, parenthesized,
    parse::{Parse, ParseStream},
    Error, LitStr, Result, Token,
};

/// Main entry point for the choreography! macro.
///
/// Parses choreographic protocol definitions and generates Rust code including
/// roles, messages, and session types.
pub fn choreography(input: TokenStream) -> Result<TokenStream> {
    // First, try to parse as a string literal (for inline DSL)
    if let Ok(lit_str) = syn::parse2::<LitStr>(input.clone()) {
        // Use the DSL parser
        return Ok(choreography_from_dsl_string(lit_str.value()));
    }

    // Otherwise, fall back to syn-based parsing
    let protocol: ProtocolDef = syn::parse2(input)?;

    // Generate role structs
    let role_structs = generate_role_structs(&protocol);

    // Generate message types
    let message_types = generate_message_types(&protocol);

    // Generate session types for each role
    let session_types = generate_session_types(&protocol)?;

    // Generate setup function
    let setup_fn = generate_setup_function(&protocol);

    // Generate use statements for the necessary imports
    let imports = quote! {
        use ::rumpsteak_aura::{channel, Message as MessageTrait, Role as RoleTrait, Roles as RolesTrait};
        use ::futures::channel::mpsc::{UnboundedReceiver, UnboundedSender};
    };

    Ok(quote! {
        #imports
        #role_structs
        #message_types
        #session_types
        #setup_fn
    })
}

/// Parse choreography from DSL string
///
/// Note: DSL string parsing with full support for parameterized roles is now available
/// in the `rumpsteak-choreography` crate. The macro in that crate (`rumpsteak_aura_choreography::choreography!`)
/// provides complete integration. This stub remains for backwards compatibility.
fn choreography_from_dsl_string(dsl: String) -> proc_macro2::TokenStream {
    drop(dsl); // Explicitly consume parameter
    quote! {
        compile_error!(
            "DSL string parsing with parameterized roles support is available through the rumpsteak_aura_choreography crate.\n\
             Use: rumpsteak_aura_choreography::choreography! instead of rumpsteak_macros::choreography!\n\
             \n\
             Or use the explicit macro syntax without string literals for basic protocols."
        );
    }
}

/// Protocol definition from the DSL
struct ProtocolDef {
    name: Ident,
    roles: Vec<RoleDef>,
    interactions: Vec<Interaction>,
}

/// Role definition
struct RoleDef {
    name: Ident,
    /// Parameters for parameterized roles like Worker[N]
    ///
    /// Reserved for future implementation of parameterized roles.
    #[allow(dead_code)]
    params: Option<syn::Expr>,
}

/// Protocol interaction
enum Interaction {
    Send {
        from: Ident,
        to: Ident,
        message: Ident,
        payload: Box<Option<syn::Type>>,
    },
    /// Choice interaction
    ///
    /// Reserved for future macro-level choice syntax.
    /// Currently choices are generated through code generation, not parsed from macro syntax.
    #[allow(dead_code)]
    Choice {
        role: Ident,
        branches: Vec<ChoiceBranch>,
    },
}

/// Branch in a choice interaction
///
/// Reserved for future macro-level choice syntax.
#[allow(dead_code)]
struct ChoiceBranch {
    label: Ident,
    interactions: Vec<Interaction>,
}

impl Parse for ProtocolDef {
    fn parse(input: ParseStream) -> Result<Self> {
        // Parse: protocol Name { ... }
        let protocol_ident: Ident = input.parse()?;
        if protocol_ident != "protocol" {
            return Err(Error::new(protocol_ident.span(), "expected 'protocol'"));
        }
        let name: Ident = input.parse()?;

        let content;
        braced!(content in input);

        // Parse roles
        let mut roles = Vec::new();
        if content.peek(syn::Ident) {
            let roles_ident: Ident = content.parse()?;
            if roles_ident != "roles" {
                return Err(Error::new(roles_ident.span(), "expected 'roles'"));
            }
            let _: Token![:] = content.parse()?;

            loop {
                let role_name: Ident = content.parse()?;
                roles.push(RoleDef {
                    name: role_name,
                    params: None,
                });

                if content.peek(Token![;]) {
                    let _: Token![;] = content.parse()?;
                    break;
                }
                let _: Token![,] = content.parse()?;
            }
        }

        // Parse interactions
        let mut interactions = Vec::new();
        while !content.is_empty() {
            interactions.push(parse_interaction(&content)?);
        }

        Ok(ProtocolDef {
            name,
            roles,
            interactions,
        })
    }
}

fn parse_interaction(input: ParseStream) -> Result<Interaction> {
    // Simple send: A -> B: Message
    if input.peek2(Token![->]) {
        let from: Ident = input.parse()?;
        let _: Token![->] = input.parse()?;
        let to: Ident = input.parse()?;
        let _: Token![:] = input.parse()?;
        let message: Ident = input.parse()?;

        let payload = if input.peek(syn::token::Paren) {
            let content;
            parenthesized!(content in input);
            Box::new(Some(content.parse()?))
        } else {
            Box::new(None)
        };

        let _: Token![;] = input.parse()?;

        return Ok(Interaction::Send {
            from,
            to,
            message,
            payload,
        });
    }

    Err(Error::new(input.span(), "expected interaction"))
}

/// Generate role struct definitions
fn generate_role_structs(protocol: &ProtocolDef) -> TokenStream {
    let role_names: Vec<_> = protocol.roles.iter().map(|r| &r.name).collect();
    let _n = protocol.roles.len();

    // Generate route attributes for each role
    let mut role_structs = Vec::new();
    for (i, role) in role_names.iter().enumerate() {
        // Find the other roles this role needs to communicate with
        let mut routes = Vec::new();
        for (j, other) in role_names.iter().enumerate() {
            if i != j {
                routes.push(quote! { #[route(#other)] });
            }
        }

        // For simplicity, just use first route for bidirectional channel
        let route = if routes.is_empty() {
            quote! {}
        } else {
            let other = &role_names[(i + 1) % role_names.len()];
            quote! { #[route(#other)] }
        };

        role_structs.push(quote! {
            #[derive(::rumpsteak_aura::Role)]
            #[message(Label)]
            #[allow(dead_code)]
            pub struct #role(#route Channel);
        });
    }

    quote! {
        type Channel = ::rumpsteak_aura::channel::Bidirectional<UnboundedSender<Label>, UnboundedReceiver<Label>>;

        #(#role_structs)*

        /// Roles tuple for protocol setup
        #[derive(::rumpsteak_aura::Roles)]
        #[allow(dead_code)]
        pub struct Roles(#(#role_names),*);
    }
}

/// Generate message types
fn generate_message_types(protocol: &ProtocolDef) -> TokenStream {
    let mut messages = Vec::new();

    // Extract messages from interactions
    for interaction in &protocol.interactions {
        if let Interaction::Send {
            message, payload, ..
        } = interaction
        {
            messages.push((message, payload.as_ref().as_ref()));
        }
    }

    let message_structs: Vec<_> = messages
        .iter()
        .map(|(name, payload)| {
            if let Some(ty) = payload {
                quote! {
                    #[derive(Clone, Debug)]
                    #[allow(dead_code)]
                    pub struct #name(pub #ty);
                }
            } else {
                quote! {
                    #[derive(Clone, Debug)]
                    #[allow(dead_code)]
                    pub struct #name;
                }
            }
        })
        .collect();

    let message_names: Vec<_> = messages.iter().map(|(name, _)| name).collect();

    quote! {
        /// Generated message types
        #(#message_structs)*

        /// Message enum for the protocol
        #[derive(::rumpsteak_aura::Message)]
        #[allow(dead_code)]
        pub enum Label {
            #(#message_names(#message_names)),*
        }
    }
}

/// Generate session types for each role
fn generate_session_types(protocol: &ProtocolDef) -> Result<TokenStream> {
    let mut types = TokenStream::new();

    // For each role, generate its session type
    for role in &protocol.roles {
        let role_name = &role.name;
        let session_type = project_role(protocol, role);

        let session_type_name = quote::format_ident!("{}Session", role_name);
        types.extend(quote! {
            #[::rumpsteak_aura::session]
            pub type #session_type_name = #session_type;
        });
    }

    Ok(types)
}

/// Project the protocol to a specific role's session type
fn project_role(protocol: &ProtocolDef, role: &RoleDef) -> proc_macro2::TokenStream {
    let mut type_expr = quote! { ::rumpsteak_aura::End };

    // Process interactions in reverse order to build the type
    for interaction in protocol.interactions.iter().rev() {
        match interaction {
            Interaction::Send {
                from, to, message, ..
            } => {
                if from == &role.name {
                    // This role sends
                    type_expr = quote! {
                        ::rumpsteak_aura::Send<#to, #message, #type_expr>
                    };
                } else if to == &role.name {
                    // This role receives
                    type_expr = quote! {
                        ::rumpsteak_aura::Receive<#from, #message, #type_expr>
                    };
                }
                // Otherwise, this role doesn't participate
            }
            Interaction::Choice {
                role: choosing_role,
                branches,
            } => {
                // Handle choice: the choosing role offers branches, others receive the choice
                if choosing_role == &role.name {
                    // This role makes the choice
                    // Generate: Choose<Label1, S1> + Choose<Label2, S2> + ...
                    let branch_types: Vec<TokenStream> = branches.iter().map(|branch| {
                        let label = &branch.label;
                        // Project each branch's interactions for this role
                        let mut branch_type = type_expr.clone();
                        for branch_interaction in branch.interactions.iter().rev() {
                            match branch_interaction {
                                Interaction::Send { from, to, message, .. } => {
                                    if from == &role.name {
                                        branch_type = quote! {
                                            ::rumpsteak_aura::Send<#to, #message, #branch_type>
                                        };
                                    } else if to == &role.name {
                                        branch_type = quote! {
                                            ::rumpsteak_aura::Receive<#from, #message, #branch_type>
                                        };
                                    }
                                }
                                Interaction::Choice { .. } => {
                                    // Nested choices - recursively handle
                                }
                            }
                        }
                        quote! { ::rumpsteak_aura::Choose<#label, #branch_type> }
                    }).collect();

                    // Combine branches into a choice type (sum type)
                    if !branch_types.is_empty() {
                        type_expr = branch_types
                            .into_iter()
                            .fold(None, |acc, branch| match acc {
                                None => Some(branch),
                                Some(prev) => {
                                    Some(quote! { ::rumpsteak_aura::Branch<#prev, #branch> })
                                }
                            })
                            .unwrap();
                    }
                } else {
                    // This role offers (receives the choice from choosing_role)
                    // Generate: Offer<Role, { Label1 => S1, Label2 => S2, ... }>
                    let branch_types: Vec<TokenStream> = branches.iter().map(|branch| {
                        let label = &branch.label;
                        // Project each branch's interactions for this role
                        let mut branch_type = type_expr.clone();
                        for branch_interaction in branch.interactions.iter().rev() {
                            match branch_interaction {
                                Interaction::Send { from, to, message, .. } => {
                                    if from == &role.name {
                                        branch_type = quote! {
                                            ::rumpsteak_aura::Send<#to, #message, #branch_type>
                                        };
                                    } else if to == &role.name {
                                        branch_type = quote! {
                                            ::rumpsteak_aura::Receive<#from, #message, #branch_type>
                                        };
                                    }
                                }
                                Interaction::Choice { .. } => {
                                    // Nested choices - recursively handle
                                }
                            }
                        }
                        quote! { #label => #branch_type }
                    }).collect();

                    if !branch_types.is_empty() {
                        type_expr = quote! {
                            ::rumpsteak_aura::Offer<#choosing_role, { #(#branch_types),* }>
                        };
                    }
                }
            }
        }
    }

    type_expr
}

/// Generate setup function
fn generate_setup_function(protocol: &ProtocolDef) -> TokenStream {
    let _n = protocol.roles.len();
    #[allow(clippy::no_effect_underscore_binding)] // For future use
    let _protocol_name = &protocol.name;

    quote! {
        /// Setup function for the #protocol_name protocol
        pub fn setup() -> Roles {
            Roles::default()
        }
    }
}
