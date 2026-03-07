//! Choreographic protocol definition macro implementation.
//!
//! This module provides the implementation of the `choreography!` macro,
//! which allows defining multiparty protocols from a global viewpoint.

use proc_macro2::{Ident, TokenStream};
use quote::{quote, ToTokens};
use std::collections::{BTreeMap, HashSet};
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
    validate_protocol(&protocol)?;

    // Generate role structs
    let role_structs = generate_role_structs(&protocol);

    // Generate message types
    let message_types = generate_message_types(&protocol)?;

    // Generate session types for each role
    let session_types = generate_session_types(&protocol)?;

    // Generate setup function
    let setup_fn = generate_setup_function(&protocol);

    // Generate use statements for the necessary imports
    let imports = quote! {
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
/// in the `telltale-choreography` crate. The macro in that crate (`telltale_choreography::choreography!`)
/// provides complete integration. This entry point emits a compile error directing users there.
fn choreography_from_dsl_string(dsl: String) -> proc_macro2::TokenStream {
    drop(dsl); // Explicitly consume parameter
    quote! {
        compile_error!(
            "DSL string parsing with parameterized roles support is available through the telltale_choreography crate.\n\
             Use: telltale_choreography::choreography! instead of telltale_macros::choreography!\n\
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
}

/// Protocol interaction
enum Interaction {
    Send {
        from: Ident,
        to: Ident,
        message: Ident,
        payload: Option<syn::Type>,
    },
}

fn parse_header_roles(input: ParseStream) -> Result<Option<Vec<RoleDef>>> {
    if !input.peek(syn::token::Paren) {
        return Ok(None);
    }

    let content;
    parenthesized!(content in input);
    let mut roles = Vec::new();
    while !content.is_empty() {
        let role_name: Ident = content.parse()?;
        roles.push(RoleDef { name: role_name });
        if content.peek(Token![,]) {
            let _: Token![,] = content.parse()?;
        } else {
            break;
        }
    }
    Ok(Some(roles))
}

fn parse_roles_block(
    content: ParseStream,
    header_roles: Option<Vec<RoleDef>>,
) -> Result<Vec<RoleDef>> {
    if let Some(roles) = header_roles {
        return Ok(roles);
    }
    if !content.peek(syn::Ident) {
        return Ok(Vec::new());
    }

    let roles_ident: Ident = content.parse()?;
    if roles_ident != "roles" {
        return Err(Error::new(roles_ident.span(), "expected 'roles'"));
    }
    if content.peek(Token![:]) {
        let _: Token![:] = content.parse()?;
    }

    let mut roles = Vec::new();
    loop {
        // bounded: consumes token stream, breaks on non-comma
        let role_name: Ident = content.parse()?;
        roles.push(RoleDef { name: role_name });
        if content.peek(Token![,]) {
            let _: Token![,] = content.parse()?;
            continue;
        }
        if content.peek(Token![;]) {
            let _: Token![;] = content.parse()?;
        }
        break;
    }
    Ok(roles)
}

fn parse_interactions(content: ParseStream) -> Result<Vec<Interaction>> {
    let mut interactions = Vec::new();
    while !content.is_empty() {
        interactions.push(parse_interaction(content)?);
    }
    Ok(interactions)
}

impl Parse for ProtocolDef {
    fn parse(input: ParseStream) -> Result<Self> {
        // Parse: protocol Name (Roles)? (=)? { ... }
        let protocol_ident: Ident = input.parse()?;
        if protocol_ident != "protocol" {
            return Err(Error::new(protocol_ident.span(), "expected 'protocol'"));
        }
        let name: Ident = input.parse()?;

        let roles_from_header = parse_header_roles(input)?;

        // Optional '=' before the block
        if input.peek(Token![=]) {
            let _: Token![=] = input.parse()?;
        }

        let content;
        braced!(content in input);

        let roles = parse_roles_block(&content, roles_from_header)?;
        let interactions = parse_interactions(&content)?;

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
            Some(content.parse()?)
        } else {
            None
        };

        if input.peek(Token![;]) {
            let _: Token![;] = input.parse()?;
        }

        return Ok(Interaction::Send {
            from,
            to,
            message,
            payload,
        });
    }

    Err(Error::new(input.span(), "expected interaction"))
}

fn validate_protocol(protocol: &ProtocolDef) -> Result<()> {
    if protocol.roles.len() < 2 {
        return Err(Error::new(
            protocol.name.span(),
            "protocol must declare at least two roles",
        ));
    }

    let mut role_names = HashSet::new();
    for role in &protocol.roles {
        let name = role.name.to_string();
        if !role_names.insert(name.clone()) {
            return Err(Error::new(
                role.name.span(),
                format!("duplicate role '{name}'"),
            ));
        }
    }

    for interaction in &protocol.interactions {
        let Interaction::Send {
            from,
            to,
            message: _,
            payload: _,
        } = interaction;

        let from_name = from.to_string();
        if !role_names.contains(&from_name) {
            return Err(Error::new(
                from.span(),
                format!("role '{from_name}' is not declared in protocol roles"),
            ));
        }

        let to_name = to.to_string();
        if !role_names.contains(&to_name) {
            return Err(Error::new(
                to.span(),
                format!("role '{to_name}' is not declared in protocol roles"),
            ));
        }

        if from == to {
            return Err(Error::new(
                from.span(),
                format!("self-send '{from_name} -> {to_name}' is not supported"),
            ));
        }
    }

    Ok(())
}

/// Generate role struct definitions
fn generate_role_structs(protocol: &ProtocolDef) -> TokenStream {
    let role_names: Vec<_> = protocol.roles.iter().map(|r| &r.name).collect();

    let mut role_structs = Vec::new();
    for (i, role) in role_names.iter().enumerate() {
        let route_fields: Vec<_> = role_names
            .iter()
            .enumerate()
            .filter_map(|(j, other)| {
                if i == j {
                    None
                } else {
                    Some(quote! { #[route(#other)] Channel })
                }
            })
            .collect();

        role_structs.push(quote! {
            #[derive(::telltale::Role)]
            #[message(Label)]
            #[allow(dead_code)]
            pub struct #role(#(#route_fields),*);
        });
    }

    quote! {
        type Channel = ::telltale::channel::Bidirectional<UnboundedSender<Label>, UnboundedReceiver<Label>>;

        #(#role_structs)*

        /// Roles tuple for protocol setup
        #[derive(::telltale::Roles)]
        #[allow(dead_code)]
        pub struct Roles(#(#role_names),*);
    }
}

fn payload_signature(payload: Option<&syn::Type>) -> String {
    match payload {
        Some(ty) => ty.to_token_stream().to_string(),
        None => "<none>".to_string(),
    }
}

fn collect_messages(protocol: &ProtocolDef) -> Result<Vec<(Ident, Option<syn::Type>)>> {
    let mut seen: BTreeMap<String, (Ident, Option<syn::Type>, String)> = BTreeMap::new();
    let mut ordered = Vec::new();

    for interaction in &protocol.interactions {
        let Interaction::Send {
            from: _,
            to: _,
            message,
            payload,
        } = interaction;

        let key = message.to_string();
        let signature = payload_signature(payload.as_ref());
        if let Some((_, _, existing_signature)) = seen.get(&key) {
            if *existing_signature != signature {
                return Err(Error::new(
                    message.span(),
                    format!(
                        "message '{key}' is used with conflicting payload types in the same protocol"
                    ),
                ));
            }
            continue;
        }

        let payload_clone = payload.clone();
        seen.insert(key, (message.clone(), payload_clone.clone(), signature));
        ordered.push((message.clone(), payload_clone));
    }

    Ok(ordered)
}

/// Generate message types
fn generate_message_types(protocol: &ProtocolDef) -> Result<TokenStream> {
    let messages = collect_messages(protocol)?;

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

    Ok(quote! {
        /// Generated message types
        #(#message_structs)*

        /// Message enum for the protocol
        #[derive(::telltale::Message)]
        #[allow(dead_code)]
        pub enum Label {
            #(#message_names(#message_names)),*
        }
    })
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
            #[::telltale::session]
            pub type #session_type_name = #session_type;
        });
    }

    Ok(types)
}

fn apply_send_recv_projection(
    role_name: &Ident,
    from: &Ident,
    to: &Ident,
    message: &Ident,
    continuation: TokenStream,
) -> TokenStream {
    if from == role_name {
        quote! { ::telltale::Send<#to, #message, #continuation> }
    } else if to == role_name {
        quote! { ::telltale::Receive<#from, #message, #continuation> }
    } else {
        continuation
    }
}

/// Project the protocol to a specific role's session type
fn project_role(protocol: &ProtocolDef, role: &RoleDef) -> proc_macro2::TokenStream {
    let mut type_expr = quote! { ::telltale::End };
    let role_name = &role.name;

    // Process interactions in reverse order to build the type
    for interaction in protocol.interactions.iter().rev() {
        let Interaction::Send {
            from,
            to,
            message,
            payload: _,
        } = interaction;
        type_expr = apply_send_recv_projection(role_name, from, to, message, type_expr);
    }

    type_expr
}

/// Generate setup function
fn generate_setup_function(protocol: &ProtocolDef) -> TokenStream {
    let protocol_name = &protocol.name;

    quote! {
        #[doc = concat!("Setup function for the ", stringify!(#protocol_name), " protocol.")]
        pub fn setup() -> Roles {
            Roles::default()
        }
    }
}
