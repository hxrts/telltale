//! Choreographic protocol definition macro implementation.
//!
//! Parsing is delegated to the shared Telltale choreography frontend. This
//! proc-macro then lowers the parsed choreography into the historical
//! `telltale-macros` output surface: message structs, a `Label` enum, public
//! role structs, `Roles`, per-role session aliases, and `setup()`.

use proc_macro2::{Delimiter, Ident, Span, TokenStream, TokenTree};
use quote::{format_ident, quote, ToTokens};
use std::collections::BTreeMap;
use syn::{Error, LitStr, Result};
use telltale_parser::ast::{Branch, Choreography, LocalType, MessageType, Protocol, Role};

/// Main entry point for the choreography! macro.
pub fn choreography(input: TokenStream) -> Result<TokenStream> {
    let choreography = parse_macro_choreography(input)?;
    choreography
        .validate()
        .map_err(|err| Error::new(Span::call_site(), err.to_string()))?;

    let local_types = project_local_types(&choreography)?;
    let generated = generate_protocol_module(&choreography, &local_types)?;
    Ok(generated)
}

fn parse_macro_choreography(input: TokenStream) -> Result<Choreography> {
    if let Ok(lit_str) = syn::parse2::<LitStr>(input.clone()) {
        return telltale_parser::parse_choreography_str(&lit_str.value())
            .map_err(|err| Error::new(lit_str.span(), format!("Choreography parse error: {err}")));
    }

    let normalized = normalize_token_dsl(input);
    telltale_parser::parse_choreography_str(&normalized).map_err(|err| {
        Error::new(
            Span::call_site(),
            format!(
                "Choreography parse error: {err}\n\
                 Macro token input is parsed as DSL text after normalization.\n\
                 You can use either string-literal DSL or token-stream DSL forms."
            ),
        )
    })
}

fn normalize_token_dsl(input: TokenStream) -> String {
    #[derive(Default)]
    struct State {
        awaiting_protocol_name: bool,
        protocol_needs_equals: bool,
        awaiting_choice_role: bool,
        choice_needs_at: bool,
    }

    fn needs_space_before_text(out: &str) -> bool {
        matches!(
            out.chars().last(),
            Some(ch) if ch.is_ascii_alphanumeric() || ch == '_' || ch == ')' || ch == ']'
        )
    }

    fn render_tokens(tokens: TokenStream) -> String {
        let mut out = String::new();
        let mut state = State::default();

        for token in tokens {
            match token {
                TokenTree::Ident(ident) => {
                    let text = ident.to_string();
                    if needs_space_before_text(&out) {
                        out.push(' ');
                    }
                    out.push_str(&text);

                    if state.awaiting_protocol_name {
                        state.awaiting_protocol_name = false;
                        state.protocol_needs_equals = true;
                    } else if state.awaiting_choice_role {
                        state.awaiting_choice_role = false;
                        state.choice_needs_at = true;
                    } else if text == "protocol" {
                        state.awaiting_protocol_name = true;
                        state.protocol_needs_equals = false;
                    } else if text == "choice" {
                        state.awaiting_choice_role = true;
                        state.choice_needs_at = false;
                    } else if state.choice_needs_at && text == "at" {
                        state.choice_needs_at = false;
                    }
                }
                TokenTree::Punct(punct) => match punct.as_char() {
                    ';' => out.push('\n'),
                    '=' => {
                        state.protocol_needs_equals = false;
                        out.push('=');
                    }
                    _ => out.push(punct.as_char()),
                },
                TokenTree::Literal(literal) => {
                    if needs_space_before_text(&out) {
                        out.push(' ');
                    }
                    out.push_str(&literal.to_string());
                }
                TokenTree::Group(group) => {
                    if group.delimiter() == Delimiter::Brace {
                        if state.protocol_needs_equals {
                            out.push_str(" =");
                            state.protocol_needs_equals = false;
                        }
                        if state.choice_needs_at {
                            out.push_str(" at");
                            state.choice_needs_at = false;
                        }
                    }

                    let open = match group.delimiter() {
                        Delimiter::Parenthesis => '(',
                        Delimiter::Brace => '{',
                        Delimiter::Bracket => '[',
                        Delimiter::None => ' ',
                    };
                    let close = match group.delimiter() {
                        Delimiter::Parenthesis => ')',
                        Delimiter::Brace => '}',
                        Delimiter::Bracket => ']',
                        Delimiter::None => ' ',
                    };

                    if group.delimiter() != Delimiter::None
                        && !out.ends_with([' ', '\n', '(', '{', '['])
                    {
                        out.push(' ');
                    }

                    if group.delimiter() != Delimiter::None {
                        out.push(open);
                    }
                    let inner = render_tokens(group.stream());
                    out.push_str(&inner);
                    if group.delimiter() != Delimiter::None {
                        out.push(close);
                    }
                }
            }
        }

        out
    }

    let mut normalized = render_tokens(input);
    let patterns = [
        ("-> *", "->*"),
        ("->  *", "->*"),
        ("<- >", "<->"),
        ("< - >", "<->"),
        ("<  - >", "<->"),
        ("< -  >", "<->"),
    ];
    loop {
        let mut changed = false;
        for (from, to) in patterns {
            if normalized.contains(from) {
                normalized = normalized.replace(from, to);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    normalized
}

fn project_local_types(choreography: &Choreography) -> Result<Vec<(Role, LocalType)>> {
    let mut local_types = Vec::new();
    for role in &choreography.roles {
        let local_type = telltale_parser::project(choreography, role)
            .map_err(|err| Error::new(Span::call_site(), err.to_string()))?;
        local_types.push((role.clone(), local_type));
    }
    Ok(local_types)
}

fn generate_protocol_module(
    choreography: &Choreography,
    local_types: &[(Role, LocalType)],
) -> Result<TokenStream> {
    let role_structs = generate_role_structs(&choreography.roles);
    let helper_types = generate_helper_types(&choreography.protocol)?;
    let session_types = generate_session_types(local_types)?;
    let setup_fn = generate_setup_function(&choreography.name);

    let body = quote! {
        use ::telltale::Role;

        #role_structs
        #helper_types
        #session_types
        #setup_fn
    };

    Ok(match &choreography.namespace {
        Some(namespace) => {
            let ns_ident = format_ident!("{}", namespace);
            quote! {
                #[allow(dead_code, unused_imports, unused_variables)]
                pub mod #ns_ident {
                    #body
                }
            }
        }
        None => body,
    })
}

fn generate_role_structs(roles: &[Role]) -> TokenStream {
    let role_names: Vec<_> = roles.iter().map(|role| role.name()).collect();

    let role_structs = roles.iter().enumerate().map(|(index, role)| {
        let role_name = role.name();
        let route_fields: Vec<_> = roles
            .iter()
            .enumerate()
            .filter_map(|(other_index, other_role)| {
                if index == other_index {
                    None
                } else {
                    let other_name = other_role.name();
                    Some(quote! { #[route(#other_name)] Channel })
                }
            })
            .collect();

        if route_fields.is_empty() {
            quote! {
                #[derive(::telltale::Role)]
                #[message(Label)]
                #[allow(dead_code)]
                pub struct #role_name;
            }
        } else {
            quote! {
                #[derive(::telltale::Role)]
                #[message(Label)]
                #[allow(dead_code)]
                pub struct #role_name(#(#route_fields),*);
            }
        }
    });

    quote! {
        type Channel = ::telltale::channel::Bidirectional<
            ::futures::channel::mpsc::UnboundedSender<Label>,
            ::futures::channel::mpsc::UnboundedReceiver<Label>,
        >;

        #(#role_structs)*

        #[derive(::telltale::Roles)]
        #[allow(dead_code)]
        pub struct Roles(#(#role_names),*);
    }
}

#[derive(Clone)]
enum LabelSurface {
    Message {
        name: Ident,
        payload: Option<TokenStream>,
    },
    Choice {
        name: Ident,
    },
}

fn generate_helper_types(protocol: &Protocol) -> Result<TokenStream> {
    let mut labels = BTreeMap::<String, LabelSurface>::new();
    collect_label_surfaces(protocol, &mut labels)?;

    let mut label_variants = Vec::new();
    let mut helper_types = Vec::new();

    for surface in labels.into_values() {
        match surface {
            LabelSurface::Message { name, payload } => {
                if let Some(payload) = payload {
                    helper_types.push(quote! {
                        #[derive(Clone, Debug)]
                        #[allow(dead_code)]
                        pub struct #name #payload;
                    });
                } else {
                    helper_types.push(quote! {
                        #[derive(Clone, Debug)]
                        #[allow(dead_code)]
                        pub struct #name;
                    });
                }
                label_variants.push(quote! { #name(#name) });
            }
            LabelSurface::Choice { name } => {
                helper_types.push(quote! {
                    #[derive(Clone, Debug)]
                    #[allow(dead_code)]
                    pub struct #name;
                });
                label_variants.push(quote! { #name(#name) });
            }
        }
    }

    Ok(quote! {
        #(#helper_types)*

        #[derive(::telltale::Message)]
        #[allow(dead_code)]
        pub enum Label {
            #(#label_variants),*
        }
    })
}

fn collect_label_surfaces(
    protocol: &Protocol,
    labels: &mut BTreeMap<String, LabelSurface>,
) -> Result<()> {
    match protocol {
        Protocol::Send {
            message,
            continuation,
            ..
        } => {
            insert_message_surface(labels, message)?;
            collect_label_surfaces(continuation, labels)?;
        }
        Protocol::Broadcast {
            message,
            continuation,
            ..
        } => {
            insert_message_surface(labels, message)?;
            collect_label_surfaces(continuation, labels)?;
        }
        Protocol::Choice { branches, .. } => {
            collect_choice_surfaces(branches, labels)?;
        }
        Protocol::Case { branches, .. } => {
            for branch in branches {
                collect_label_surfaces(&branch.protocol, labels)?;
            }
        }
        Protocol::Timeout {
            body,
            on_timeout,
            on_cancel,
            ..
        } => {
            collect_label_surfaces(body, labels)?;
            collect_label_surfaces(on_timeout, labels)?;
            if let Some(on_cancel) = on_cancel {
                collect_label_surfaces(on_cancel, labels)?;
            }
        }
        Protocol::Loop { body, .. } | Protocol::Rec { body, .. } => {
            collect_label_surfaces(body, labels)?;
        }
        Protocol::Parallel { protocols } => {
            for protocol in protocols {
                collect_label_surfaces(protocol, labels)?;
            }
        }
        Protocol::Let { continuation, .. }
        | Protocol::Publish { continuation, .. }
        | Protocol::DependentWork { continuation, .. }
        | Protocol::Extension { continuation, .. } => {
            collect_label_surfaces(continuation, labels)?;
        }
        Protocol::Handoff { continuation, .. } => {
            collect_label_surfaces(continuation, labels)?;
        }
        Protocol::Var(_) | Protocol::End => {}
    }

    Ok(())
}

fn collect_choice_surfaces(
    branches: &[Branch],
    labels: &mut BTreeMap<String, LabelSurface>,
) -> Result<()> {
    for branch in branches {
        let key = branch.label.to_string();
        match labels.get(&key) {
            Some(LabelSurface::Message { .. }) => {
                return Err(Error::new(
                    branch.label.span(),
                    format!(
                        "choice label '{}' conflicts with a message name in the same protocol",
                        key
                    ),
                ));
            }
            Some(LabelSurface::Choice { .. }) | None => {
                labels.entry(key).or_insert_with(|| LabelSurface::Choice {
                    name: branch.label.clone(),
                });
            }
        }
        collect_label_surfaces(&branch.protocol, labels)?;
    }

    Ok(())
}

fn insert_message_surface(
    labels: &mut BTreeMap<String, LabelSurface>,
    message: &MessageType,
) -> Result<()> {
    let key = message.name.to_string();
    let payload = message.payload.clone();
    match labels.get(&key) {
        Some(LabelSurface::Message {
            payload: existing_payload,
            ..
        }) => {
            let existing = existing_payload
                .as_ref()
                .map(ToString::to_string)
                .unwrap_or_else(|| "<none>".to_string());
            let next = payload
                .as_ref()
                .map(ToString::to_string)
                .unwrap_or_else(|| "<none>".to_string());
            if existing != next {
                return Err(Error::new(
                    message.name.span(),
                    format!(
                        "message '{}' is used with conflicting payload types in the same protocol",
                        key
                    ),
                ));
            }
        }
        Some(LabelSurface::Choice { .. }) => {
            return Err(Error::new(
                message.name.span(),
                format!(
                    "message '{}' conflicts with a choice label in the same protocol",
                    key
                ),
            ));
        }
        None => {
            labels.insert(
                key,
                LabelSurface::Message {
                    name: message.name.clone(),
                    payload,
                },
            );
        }
    }

    Ok(())
}

fn generate_session_types(local_types: &[(Role, LocalType)]) -> Result<TokenStream> {
    let mut output = TokenStream::new();

    for (role, local_type) in local_types {
        let mut state = ChoiceCodegenState::new(role.name().clone());
        let session_body = state.render_local_type(local_type)?;
        let session_name = format_ident!("{}Session", role.name());
        let choice_defs = state.choice_defs;

        output.extend(quote! {
            #(#choice_defs)*

            #[::telltale::session]
            pub type #session_name = #session_body;
        });
    }

    Ok(output)
}

struct ChoiceCodegenState {
    role_name: Ident,
    next_choice_id: usize,
    choice_defs: Vec<TokenStream>,
}

impl ChoiceCodegenState {
    fn new(role_name: Ident) -> Self {
        Self {
            role_name,
            next_choice_id: 0,
            choice_defs: Vec::new(),
        }
    }

    fn render_local_type(&mut self, local_type: &LocalType) -> Result<TokenStream> {
        match local_type {
            LocalType::Send {
                to,
                message,
                continuation,
            } => {
                let continuation = self.render_local_type(continuation)?;
                let to_name = to.name();
                let message_name = &message.name;
                Ok(quote! { ::telltale::Send<#to_name, #message_name, #continuation> })
            }
            LocalType::Receive {
                from,
                message,
                continuation,
            } => {
                let continuation = self.render_local_type(continuation)?;
                let from_name = from.name();
                let message_name = &message.name;
                Ok(quote! { ::telltale::Receive<#from_name, #message_name, #continuation> })
            }
            LocalType::Select { to, branches } => {
                let enum_name = self.push_choice_enum(branches)?;
                let to_name = to.name();
                Ok(quote! { ::telltale::Select<#to_name, #enum_name> })
            }
            LocalType::Branch { from, branches } => {
                let enum_name = self.push_choice_enum(branches)?;
                let from_name = from.name();
                Ok(quote! { ::telltale::Branch<#from_name, #enum_name> })
            }
            LocalType::End => Ok(quote! { ::telltale::End }),
            LocalType::Rec { body, .. } => self.render_local_type(body),
            LocalType::Var(label) => Ok(label.to_token_stream()),
            LocalType::Loop { .. } => Err(Error::new(
                Span::call_site(),
                "loop session code generation is not yet supported by telltale-macros",
            )),
            LocalType::LocalChoice { .. } => Err(Error::new(
                Span::call_site(),
                "local-only choice session code generation is not yet supported by telltale-macros",
            )),
            LocalType::Timeout { .. } => Err(Error::new(
                Span::call_site(),
                "timeout session code generation is not yet supported by telltale-macros",
            )),
        }
    }

    fn push_choice_enum(&mut self, branches: &[(Ident, LocalType)]) -> Result<Ident> {
        self.next_choice_id += 1;
        let enum_name = format_ident!("{}Choice{}", self.role_name, self.next_choice_id);
        let variants: Vec<_> = branches
            .iter()
            .map(|(label, local_type)| {
                let continuation = self.render_local_type(local_type)?;
                Ok(quote! { #label(#label, #continuation) })
            })
            .collect::<Result<Vec<_>>>()?;

        self.choice_defs.push(quote! {
            #[::telltale::session]
            pub enum #enum_name {
                #(#variants),*
            }
        });

        Ok(enum_name)
    }
}

fn generate_setup_function(protocol_name: &Ident) -> TokenStream {
    quote! {
        #[doc = concat!("Setup function for the ", stringify!(#protocol_name), " protocol.")]
        pub fn setup() -> Roles {
            Roles::default()
        }
    }
}
