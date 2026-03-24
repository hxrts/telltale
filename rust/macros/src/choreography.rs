//! Choreographic protocol definition macro implementation.
//!
//! Parsing is delegated to the shared Telltale choreography frontend. This
//! proc-macro then lowers the parsed choreography into the historical
//! `telltale-macros` output surface: message structs, a `Label` enum, public
//! role structs, `Roles`, per-role session aliases, and `setup()`.

use proc_macro::{Delimiter, TokenStream as MacroTokenStream, TokenTree as MacroTokenTree};
use proc_macro2::{Ident, Span, TokenStream};
use quote::{format_ident, quote, ToTokens};
use std::collections::{BTreeMap, HashMap};
use syn::{Error, LitStr, Result};
use telltale_parser::ast::{Branch, Choreography, LocalType, MessageType, Protocol, Role};

/// Main entry point for the choreography! macro.
pub fn choreography(input: MacroTokenStream) -> Result<TokenStream> {
    let choreography = parse_macro_choreography(input)?;
    choreography
        .validate()
        .map_err(|err| Error::new(Span::call_site(), err.to_string()))?;

    let local_types = project_local_types(&choreography)?;
    let generated = generate_protocol_module(&choreography, &local_types)?;
    Ok(generated)
}

fn parse_macro_choreography(input: MacroTokenStream) -> Result<Choreography> {
    if let Ok(lit_str) = syn::parse::<LitStr>(input.clone()) {
        return Err(Error::new(
            lit_str.span(),
            "string-literal choreography input was removed; use the canonical indentation-based token DSL directly",
        ));
    }

    let source = macro_source_text(input)
        .map(normalize_macro_indentation)
        .ok_or_else(|| {
            Error::new(
                Span::call_site(),
                "failed to recover original choreography source from macro input",
            )
        })?;

    telltale_parser::parse_choreography_str(&source).map_err(|err| {
        Error::new(
            Span::call_site(),
            format!(
                "Choreography parse error: {err}\n\
                 Macro token input is parsed from original source text.\n\
                 Use the canonical indentation-based DSL surface in token form."
            ),
        )
    })
}

fn normalize_macro_indentation(source: String) -> String {
    const TOP_LEVEL_HEADERS: &[&str] = &[
        "module ",
        "import ",
        "protocol ",
        "proof_bundle ",
        "role_set ",
        "topology ",
        "type ",
        "effect ",
        "fragment ",
        "operation ",
        "guest runtime ",
    ];

    let mut normalized = String::new();
    for line in source.lines() {
        let trimmed = line.trim_start();
        if TOP_LEVEL_HEADERS
            .iter()
            .any(|prefix| trimmed.starts_with(prefix))
        {
            normalized.push_str(trimmed);
        } else {
            normalized.push_str(line);
        }
        normalized.push('\n');
    }

    if !source.ends_with('\n') {
        normalized.pop();
    }
    normalized
}

fn macro_source_text(input: MacroTokenStream) -> Option<String> {
    #[derive(Clone, Copy)]
    struct Location {
        line: usize,
        column: usize,
    }

    fn location_of(start: proc_macro::Span) -> (Location, Location) {
        let start_loc = start.start();
        let end_loc = start.end();
        (
            Location {
                line: start_loc.line(),
                column: start_loc.column(),
            },
            Location {
                line: end_loc.line(),
                column: end_loc.column(),
            },
        )
    }

    fn append_gap(out: &mut String, previous_end: Location, next_start: Location) {
        if next_start.line > previous_end.line {
            for _ in previous_end.line..next_start.line {
                out.push('\n');
            }
            for _ in 0..next_start.column {
                out.push(' ');
            }
        } else if next_start.column > previous_end.column {
            for _ in previous_end.column..next_start.column {
                out.push(' ');
            }
        }
    }

    fn append_stream(
        out: &mut String,
        previous_end: &mut Option<Location>,
        stream: MacroTokenStream,
    ) -> Option<()> {
        for token in stream {
            match token {
                MacroTokenTree::Group(group) => {
                    let (open_start, _) = location_of(group.span_open());
                    let (_, close_end) = location_of(group.span_close());
                    if let Some(prev) = previous_end.as_ref() {
                        append_gap(out, *prev, open_start);
                    }
                    out.push_str(&group.to_string());
                    *previous_end = Some(close_end);
                }
                MacroTokenTree::Ident(ident) => {
                    let span = ident.span();
                    let (start, end) = location_of(span);
                    if let Some(prev) = previous_end.as_ref() {
                        append_gap(out, *prev, start);
                    }
                    out.push_str(&ident.to_string());
                    *previous_end = Some(end);
                }
                MacroTokenTree::Punct(punct) => {
                    let span = punct.span();
                    let (start, end) = location_of(span);
                    if let Some(prev) = previous_end.as_ref() {
                        append_gap(out, *prev, start);
                    }
                    out.push(punct.as_char());
                    *previous_end = Some(end);
                }
                MacroTokenTree::Literal(literal) => {
                    let span = literal.span();
                    let (start, end) = location_of(span);
                    if let Some(prev) = previous_end.as_ref() {
                        append_gap(out, *prev, start);
                    }
                    out.push_str(&literal.to_string());
                    *previous_end = Some(end);
                }
            }
        }
        Some(())
    }

    fn strip_group_source(source: &str, delimiter: Delimiter) -> String {
        let trimmed = source.trim();
        match delimiter {
            Delimiter::Parenthesis | Delimiter::Brace | Delimiter::Bracket
                if trimmed.len() >= 2 =>
            {
                trimmed[1..trimmed.len() - 1].to_string()
            }
            _ => trimmed.to_string(),
        }
    }

    let mut tokens = input.clone().into_iter();
    if let Some(MacroTokenTree::Group(group)) = tokens.next() {
        let single_group = tokens.next().is_none();
        if single_group {
            if let Some(source) = group.span().source_text() {
                return Some(strip_group_source(&source, group.delimiter()));
            }
        }
        if single_group && group.delimiter() == Delimiter::Brace {
            return macro_source_text(group.stream());
        }
    }

    let mut out = String::new();
    let mut previous_end = None;
    append_stream(&mut out, &mut previous_end, input)?;
    Some(out)
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
            // When a message with the same name already exists, the choice
            // label reuses the message struct (the payload carries the label).
            Some(LabelSurface::Message { .. }) => {}
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
            // Promote the choice label to a message — the payload-carrying
            // message struct doubles as the choice dispatch label.
            labels.insert(
                key,
                LabelSurface::Message {
                    name: message.name.clone(),
                    payload,
                },
            );
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
    /// Maps `rec` labels to the session-type token streams they produce.
    /// Populated when entering a `Rec` node so that inner `Var`
    /// references resolve to e.g. `Select<Peer, Enum>` or
    /// `Branch<Peer, Enum>`.
    rec_labels: HashMap<String, TokenStream>,
}

impl ChoiceCodegenState {
    fn new(role_name: Ident) -> Self {
        Self {
            role_name,
            next_choice_id: 0,
            choice_defs: Vec::new(),
            rec_labels: HashMap::new(),
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
            LocalType::Rec { label, body } => {
                // Pre-register the session type that the body will
                // produce, so that inner `Var` references resolve to
                // `Select<Peer, Enum>` or `Branch<Peer, Enum>` rather
                // than a bare enum name.
                let predicted_id = self.next_choice_id + 1;
                let predicted_name = format_ident!("{}Choice{}", self.role_name, predicted_id);
                let predicted_tokens = match body.as_ref() {
                    LocalType::Select { to, .. } => {
                        let to_name = to.name();
                        quote! { ::telltale::Select<#to_name, #predicted_name> }
                    }
                    LocalType::Branch { from, .. } => {
                        let from_name = from.name();
                        quote! { ::telltale::Branch<#from_name, #predicted_name> }
                    }
                    _ => predicted_name.to_token_stream(),
                };
                self.rec_labels.insert(label.to_string(), predicted_tokens);
                self.render_local_type(body)
            }
            LocalType::Var(label) => {
                if let Some(tokens) = self.rec_labels.get(&label.to_string()) {
                    Ok(tokens.clone())
                } else {
                    Ok(label.to_token_stream())
                }
            }
            LocalType::Loop { body, .. } => {
                // Bounded/unbounded loops lower to their body. The runtime
                // controls iteration; the session type describes one pass.
                self.render_local_type(body)
            }
            LocalType::LocalChoice { branches } => {
                // Local decisions without communication still need a choice
                // enum so the implementation can branch.  We generate a
                // `Select`-style enum without a partner role; the runtime
                // dispatcher uses it structurally.
                let enum_name = self.push_choice_enum(branches)?;
                Ok(quote! { ::telltale::Select<Self, #enum_name> })
            }
            LocalType::Timeout { body, .. } => {
                // Timeout is a runtime concern. The session type for the
                // happy path is the body; timeout/cancel paths are handled
                // by the handler at runtime.
                self.render_local_type(body)
            }
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
