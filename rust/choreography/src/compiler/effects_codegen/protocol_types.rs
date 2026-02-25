use crate::ast::{MessageType, Protocol};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use std::collections::HashSet;

pub(super) fn generate_message_types(protocol: &Protocol) -> TokenStream {
    let mut message_types = HashSet::new();

    collect_message_types(protocol, &mut message_types);

    let mut message_types: Vec<_> = message_types.into_iter().collect();
    message_types.sort_by(|left, right| {
        left.name
            .to_string()
            .cmp(&right.name.to_string())
            .then_with(|| {
                left.type_annotation
                    .as_ref()
                    .map(ToString::to_string)
                    .cmp(&right.type_annotation.as_ref().map(ToString::to_string))
            })
            .then_with(|| {
                left.payload
                    .as_ref()
                    .map(ToString::to_string)
                    .cmp(&right.payload.as_ref().map(ToString::to_string))
            })
    });

    let message_structs: Vec<_> = message_types
        .into_iter()
        .map(|msg_type| {
            let type_name = &msg_type.name;
            let content_type = if let Some(ref payload) = msg_type.payload {
                payload.clone()
            } else {
                infer_content_type(&msg_type.name.to_string())
            };

            quote! {
                #[derive(Clone, Debug, Serialize, Deserialize)]
                pub struct #type_name(pub #content_type);
            }
        })
        .collect();

    quote! {
        #(#message_structs)*
    }
}

pub(super) fn generate_label_type(protocol: &Protocol) -> TokenStream {
    let mut labels = HashSet::new();
    collect_choice_labels(protocol, &mut labels);

    let mut label_list: Vec<String> = labels.into_iter().collect();
    label_list.sort();

    if label_list.is_empty() {
        return generate_empty_label_type();
    }

    generate_populated_label_type(&label_list)
}

fn generate_empty_label_type() -> TokenStream {
    quote! {
        #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
        pub enum Label {}

        impl LabelId for Label {
            fn as_str(&self) -> &'static str {
                match *self {}
            }

            fn from_str(_label: &str) -> Option<Self> {
                None
            }
        }
    }
}

fn generate_populated_label_type(label_list: &[String]) -> TokenStream {
    let variants = label_list.iter().map(|label| {
        let ident = format_ident!("{}", label);
        quote! { #ident }
    });

    let as_str_arms = label_list.iter().map(|label| {
        let ident = format_ident!("{}", label);
        quote! { Label::#ident => #label }
    });

    let from_str_arms = label_list.iter().map(|label| {
        let ident = format_ident!("{}", label);
        quote! { #label => Some(Label::#ident) }
    });

    quote! {
        #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
        pub enum Label {
            #(#variants),*
        }

        impl LabelId for Label {
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

// RECURSION_SAFE: structural recursion over finite protocol AST depth.
fn collect_message_types(protocol: &Protocol, message_types: &mut HashSet<MessageType>) {
    match protocol {
        Protocol::Send {
            message,
            continuation,
            ..
        } => {
            message_types.insert(message.clone());
            collect_message_types(continuation, message_types);
        }
        Protocol::Broadcast {
            message,
            continuation,
            ..
        } => {
            message_types.insert(message.clone());
            collect_message_types(continuation, message_types);
        }
        Protocol::Choice { branches, .. } => {
            for branch in branches {
                collect_message_types(&branch.protocol, message_types);
            }
        }
        Protocol::Loop { body, .. } => {
            collect_message_types(body, message_types);
        }
        Protocol::Parallel { protocols } => {
            for p in protocols {
                collect_message_types(p, message_types);
            }
        }
        Protocol::Rec { body, .. } => {
            collect_message_types(body, message_types);
        }
        Protocol::Var(_) | Protocol::End => {}

        Protocol::Extension { continuation, .. } => {
            collect_message_types(continuation, message_types);
        }
    }
}

// RECURSION_SAFE: structural recursion over finite protocol AST depth.
fn collect_choice_labels(protocol: &Protocol, labels: &mut HashSet<String>) {
    match protocol {
        Protocol::Choice { branches, .. } => {
            for branch in branches {
                labels.insert(branch.label.to_string());
                collect_choice_labels(&branch.protocol, labels);
            }
        }
        Protocol::Send { continuation, .. }
        | Protocol::Broadcast { continuation, .. }
        | Protocol::Extension { continuation, .. } => {
            collect_choice_labels(continuation, labels);
        }
        Protocol::Loop { body, .. } | Protocol::Rec { body, .. } => {
            collect_choice_labels(body, labels);
        }
        Protocol::Parallel { protocols } => {
            for proto in protocols {
                collect_choice_labels(proto, labels);
            }
        }
        Protocol::Var(_) | Protocol::End => {}
    }
}

fn infer_content_type(message_type: &str) -> TokenStream {
    match message_type {
        s if s.contains("Request") => quote! { String },
        s if s.contains("Response") => quote! { String },
        s if s.contains("Data") => quote! { Vec<u8> },
        s if s.contains("Count") => quote! { u64 },
        s if s.contains("Flag") => quote! { bool },
        _ => quote! { String },
    }
}
