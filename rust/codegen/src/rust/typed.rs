//! Typed Runner Wrapper Generation
//!
//! This module generates type-safe runner wrappers that handle serialization
//! internally, providing a cleaner API for protocol execution.
//!
//! Uses `rumpsteak_types::LocalTypeR` as input.
//!
//! # Generated Code Structure
//!
//! For a protocol `Consensus` with role `Coordinator`, this generates:
//!
//! ```ignore
//! /// Input parameters for Coordinator role
//! pub struct ConsensusCoordinatorParams {
//!     pub proposal: Proposal,
//! }
//!
//! /// Output results from Coordinator role
//! pub struct ConsensusCoordinatorResult {
//!     pub decision: Decision,
//! }
//!
//! /// Typed runner for Coordinator role
//! pub struct ConsensusCoordinatorRunner;
//!
//! impl ConsensusCoordinatorRunner {
//!     pub async fn run_typed<A: Adapter>(
//!         adapter: &mut A,
//!         params: ConsensusCoordinatorParams,
//!     ) -> Result<ConsensusCoordinatorResult, Error>;
//! }
//! ```

use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use rumpsteak_types::{Label, LocalTypeR};
use std::collections::HashSet;

/// Configuration for serialization in typed wrappers.
#[derive(Debug, Clone, Default)]
pub struct SerializationConfig {
    /// The serialization format to use.
    pub format: SerializationFormat,
    /// Whether to include type information in errors.
    pub include_type_info: bool,
}

/// Supported serialization formats.
#[derive(Debug, Clone, Copy, Default)]
pub enum SerializationFormat {
    /// Binary format using bincode (default, most efficient).
    #[default]
    Bincode,
    /// JSON format using serde_json (good for debugging).
    Json,
    /// CBOR format using dag_cbor (good for IPLD compatibility).
    DagCbor,
}

impl SerializationFormat {
    /// Get the serialization expression for this format.
    fn serialize_expr(&self, value: TokenStream) -> TokenStream {
        match self {
            SerializationFormat::Bincode => quote! {
                bincode::serialize(&#value)
                    .map_err(|e| Error::Serialization(format!("bincode: {}", e)))?
            },
            SerializationFormat::Json => quote! {
                serde_json::to_vec(&#value)
                    .map_err(|e| Error::Serialization(format!("json: {}", e)))?
            },
            SerializationFormat::DagCbor => quote! {
                serde_ipld_dagcbor::to_vec(&#value)
                    .map_err(|e| Error::Serialization(format!("dag-cbor: {}", e)))?
            },
        }
    }

    /// Get the deserialization expression for this format.
    fn deserialize_expr(&self, bytes: TokenStream, type_name: TokenStream) -> TokenStream {
        match self {
            SerializationFormat::Bincode => quote! {
                bincode::deserialize::<#type_name>(&#bytes)
                    .map_err(|e| Error::Serialization(format!("bincode deserialize {}: {}", stringify!(#type_name), e)))?
            },
            SerializationFormat::Json => quote! {
                serde_json::from_slice::<#type_name>(&#bytes)
                    .map_err(|e| Error::Serialization(format!("json deserialize {}: {}", stringify!(#type_name), e)))?
            },
            SerializationFormat::DagCbor => quote! {
                serde_ipld_dagcbor::from_slice::<#type_name>(&#bytes)
                    .map_err(|e| Error::Serialization(format!("dag-cbor deserialize {}: {}", stringify!(#type_name), e)))?
            },
        }
    }
}

/// Message direction for a role.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MessageDirection {
    /// Message is sent by this role (input to the role's logic).
    Input,
    /// Message is received by this role (output from the role's logic).
    Output,
}

/// Information about a message type used by a role.
#[derive(Debug, Clone)]
pub struct RoleMessageInfo {
    /// The message label.
    pub label: Label,
    /// Whether this is an input or output for the role.
    pub direction: MessageDirection,
    /// The partner role involved in this message.
    pub partner: String,
}

/// Extract all message labels used by a role from its local type.
pub fn extract_role_messages(local_type: &LocalTypeR) -> Vec<RoleMessageInfo> {
    let mut messages = Vec::new();
    extract_messages_recursive(local_type, &mut messages, &mut HashSet::new());
    messages
}

fn extract_messages_recursive(
    local_type: &LocalTypeR,
    messages: &mut Vec<RoleMessageInfo>,
    seen: &mut HashSet<String>,
) {
    match local_type {
        LocalTypeR::Send { partner, branches } => {
            for (label, continuation) in branches {
                let key = format!("send:{}", label.name);
                if !seen.contains(&key) {
                    seen.insert(key);
                    messages.push(RoleMessageInfo {
                        label: label.clone(),
                        direction: MessageDirection::Input,
                        partner: partner.clone(),
                    });
                }
                extract_messages_recursive(continuation, messages, seen);
            }
        }
        LocalTypeR::Recv { partner, branches } => {
            for (label, continuation) in branches {
                let key = format!("recv:{}", label.name);
                if !seen.contains(&key) {
                    seen.insert(key);
                    messages.push(RoleMessageInfo {
                        label: label.clone(),
                        direction: MessageDirection::Output,
                        partner: partner.clone(),
                    });
                }
                extract_messages_recursive(continuation, messages, seen);
            }
        }
        LocalTypeR::Mu { body, .. } => {
            extract_messages_recursive(body, messages, seen);
        }
        LocalTypeR::End | LocalTypeR::Var(_) => {}
    }
}

/// Generate a typed runner wrapper for a role.
///
/// # Arguments
///
/// * `protocol_name` - Name of the protocol
/// * `role_name` - Name of the role
/// * `local_type` - The projected local type for this role
/// * `config` - Serialization configuration
///
/// # Returns
///
/// A TokenStream containing the typed wrapper structs and impl.
#[must_use]
pub fn generate_typed_runner(
    protocol_name: &str,
    role_name: &str,
    local_type: &LocalTypeR,
    config: &SerializationConfig,
) -> TokenStream {
    // Generate type names
    let params_type = format_ident!("{}{}Params", protocol_name, role_name);
    let result_type = format_ident!("{}{}Result", protocol_name, role_name);
    let runner_type = format_ident!("{}{}Runner", protocol_name, role_name);

    // Extract messages for this role
    let messages = extract_role_messages(local_type);

    // Separate inputs and outputs
    let inputs: Vec<_> = messages
        .iter()
        .filter(|m| m.direction == MessageDirection::Input)
        .collect();
    let outputs: Vec<_> = messages
        .iter()
        .filter(|m| m.direction == MessageDirection::Output)
        .collect();

    // Generate params struct fields
    let param_fields: Vec<TokenStream> = inputs
        .iter()
        .map(|m| {
            let field_name = format_ident!("{}", to_snake_case(&m.label.name));
            let field_type = format_ident!("{}", &m.label.name);
            quote! {
                pub #field_name: #field_type
            }
        })
        .collect();

    // Generate result struct fields
    let result_fields: Vec<TokenStream> = outputs
        .iter()
        .map(|m| {
            let field_name = format_ident!("{}", to_snake_case(&m.label.name));
            let field_type = format_ident!("{}", &m.label.name);
            quote! {
                pub #field_name: Option<#field_type>
            }
        })
        .collect();

    // Generate params struct
    let params_struct = if param_fields.is_empty() {
        quote! {
            /// Input parameters for role (no inputs).
            #[derive(Debug, Clone, Default)]
            pub struct #params_type;
        }
    } else {
        quote! {
            /// Input parameters for role.
            #[derive(Debug, Clone)]
            pub struct #params_type {
                #(#param_fields),*
            }
        }
    };

    // Generate result struct
    let result_struct = if result_fields.is_empty() {
        quote! {
            /// Output results from role (no outputs).
            #[derive(Debug, Clone, Default)]
            pub struct #result_type;
        }
    } else {
        quote! {
            /// Output results from role.
            #[derive(Debug, Clone, Default)]
            pub struct #result_type {
                #(#result_fields),*
            }
        }
    };

    // Generate serialization helpers based on config
    let serialize_fn = generate_serialize_helper(config);
    let deserialize_fn = generate_deserialize_helper(config);

    // Generate the runner struct and impl
    let protocol_str = protocol_name;
    let role_str = role_name;

    quote! {
        #params_struct

        #result_struct

        /// Typed runner for role in protocol.
        ///
        /// This runner provides a type-safe interface that handles serialization
        /// internally.
        #[derive(Debug, Clone, Copy, Default)]
        pub struct #runner_type;

        impl #runner_type {
            /// Create a new runner instance.
            #[must_use]
            pub fn new() -> Self {
                Self
            }

            /// Run the protocol with typed parameters and results.
            pub async fn run_typed<A: Adapter>(
                adapter: &mut A,
                params: #params_type,
            ) -> Result<#result_type, Error> {
                let ctx = ProtocolContext::new(#protocol_str, #role_str);
                Self::run_impl(adapter, &ctx, params).await
            }

            /// Internal implementation that runs the protocol logic.
            async fn run_impl<A: Adapter>(
                adapter: &mut A,
                ctx: &ProtocolContext,
                _params: #params_type,
            ) -> Result<#result_type, Error> {
                let _ = ctx; // Context available for future use
                let _ = adapter;

                // TODO: Generated protocol execution logic goes here
                // This is a placeholder - actual implementation would be generated
                // from the local type

                Ok(#result_type::default())
            }

            #serialize_fn

            #deserialize_fn
        }
    }
}

/// Generate a serialize helper function based on config.
fn generate_serialize_helper(config: &SerializationConfig) -> TokenStream {
    let serialize_body = config.format.serialize_expr(quote! { value });

    quote! {
        /// Serialize a value using the configured format.
        #[allow(dead_code)]
        fn serialize<T: serde::Serialize>(value: &T) -> Result<Vec<u8>, Error> {
            Ok(#serialize_body)
        }
    }
}

/// Generate a deserialize helper function based on config.
fn generate_deserialize_helper(config: &SerializationConfig) -> TokenStream {
    let deserialize_body = config
        .format
        .deserialize_expr(quote! { bytes }, quote! { T });

    quote! {
        /// Deserialize a value using the configured format.
        #[allow(dead_code)]
        fn deserialize<T: serde::de::DeserializeOwned>(bytes: &[u8]) -> Result<T, Error> {
            Ok(#deserialize_body)
        }
    }
}

/// Convert a PascalCase string to snake_case.
fn to_snake_case(s: &str) -> String {
    let mut result = String::new();
    for (i, c) in s.chars().enumerate() {
        if c.is_uppercase() {
            if i > 0 {
                result.push('_');
            }
            result.push(c.to_ascii_lowercase());
        } else {
            result.push(c);
        }
    }
    result
}

/// Generate typed runners for all roles in a protocol.
///
/// # Arguments
///
/// * `protocol_name` - Name of the protocol
/// * `local_types` - Vector of (role_name, local_type) pairs
/// * `config` - Serialization configuration
///
/// # Returns
///
/// A TokenStream containing all typed wrapper structs and impls.
#[must_use]
pub fn generate_all_typed_runners(
    protocol_name: &str,
    local_types: &[(&str, &LocalTypeR)],
    config: &SerializationConfig,
) -> TokenStream {
    let runners: Vec<TokenStream> = local_types
        .iter()
        .map(|(role_name, local_type)| {
            generate_typed_runner(protocol_name, role_name, local_type, config)
        })
        .collect();

    quote! {
        /// Typed runner wrappers for protocol execution.
        pub mod typed_runners {
            use super::*;

            /// Error type for typed runners
            #[derive(Debug)]
            pub enum Error {
                Serialization(String),
                Protocol(String),
            }

            impl std::fmt::Display for Error {
                fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                    match self {
                        Error::Serialization(msg) => write!(f, "Serialization error: {}", msg),
                        Error::Protocol(msg) => write!(f, "Protocol error: {}", msg),
                    }
                }
            }

            impl std::error::Error for Error {}

            /// Adapter trait for communication
            pub trait Adapter {
                type Error;
                async fn send<M>(&mut self, to: RoleId, msg: M) -> Result<(), Self::Error>;
                async fn recv<M>(&mut self, from: RoleId) -> Result<M, Self::Error>;
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

            #(#runners)*
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_extract_role_messages() {
        let local_type = LocalTypeR::send(
            "Server",
            Label::new("Request"),
            LocalTypeR::recv("Server", Label::new("Response"), LocalTypeR::End),
        );

        let messages = extract_role_messages(&local_type);
        assert_eq!(messages.len(), 2);
        assert_eq!(messages[0].direction, MessageDirection::Input);
        assert_eq!(messages[1].direction, MessageDirection::Output);
    }

    #[test]
    fn test_to_snake_case() {
        assert_eq!(to_snake_case("Request"), "request");
        assert_eq!(to_snake_case("MyMessage"), "my_message");
        assert_eq!(to_snake_case("HTTPRequest"), "h_t_t_p_request");
    }

    #[test]
    fn test_generate_typed_runner() {
        let local_type = LocalTypeR::send("Server", Label::new("Request"), LocalTypeR::End);

        let config = SerializationConfig::default();
        let tokens = generate_typed_runner("TestProtocol", "Client", &local_type, &config);

        let code = tokens.to_string();
        assert!(code.contains("TestProtocolClientParams"));
        assert!(code.contains("TestProtocolClientResult"));
        assert!(code.contains("TestProtocolClientRunner"));
        assert!(code.contains("run_typed"));
    }
}
