//! Concurrency Control Codegen
//!
//! This module provides code generation utilities for controlling
//! concurrent vs sequential execution of broadcast and collection operations.
//!
//! # Broadcast Modes
//!
//! - **Parallel** (default): Use `try_join_all` to send to all recipients concurrently
//! - **Sequential**: Send to recipients one at a time in order
//!
//! # Collection Modes
//!
//! - **Ordered**: Collect responses in a deterministic order (default)
//! - **Unordered**: Collect responses as they arrive using `select_all`
//!
//! # Annotations
//!
//! - `#[sequential]` - Force sequential execution
//! - `#[unordered]` - Allow unordered collection
//! - `#[batch]` - Combine multiple messages into a single send

use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use std::collections::HashMap;

/// Broadcast execution mode
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum BroadcastMode {
    /// Send to all recipients concurrently using try_join_all
    #[default]
    Parallel,
    /// Send to recipients sequentially in order
    Sequential,
}

impl BroadcastMode {
    /// Parse from annotation string
    #[must_use]
    pub fn from_annotation(value: &str) -> Option<Self> {
        match value.to_lowercase().as_str() {
            "parallel" | "concurrent" => Some(Self::Parallel),
            "sequential" | "ordered" | "seq" => Some(Self::Sequential),
            _ => None,
        }
    }

    /// Get annotation name
    #[must_use]
    pub fn annotation_name(&self) -> &'static str {
        match self {
            Self::Parallel => "parallel",
            Self::Sequential => "sequential",
        }
    }
}

/// Collection execution mode
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum CollectionMode {
    /// Collect responses in deterministic order
    #[default]
    Ordered,
    /// Collect responses as they arrive (parallel)
    Unordered,
}

impl CollectionMode {
    /// Parse from annotation string
    #[must_use]
    pub fn from_annotation(value: &str) -> Option<Self> {
        match value.to_lowercase().as_str() {
            "ordered" | "sequential" | "ordered_collection" => Some(Self::Ordered),
            "unordered" | "parallel" | "any_order" => Some(Self::Unordered),
            _ => None,
        }
    }

    /// Get annotation name
    #[must_use]
    pub fn annotation_name(&self) -> &'static str {
        match self {
            Self::Ordered => "ordered",
            Self::Unordered => "unordered",
        }
    }
}

/// Configuration for batch operations
#[derive(Debug, Clone, Default)]
pub struct BatchConfig {
    /// Messages in the batch
    pub messages: Vec<String>,
    /// Whether to auto-unwrap on receive
    pub auto_unwrap: bool,
}

/// Generate parallel broadcast code
///
/// Generates code like:
/// ```ignore
/// futures::future::try_join_all(
///     recipients.iter().map(|r| adapter.send(*r, payload.clone()))
/// ).await?;
/// ```
pub fn generate_parallel_broadcast(
    adapter_name: &str,
    recipients_name: &str,
    payload_name: &str,
) -> TokenStream {
    let adapter = format_ident!("{}", adapter_name);
    let recipients = format_ident!("{}", recipients_name);
    let payload = format_ident!("{}", payload_name);

    quote! {
        futures::future::try_join_all(
            #recipients.iter().map(|r| #adapter.send(*r, #payload.clone()))
        ).await?;
    }
}

/// Generate sequential broadcast code
///
/// Generates code like:
/// ```ignore
/// for recipient in &recipients {
///     adapter.send(*recipient, payload.clone()).await?;
/// }
/// ```
pub fn generate_sequential_broadcast(
    adapter_name: &str,
    recipients_name: &str,
    payload_name: &str,
) -> TokenStream {
    let adapter = format_ident!("{}", adapter_name);
    let recipients = format_ident!("{}", recipients_name);
    let payload = format_ident!("{}", payload_name);

    quote! {
        for recipient in &#recipients {
            #adapter.send(*recipient, #payload.clone()).await?;
        }
    }
}

/// Generate broadcast code based on mode
pub fn generate_broadcast(
    mode: BroadcastMode,
    adapter_name: &str,
    recipients_name: &str,
    payload_name: &str,
) -> TokenStream {
    match mode {
        BroadcastMode::Parallel => {
            generate_parallel_broadcast(adapter_name, recipients_name, payload_name)
        }
        BroadcastMode::Sequential => {
            generate_sequential_broadcast(adapter_name, recipients_name, payload_name)
        }
    }
}

/// Generate ordered collection code
///
/// Generates code like:
/// ```ignore
/// let mut responses = Vec::with_capacity(senders.len());
/// for sender in &senders {
///     let msg = adapter.recv::<ResponseType>(*sender).await?;
///     responses.push(msg);
/// }
/// ```
pub fn generate_ordered_collection(
    adapter_name: &str,
    senders_name: &str,
    response_type: &str,
    result_name: &str,
) -> TokenStream {
    let adapter = format_ident!("{}", adapter_name);
    let senders = format_ident!("{}", senders_name);
    let response_ty = format_ident!("{}", response_type);
    let result = format_ident!("{}", result_name);

    quote! {
        let mut #result = Vec::with_capacity(#senders.len());
        for sender in &#senders {
            let msg = #adapter.recv::<#response_ty>(*sender).await?;
            #result.push(msg);
        }
    }
}

/// Generate unordered collection code
///
/// Generates code like:
/// ```ignore
/// use futures::future::select_all;
/// let mut pending: Vec<_> = senders.iter()
///     .map(|s| Box::pin(adapter.recv::<ResponseType>(*s)))
///     .collect();
/// let mut responses = Vec::with_capacity(pending.len());
/// while !pending.is_empty() {
///     let (result, _idx, remaining) = select_all(pending).await;
///     responses.push(result?);
///     pending = remaining;
/// }
/// ```
pub fn generate_unordered_collection(
    adapter_name: &str,
    senders_name: &str,
    response_type: &str,
    result_name: &str,
) -> TokenStream {
    let adapter = format_ident!("{}", adapter_name);
    let senders = format_ident!("{}", senders_name);
    let response_ty = format_ident!("{}", response_type);
    let result = format_ident!("{}", result_name);

    quote! {
        use futures::future::select_all;
        let mut pending: Vec<_> = #senders.iter()
            .map(|s| Box::pin(#adapter.recv::<#response_ty>(*s)))
            .collect();
        let mut #result = Vec::with_capacity(pending.len());
        while !pending.is_empty() {
            let (recv_result, _idx, remaining) = select_all(pending).await;
            #result.push(recv_result?);
            pending = remaining;
        }
    }
}

/// Generate collection code based on mode
pub fn generate_collection(
    mode: CollectionMode,
    adapter_name: &str,
    senders_name: &str,
    response_type: &str,
    result_name: &str,
) -> TokenStream {
    match mode {
        CollectionMode::Ordered => {
            generate_ordered_collection(adapter_name, senders_name, response_type, result_name)
        }
        CollectionMode::Unordered => {
            generate_unordered_collection(adapter_name, senders_name, response_type, result_name)
        }
    }
}

/// Generate batch send code
///
/// Generates code that combines multiple messages into a single payload:
/// ```ignore
/// let batch_payload = BatchPayload {
///     msg_a: a_value,
///     msg_b: b_value,
///     msg_c: c_value,
/// };
/// adapter.send(recipient, batch_payload).await?;
/// ```
pub fn generate_batch_send(
    adapter_name: &str,
    recipient_name: &str,
    message_names: &[(&str, &str)], // (field_name, value_name)
) -> TokenStream {
    let adapter = format_ident!("{}", adapter_name);
    let recipient = format_ident!("{}", recipient_name);

    let field_assignments: Vec<TokenStream> = message_names
        .iter()
        .map(|(field, value)| {
            let field_ident = format_ident!("{}", field);
            let value_ident = format_ident!("{}", value);
            quote! { #field_ident: #value_ident }
        })
        .collect();

    quote! {
        let batch_payload = BatchPayload {
            #(#field_assignments),*
        };
        #adapter.send(#recipient, batch_payload).await?;
    }
}

/// Generate batch receive code
///
/// Generates code that receives a batch and unpacks it:
/// ```ignore
/// let batch: BatchPayload = adapter.recv(sender).await?;
/// let msg_a = batch.msg_a;
/// let msg_b = batch.msg_b;
/// let msg_c = batch.msg_c;
/// ```
pub fn generate_batch_recv(
    adapter_name: &str,
    sender_name: &str,
    batch_type: &str,
    field_names: &[&str],
) -> TokenStream {
    let adapter = format_ident!("{}", adapter_name);
    let sender = format_ident!("{}", sender_name);
    let batch_ty = format_ident!("{}", batch_type);

    let field_extractions: Vec<TokenStream> = field_names
        .iter()
        .map(|field| {
            let field_ident = format_ident!("{}", field);
            quote! { let #field_ident = batch.#field_ident; }
        })
        .collect();

    quote! {
        let batch: #batch_ty = #adapter.recv(#sender).await?;
        #(#field_extractions)*
    }
}

/// Protocol concurrency configuration
#[derive(Debug, Clone, Default)]
pub struct ProtocolConcurrencyConfig {
    /// Default broadcast mode for the protocol
    pub default_broadcast: BroadcastMode,
    /// Default collection mode for the protocol
    pub default_collection: CollectionMode,
}

impl ProtocolConcurrencyConfig {
    /// Create from protocol annotations
    pub fn from_annotations(annotations: &HashMap<String, String>) -> Self {
        let mut config = Self::default();

        if let Some(broadcast) = annotations.get("default_broadcast") {
            if let Some(mode) = BroadcastMode::from_annotation(broadcast) {
                config.default_broadcast = mode;
            }
        }

        if let Some(collection) = annotations.get("default_collection") {
            if let Some(mode) = CollectionMode::from_annotation(collection) {
                config.default_collection = mode;
            }
        }

        config
    }
}

/// Statement concurrency configuration
#[derive(Debug, Clone, Default)]
pub struct StatementConcurrencyConfig {
    /// Broadcast mode for this statement
    pub broadcast_mode: Option<BroadcastMode>,
    /// Collection mode for this statement
    pub collection_mode: Option<CollectionMode>,
    /// Whether this is part of a batch
    pub is_batch: bool,
}

impl StatementConcurrencyConfig {
    /// Create from statement annotations
    pub fn from_annotations(annotations: &HashMap<String, String>) -> Self {
        let mut config = Self::default();

        // Check for explicit mode annotations
        if annotations.contains_key("sequential") {
            config.broadcast_mode = Some(BroadcastMode::Sequential);
        } else if annotations.contains_key("parallel") {
            config.broadcast_mode = Some(BroadcastMode::Parallel);
        }

        if annotations.contains_key("unordered") {
            config.collection_mode = Some(CollectionMode::Unordered);
        } else if annotations.contains_key("ordered") {
            config.collection_mode = Some(CollectionMode::Ordered);
        }

        if annotations.contains_key("batch") {
            config.is_batch = true;
        }

        config
    }

    /// Get effective broadcast mode (falls back to protocol default)
    #[must_use]
    pub fn effective_broadcast_mode(
        &self,
        protocol_config: &ProtocolConcurrencyConfig,
    ) -> BroadcastMode {
        self.broadcast_mode
            .unwrap_or(protocol_config.default_broadcast)
    }

    /// Get effective collection mode (falls back to protocol default)
    #[must_use]
    pub fn effective_collection_mode(
        &self,
        protocol_config: &ProtocolConcurrencyConfig,
    ) -> CollectionMode {
        self.collection_mode
            .unwrap_or(protocol_config.default_collection)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_broadcast_mode_parsing() {
        assert_eq!(
            BroadcastMode::from_annotation("parallel"),
            Some(BroadcastMode::Parallel)
        );
        assert_eq!(
            BroadcastMode::from_annotation("sequential"),
            Some(BroadcastMode::Sequential)
        );
        assert_eq!(
            BroadcastMode::from_annotation("concurrent"),
            Some(BroadcastMode::Parallel)
        );
        assert_eq!(
            BroadcastMode::from_annotation("seq"),
            Some(BroadcastMode::Sequential)
        );
        assert_eq!(BroadcastMode::from_annotation("invalid"), None);
    }

    #[test]
    fn test_collection_mode_parsing() {
        assert_eq!(
            CollectionMode::from_annotation("ordered"),
            Some(CollectionMode::Ordered)
        );
        assert_eq!(
            CollectionMode::from_annotation("unordered"),
            Some(CollectionMode::Unordered)
        );
        assert_eq!(
            CollectionMode::from_annotation("parallel"),
            Some(CollectionMode::Unordered)
        );
        assert_eq!(CollectionMode::from_annotation("invalid"), None);
    }

    #[test]
    fn test_generate_parallel_broadcast() {
        let code = generate_parallel_broadcast("adapter", "witnesses", "msg");
        let code_str = code.to_string();
        assert!(code_str.contains("try_join_all"));
        assert!(code_str.contains("witnesses"));
        assert!(code_str.contains("adapter"));
    }

    #[test]
    fn test_generate_sequential_broadcast() {
        let code = generate_sequential_broadcast("adapter", "witnesses", "msg");
        let code_str = code.to_string();
        assert!(code_str.contains("for recipient"));
        assert!(code_str.contains("witnesses"));
    }

    #[test]
    fn test_generate_ordered_collection() {
        let code = generate_ordered_collection("adapter", "senders", "Response", "responses");
        let code_str = code.to_string();
        assert!(code_str.contains("for sender"));
        assert!(code_str.contains("recv"));
        assert!(code_str.contains("Response"));
    }

    #[test]
    fn test_generate_unordered_collection() {
        let code = generate_unordered_collection("adapter", "senders", "Response", "responses");
        let code_str = code.to_string();
        assert!(code_str.contains("select_all"));
        assert!(code_str.contains("while"));
    }

    #[test]
    fn test_protocol_config_from_annotations() {
        let mut annotations = HashMap::new();
        annotations.insert("default_broadcast".to_string(), "sequential".to_string());
        annotations.insert("default_collection".to_string(), "unordered".to_string());

        let config = ProtocolConcurrencyConfig::from_annotations(&annotations);
        assert_eq!(config.default_broadcast, BroadcastMode::Sequential);
        assert_eq!(config.default_collection, CollectionMode::Unordered);
    }

    #[test]
    fn test_statement_config_from_annotations() {
        let mut annotations = HashMap::new();
        annotations.insert("sequential".to_string(), "true".to_string());
        annotations.insert("batch".to_string(), "true".to_string());

        let config = StatementConcurrencyConfig::from_annotations(&annotations);
        assert_eq!(config.broadcast_mode, Some(BroadcastMode::Sequential));
        assert!(config.is_batch);
    }

    #[test]
    fn test_effective_modes() {
        let protocol_config = ProtocolConcurrencyConfig {
            default_broadcast: BroadcastMode::Sequential,
            default_collection: CollectionMode::Unordered,
        };

        let stmt_config = StatementConcurrencyConfig::default();
        assert_eq!(
            stmt_config.effective_broadcast_mode(&protocol_config),
            BroadcastMode::Sequential
        );
        assert_eq!(
            stmt_config.effective_collection_mode(&protocol_config),
            CollectionMode::Unordered
        );

        let override_config = StatementConcurrencyConfig {
            broadcast_mode: Some(BroadcastMode::Parallel),
            ..Default::default()
        };
        assert_eq!(
            override_config.effective_broadcast_mode(&protocol_config),
            BroadcastMode::Parallel
        );
    }

    #[test]
    fn test_batch_send_generation() {
        let code = generate_batch_send(
            "adapter",
            "recipient",
            &[("msg_a", "a_value"), ("msg_b", "b_value")],
        );
        let code_str = code.to_string();
        assert!(code_str.contains("BatchPayload"));
        assert!(code_str.contains("msg_a"));
        assert!(code_str.contains("msg_b"));
    }

    #[test]
    fn test_batch_recv_generation() {
        let code = generate_batch_recv("adapter", "sender", "BatchPayload", &["msg_a", "msg_b"]);
        let code_str = code.to_string();
        assert!(
            code_str.contains("BatchPayload"),
            "Should contain BatchPayload: {}",
            code_str
        );
        assert!(
            code_str.contains("batch") && code_str.contains("msg_a"),
            "Should reference batch.msg_a: {}",
            code_str
        );
        assert!(
            code_str.contains("batch") && code_str.contains("msg_b"),
            "Should reference batch.msg_b: {}",
            code_str
        );
    }
}
