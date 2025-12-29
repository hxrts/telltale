//! Rust Code Generation
//!
//! This module generates Rust code from the intermediate representation.
//!
//! # Modules
//!
//! - `session` - Session type generation (Send/Recv/Choose/Offer)
//! - `roles` - Role struct generation
//! - `messages` - Message type generation
//! - `runners` - Runner function generation
//! - `typed` - Typed runner wrapper generation
//! - `effects` - Effects-based protocol generation
//! - `concurrency` - Concurrency control utilities

mod concurrency;
mod effects;
mod messages;
mod roles;
mod runners;
mod session;
mod typed;

pub use concurrency::{
    generate_batch_recv, generate_batch_send, generate_broadcast, generate_collection,
    generate_ordered_collection, generate_parallel_broadcast, generate_sequential_broadcast,
    generate_unordered_collection, BatchConfig, BroadcastMode, CollectionMode,
    ProtocolConcurrencyConfig, StatementConcurrencyConfig,
};
pub use effects::{generate_effects_protocol, interpret, Handler, InterpretResult, Label, Program};
pub use messages::generate_messages;
pub use roles::generate_role;
pub use runners::{
    generate_all_runners, generate_execute_as, generate_output_types, generate_role_enum,
    generate_runner_fn,
};
pub use session::generate_session_type;
pub use typed::{
    extract_role_messages, generate_all_typed_runners, generate_typed_runner, MessageDirection,
    RoleMessageInfo, SerializationConfig, SerializationFormat,
};

use crate::ir::CodegenIR;
use proc_macro2::TokenStream;
use quote::quote;

/// Generate a complete protocol module
pub fn generate_protocol(ir: &CodegenIR) -> TokenStream {
    let name = syn::Ident::new(&ir.name, proc_macro2::Span::call_site());

    let role_code: Vec<TokenStream> = ir.protocol.roles.iter().map(generate_role).collect();

    let message_code = generate_messages(&ir.protocol.messages);

    quote! {
        pub mod #name {
            #message_code

            #(#role_code)*
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{MessageIR, ProtocolIR, RoleIR};
    use rumpsteak_types::{Label, LocalTypeR};

    #[test]
    fn test_generate_protocol() {
        let mut protocol = ProtocolIR::new();
        protocol.add_role(RoleIR::new("Client", LocalTypeR::End));
        protocol.add_message(MessageIR::new(Label::new("hello"), false));

        let ir = CodegenIR::new("ping_pong", protocol);
        let code = generate_protocol(&ir);

        let code_str = code.to_string();
        assert!(code_str.contains("ping_pong"));
    }
}
