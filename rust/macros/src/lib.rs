//! Procedural macros for Telltale session types.
//!
//! This crate provides derive macros and attribute macros for defining
//! session-typed protocols in Telltale. It includes:
//!
//! These macros are public convenience surfaces, not part of the current
//! formal-verification claim. They are covered by strict operational and UI
//! regression gates rather than a mechanized macro-correctness proof today.
//!
//! - `#[derive(Message)]` - Derive message trait implementations
//! - `#[derive(Role)]` - Derive role trait implementations with routing
//! - `#[derive(Roles)]` - Derive roles container with automatic channel setup
//! - `#[session]` - Transform session type definitions with lifetime parameters
//! - `tell!` - Define protocols from Telltale DSL specifications

use proc_macro::TokenStream;

mod choreography;
mod message;
mod ownership;
mod parse;
mod role;
mod roles;
mod session;

/// Derives the `Message` trait for message types.
///
/// For structs, implements the identity conversion. For enums, implements
/// conversions for each variant type.
///
/// # Example
///
/// ```text
/// #[derive(Message)]
/// enum Label {
///     Hello(Hello),
///     Goodbye(Goodbye),
/// }
/// ```
#[proc_macro_derive(Message)]
pub fn message(input: TokenStream) -> TokenStream {
    message::message(input.into())
        .unwrap_or_else(|err| err.to_compile_error())
        .into()
}

/// Derives the `Role` trait for role types.
///
/// Requires `#[message(MessageType)]` attribute to specify the message type,
/// and `#[route(OtherRole)]` attributes on fields to specify communication routes.
///
/// # Example
///
/// ```text
/// #[derive(Role)]
/// #[message(Label)]
/// struct Client(#[route(Server)] Channel);
/// ```
#[proc_macro_derive(Role, attributes(message, route))]
pub fn role(input: TokenStream) -> TokenStream {
    role::role(input.into())
        .unwrap_or_else(|err| err.to_compile_error())
        .into()
}

/// Derives the `Default` trait for a roles container with automatic channel setup.
///
/// Creates paired channels between all roles automatically.
///
/// # Example
///
/// ```text
/// #[derive(Roles)]
/// struct MyRoles(Client, Server);
/// ```
#[proc_macro_derive(Roles)]
pub fn roles(input: TokenStream) -> TokenStream {
    roles::roles(input.into())
        .unwrap_or_else(|err| err.to_compile_error())
        .into()
}

/// Attribute macro for session type definitions.
///
/// Augments type aliases, structs, and enums with the necessary lifetime parameters
/// and trait implementations for session types.
///
/// # Example
///
/// ```text
/// #[session]
/// type ClientSession = Send<Server, Hello, Receive<Server, Goodbye, End>>;
/// ```
#[proc_macro_attribute]
pub fn session(attr: TokenStream, input: TokenStream) -> TokenStream {
    session::session(attr.into(), input.into())
        .unwrap_or_else(|err| err.to_compile_error())
        .into()
}

/// Procedural macro for defining Telltale protocol specifications.
///
/// Generates a protocol module with the canonical spec/effect surfaces and,
/// when projectable, a derived `sessions` submodule.
///
/// # Example
///
/// ```text
/// tell! {
///     protocol Simple =
///       roles Client, Server
///       Client -> Server : Hello
///       Server -> Client : Goodbye
/// }
/// ```
#[proc_macro]
pub fn tell(input: TokenStream) -> TokenStream {
    choreography::tell(input)
        .unwrap_or_else(|err| err.to_compile_error())
        .into()
}

/// Marks an observed-only surface that must not become an authoritative owner.
#[proc_macro_attribute]
pub fn observed_only(attr: TokenStream, input: TokenStream) -> TokenStream {
    ownership::observed_only(attr.into(), input.into())
        .unwrap_or_else(|err| err.to_compile_error())
        .into()
}

/// Marks an actor-owned async/runtime surface with an explicit owner label.
#[proc_macro_attribute]
pub fn actor_owned(attr: TokenStream, input: TokenStream) -> TokenStream {
    ownership::actor_owned(attr.into(), input.into())
        .unwrap_or_else(|err| err.to_compile_error())
        .into()
}

/// Marks a function or module that mints an authoritative-source projection.
#[proc_macro_attribute]
pub fn authoritative_source(attr: TokenStream, input: TokenStream) -> TokenStream {
    ownership::authoritative_source(attr.into(), input.into())
        .unwrap_or_else(|err| err.to_compile_error())
        .into()
}

/// Marks a strong-reference boundary in UI/viewer plumbing.
#[proc_macro_attribute]
pub fn strong_reference(attr: TokenStream, input: TokenStream) -> TokenStream {
    ownership::strong_reference(attr.into(), input.into())
        .unwrap_or_else(|err| err.to_compile_error())
        .into()
}

/// Marks a weak identifier that must not be silently upgraded.
#[proc_macro_attribute]
pub fn weak_identifier(attr: TokenStream, input: TokenStream) -> TokenStream {
    ownership::weak_identifier(attr.into(), input.into())
        .unwrap_or_else(|err| err.to_compile_error())
        .into()
}
