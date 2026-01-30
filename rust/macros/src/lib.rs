//! Procedural macros for Telltale session types.
//!
//! This crate provides derive macros and attribute macros for defining
//! session-typed protocols in Telltale. It includes:
//!
//! - `#[derive(Message)]` - Derive message trait implementations
//! - `#[derive(Role)]` - Derive role trait implementations with routing
//! - `#[derive(Roles)]` - Derive roles container with automatic channel setup
//! - `#[session]` - Transform session type definitions with lifetime parameters
//! - `choreography!` - Define protocols from choreographic descriptions

#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

use proc_macro::TokenStream;

mod choreography;
mod message;
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

/// Procedural macro for defining choreographic protocols.
///
/// Generates role definitions, message types, and session types from a
/// choreographic protocol specification.
///
/// # Example
///
/// ```text
/// choreography! {
///     protocol Simple =
///       roles Client, Server
///       Client -> Server : Hello
///       Server -> Client : Goodbye
/// }
/// ```
#[proc_macro]
pub fn choreography(input: TokenStream) -> TokenStream {
    choreography::choreography(input.into())
        .unwrap_or_else(|err| err.to_compile_error())
        .into()
}
