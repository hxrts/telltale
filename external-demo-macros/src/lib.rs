//! External Demo Macros - Proc Macro Crate
//!
//! This crate provides additional proc macros for the external demo,
//! demonstrating how 3rd party projects can create their own macros
//! while still using rumpsteak-aura's choreography! macro for protocols.

use proc_macro::TokenStream;

mod effect_handlers;
mod choreography;

/// Full-featured choreography! macro with ALL rumpsteak-aura features
///
/// This macro provides access to ALL rumpsteak-aura features including:
/// - Module declarations: `module my_protocol exposing (MyProtocol)`
/// - Parameterized roles: `Worker[N]`, `Signer[*]`
/// - Choice constructs: `choice at Role { ... }`
/// - Loop constructs: `loop repeat N { ... }`, `loop decide by Role { ... }`
/// - Extension system integration
///
/// # Example
///
/// ```ignore
/// use external_demo::choreography;
///
/// choreography! {
///     module threshold_ceremony exposing (ThresholdExample)
///     protocol ThresholdExample = {
///         roles Coordinator, Signer[N]
///
///         choice at Coordinator {
///             start_ceremony -> {
///                 Coordinator -> Signer[*] : StartRequest
///                 Signer[*] -> Coordinator : Commitment
///                 Coordinator -> Signer[*] : Challenge
///                 Signer[*] -> Coordinator : Response
///             }
///             abort -> {
///                 Coordinator -> Signer[*] : Abort
///             }
///         }
///     }
/// }
/// ```
#[proc_macro]
pub fn choreography(input: TokenStream) -> TokenStream {
    match choreography::choreography_impl(input.into()) {
        Ok(output) => output.into(),
        Err(err) => err.to_compile_error().into(),
    }
}

/// Generate effect handler implementations with mock and real variants
///
/// This macro eliminates boilerplate code for effect handler implementations by
/// generating consistent patterns for mock and real handler variants.
///
/// # Example
///
/// ```ignore
/// use external_demo_macros::aura_effect_handlers;
///
/// aura_effect_handlers! {
///     trait_name: RandomEffects,
///     mock: {
///         struct_name: MockRandomHandler,
///         state: {
///             seed: u64,
///         },
///         methods: {
///             random_bytes(len: usize) -> Vec<u8> => {
///                 vec![0; len] // deterministic for testing
///             },
///         },
///     },
///     real: {
///         struct_name: RealRandomHandler, 
///         methods: {
///             random_bytes(len: usize) -> Vec<u8> => {
///                 let mut bytes = vec![0u8; len];
///                 rand::thread_rng().fill_bytes(&mut bytes);
///                 bytes
///             },
///         },
///     },
/// }
/// ```
#[proc_macro]
pub fn aura_effect_handlers(input: TokenStream) -> TokenStream {
    match effect_handlers::aura_effect_handlers_impl(input) {
        Ok(output) => output,
        Err(err) => err.to_compile_error().into(),
    }
}
