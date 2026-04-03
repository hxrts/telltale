//! External Demo Macros - Proc Macro Crate
//!
//! This crate provides downstream-specific proc macros that complement the
//! upstream `tell!` choreography macro. Protocol compilation should go through
//! Telltale directly; this crate only owns macros that are genuinely specific
//! to the external demo.

use proc_macro::TokenStream;

mod effect_handlers;

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
