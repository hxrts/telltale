//! Runner Function Code Generation
//!
//! This module generates `run_{role}` async functions from local type projections.
//! These functions use the `ChoreographicAdapter` trait to execute protocol logic.
//!
//! # Generated Code Structure
//!
//! For a protocol with roles `Client` and `Server`, this generates:
//!
//! ```ignore
//! pub async fn run_client<A: ChoreographicAdapter<Role = Role>>(
//!     adapter: &mut A,
//! ) -> Result<ClientOutput, A::Error> {
//!     // Generated from Client's local type projection
//! }
//!
//! pub async fn run_server<A: ChoreographicAdapter<Role = Role>>(
//!     adapter: &mut A,
//! ) -> Result<ServerOutput, A::Error> {
//!     // Generated from Server's local type projection
//! }
//!
//! pub async fn execute_as<A: ChoreographicAdapter<Role = Role>>(
//!     role: Role,
//!     adapter: &mut A,
//! ) -> Result<ProtocolOutput, A::Error> {
//!     match role {
//!         Role::Client => run_client(adapter).await,
//!         Role::Server => run_server(adapter).await,
//!     }
//! }
//! ```

use crate::ast::{ExecutionHints, LocalType, OperationPath, OperationStep, Role};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use std::collections::BTreeSet;

mod body;

pub(crate) use body::{
    generate_runner_body, generate_runner_body_with_hints, HintCounters, RecursionContext,
};
#[cfg(test)]
pub(crate) use body::generate_role_id;
#[cfg(test)]
pub(crate) use body::generate_range_exprs;

/// Generate a runner function for a single role.
///
/// # Arguments
///
/// * `protocol_name` - Name of the protocol
/// * `role` - The role to generate a runner for
/// * `local_type` - The projected local type for this role
///
/// # Returns
///
/// A TokenStream containing the `run_{role}` function.
#[must_use]
pub fn generate_runner_fn(protocol_name: &str, role: &Role, local_type: &LocalType) -> TokenStream {
    generate_runner_fn_with_hints(protocol_name, role, local_type, None)
}

/// Generate a runner function for a single role with optional execution hints.
///
/// # Arguments
///
/// * `protocol_name` - Name of the protocol
/// * `role` - The role to generate a runner for
/// * `local_type` - The projected local type for this role
/// * `hints` - Optional execution hints for controlling broadcast/collect behavior
///
/// # Returns
///
/// A TokenStream containing the `run_{role}` function.
#[must_use]
pub fn generate_runner_fn_with_hints(
    protocol_name: &str,
    role: &Role,
    local_type: &LocalType,
    hints: Option<&ExecutionHints>,
) -> TokenStream {
    let role_name = role.name();
    let fn_name = format_ident!("run_{}", role_name.to_string().to_lowercase());
    let output_type = format_ident!("{}Output", role_name);
    let protocol_str = protocol_name;
    let role_variant = if role.index().is_some() || role.param().is_some() {
        quote! { Role::#role_name(index) }
    } else {
        quote! { Role::#role_name }
    };

    // Generate the function body from local type
    let body = generate_runner_body_with_hints(
        local_type,
        &mut RecursionContext::new(),
        hints,
        &OperationPath::new(),
        &mut HintCounters::default(),
    );

    // Determine if this role is indexed
    let (fn_signature, ctx_creation) = if role.index().is_some() || role.param().is_some() {
        // Indexed role - add index parameter
        (
            quote! {
                pub async fn #fn_name<A: ChoreographicAdapter<Role = Role>>(
                    adapter: &mut A,
                    index: u32,
                ) -> Result<#output_type, A::Error>
                where
                    A::Error: From<::telltale_choreography::ChoreographyError>
            },
            quote! {
                let _ctx = ProtocolContext::for_role(#protocol_str, #role_variant);
            },
        )
    } else {
        // Static role
        (
            quote! {
                pub async fn #fn_name<A: ChoreographicAdapter<Role = Role>>(
                    adapter: &mut A,
                ) -> Result<#output_type, A::Error>
                where
                    A::Error: From<::telltale_choreography::ChoreographyError>
            },
            quote! {
                let _ctx = ProtocolContext::for_role(#protocol_str, #role_variant);
            },
        )
    };

    quote! {
        #fn_signature {
            #ctx_creation
            let mut output = #output_type::default();

            #body

            Ok(output)
        }
    }
}

/// Generate the `execute_as` dispatch function.
///
/// This function routes execution to the appropriate `run_{role}` function
/// based on a runtime role value.
#[must_use]
pub fn generate_execute_as(
    _protocol_name: &str,
    roles: &[Role],
    _local_types: &[(Role, LocalType)],
) -> TokenStream {
    // Generate match arms
    let match_arms: Vec<TokenStream> = roles
        .iter()
        .map(|role| {
            let name = role.name();
            let fn_name = format_ident!("run_{}", name.to_string().to_lowercase());

            if role.index().is_some() || role.param().is_some() {
                quote! {
                    Role::#name(index) => {
                        #fn_name(adapter, index).await?;
                    }
                }
            } else {
                quote! {
                    Role::#name => {
                        #fn_name(adapter).await?;
                    }
                }
            }
        })
        .collect();

    quote! {
        /// Execute the protocol as a specific role.
        ///
        /// This function dispatches to the appropriate `run_{role}` function
        /// based on the provided role.
        pub async fn execute_as<A: ChoreographicAdapter<Role = Role>>(
            role: Role,
            adapter: &mut A,
        ) -> Result<(), A::Error>
        where
            A::Error: From<::telltale_choreography::ChoreographyError>
        {
            match role {
                #(#match_arms)*
            }

            Ok(())
        }
    }
}

/// Generate output type structs for each role.
#[must_use]
pub fn generate_output_types(roles: &[Role]) -> TokenStream {
    let output_structs: Vec<TokenStream> = roles
        .iter()
        .map(|role| {
            let name = role.name();
            let output_name = format_ident!("{}Output", name);

            quote! {
                /// Output from running the #name role
                #[derive(Debug, Default)]
                pub struct #output_name {
                    // Intentionally empty in V1: runners report success/failure via `Result`.
                }
            }
        })
        .collect();

    quote! {
        #(#output_structs)*
    }
}

/// Generate all runner code for a choreography.
///
/// This includes:
/// - Output types for each role
/// - `run_{role}` functions for each role
/// - `execute_as` dispatch function
/// - Role enum for runtime dispatch
#[must_use]
pub fn generate_all_runners(
    protocol_name: &str,
    roles: &[Role],
    local_types: &[(Role, LocalType)],
) -> TokenStream {
    let mut label_names = BTreeSet::new();
    for (_, local_type) in local_types {
        collect_branch_labels(local_type, &mut label_names);
    }

    let branch_label_enum = generate_branch_label_enum(&label_names);
    let role_enum = generate_runtime_role_enum(roles);
    let output_types = generate_output_types(roles);

    let runner_fns: Vec<TokenStream> = local_types
        .iter()
        .map(|(role, local_type)| generate_runner_fn(protocol_name, role, local_type))
        .collect();

    let execute_as = generate_execute_as(protocol_name, roles, local_types);

    quote! {
        #branch_label_enum
        #role_enum

        /// Generated runner functions for protocol execution
        #[allow(dead_code, unused_imports, unused_variables)]
        pub mod runners {
            use super::*;
            use ::telltale_choreography::{ChoreographicAdapter, LabelId, ProtocolContext};

            #output_types

            #(#runner_fns)*

            #execute_as
        }
    }
}

// RECURSION_SAFE: structural recursion over finite local-type AST depth.
fn collect_branch_labels(local_type: &LocalType, labels: &mut BTreeSet<String>) {
    match local_type {
        LocalType::Select { branches, .. }
        | LocalType::Branch { branches, .. }
        | LocalType::LocalChoice { branches } => {
            for (label, branch) in branches {
                labels.insert(label.to_string());
                collect_branch_labels(branch, labels);
            }
        }
        LocalType::Send { continuation, .. }
        | LocalType::Receive { continuation, .. }
        | LocalType::Loop {
            body: continuation, ..
        }
        | LocalType::Rec {
            body: continuation, ..
        }
        | LocalType::Timeout {
            body: continuation, ..
        } => {
            collect_branch_labels(continuation, labels);
        }
        LocalType::Var(_) | LocalType::End => {}
    }
}

fn generate_branch_label_enum(labels: &BTreeSet<String>) -> TokenStream {
    if labels.is_empty() {
        return quote! {
            #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
            pub enum BranchLabel {}

            impl ::telltale_choreography::LabelId for BranchLabel {
                fn as_str(&self) -> &'static str {
                    match *self {}
                }

                fn from_str(_label: &str) -> Option<Self> {
                    None
                }
            }
        };
    }

    let variants = labels.iter().map(|label| {
        let ident = format_ident!("{}", label);
        quote! { #ident }
    });

    let as_str_arms = labels.iter().map(|label| {
        let ident = format_ident!("{}", label);
        quote! { BranchLabel::#ident => #label }
    });

    let from_str_arms = labels.iter().map(|label| {
        let ident = format_ident!("{}", label);
        quote! { #label => Some(BranchLabel::#ident) }
    });

    quote! {
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
        pub enum BranchLabel {
            #(#variants),*
        }

        impl ::telltale_choreography::LabelId for BranchLabel {
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

fn generate_runtime_role_enum(roles: &[Role]) -> TokenStream {
    let role_variants: Vec<TokenStream> = roles.iter().map(runtime_role_variant).collect();
    let role_name_arms: Vec<TokenStream> = roles.iter().map(runtime_role_name_arm).collect();
    let role_index_arms: Vec<TokenStream> = roles.iter().map(runtime_role_index_arm).collect();

    runtime_role_enum_tokens(&role_variants, &role_name_arms, &role_index_arms)
}

fn is_parameterized_role(role: &Role) -> bool {
    role.index().is_some() || role.param().is_some()
}

fn runtime_role_variant(role: &Role) -> TokenStream {
    let name = role.name();
    if is_parameterized_role(role) {
        quote! { #name(u32) }
    } else {
        quote! { #name }
    }
}

fn runtime_role_name_arm(role: &Role) -> TokenStream {
    let name = role.name();
    let role_str = role.name().to_string();
    if is_parameterized_role(role) {
        quote! { Role::#name(_) => ::telltale_choreography::RoleName::from_static(#role_str) }
    } else {
        quote! { Role::#name => ::telltale_choreography::RoleName::from_static(#role_str) }
    }
}

fn runtime_role_index_arm(role: &Role) -> TokenStream {
    let name = role.name();
    if is_parameterized_role(role) {
        quote! { Role::#name(index) => Some(*index) }
    } else {
        quote! { Role::#name => None }
    }
}

fn runtime_role_enum_tokens(
    role_variants: &[TokenStream],
    role_name_arms: &[TokenStream],
    role_index_arms: &[TokenStream],
) -> TokenStream {
    quote! {
        /// Runtime role identifier for protocol dispatch and adapters.
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
        pub enum Role {
            #(#role_variants),*
        }

        impl ::telltale_choreography::RoleId for Role {
            type Label = BranchLabel;

            fn role_name(&self) -> ::telltale_choreography::RoleName {
                match self {
                    #(#role_name_arms),*
                }
            }

            fn role_index(&self) -> Option<u32> {
                match self {
                    #(#role_index_arms),*
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    include!("../../tests/unit/compiler/runner_tests.rs");
}
