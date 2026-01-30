//! Code generation from projected local types to Telltale session types.
//!
//! This module generates Rust code from choreographies including:
//! - Session type definitions
//! - Role structs and implementations
//! - Extension support
//! - Namespace wrapping
//! - Topology integration

mod annotation;
mod dynamic;
mod topology;

// Internal annotation helpers used within codegen
pub(crate) use annotation::{
    generate_annotation_docs, generate_annotation_metadata, generate_runtime_annotation_access,
};

pub use dynamic::{generate_choreography_code_with_dynamic_roles, generate_dynamic_role_support};
pub use topology::{
    generate_choreography_code_with_topology, generate_topology_integration, InlineTopology,
};

use crate::ast::{Choreography, LocalType, MessageType, Role};
use crate::extensions::ProtocolExtension;
use proc_macro2::{Ident, TokenStream};
use quote::{format_ident, quote};
use std::collections::HashMap;

/// Generate Telltale session type definitions from a local type
#[must_use]
pub fn generate_session_type(
    role: &Role,
    local_type: &LocalType,
    protocol_name: &str,
) -> TokenStream {
    let type_name = format_ident!("{}_{}", role.name(), protocol_name);
    let inner_type = generate_type_expr(local_type);

    quote! {
        #[session]
        type #type_name = #inner_type;
    }
}

/// Generate the type expression for a local type
fn generate_type_expr(local_type: &LocalType) -> TokenStream {
    match local_type {
        LocalType::Send {
            to,
            message,
            continuation,
        } => {
            let to_name = to.name();
            let msg_name = &message.name;
            let cont = generate_type_expr(continuation);

            quote! {
                Send<#to_name, #msg_name, #cont>
            }
        }

        LocalType::Receive {
            from,
            message,
            continuation,
        } => {
            let from_name = from.name();
            let msg_name = &message.name;
            let cont = generate_type_expr(continuation);

            quote! {
                Receive<#from_name, #msg_name, #cont>
            }
        }

        LocalType::Select { to, branches } => {
            let to_name = to.name();
            let choice_type = generate_choice_enum(branches, true);

            quote! {
                Select<#to_name, #choice_type>
            }
        }

        LocalType::Branch { from, branches } => {
            let from_name = from.name();
            let choice_type = generate_choice_enum(branches, false);

            quote! {
                Branch<#from_name, #choice_type>
            }
        }

        LocalType::LocalChoice { branches } => {
            let choice_type = generate_choice_enum(branches, true);

            quote! {
                LocalChoice<#choice_type>
            }
        }

        LocalType::Loop { condition, body } => {
            let body_expr = generate_type_expr(body);

            // Generate Loop type with condition information
            // The condition affects the loop semantics but is typically
            // enforced at runtime rather than in the type system
            match condition {
                Some(crate::ast::Condition::Count(_n)) => {
                    // Fixed iteration count - can be encoded in type comments
                    // The count is enforced at runtime in the effect algebra
                    quote! {
                        Loop<#body_expr>
                    }
                }
                Some(crate::ast::Condition::RoleDecides(_role)) => {
                    // Role-based loop control - runtime behavior
                    quote! {
                        // Loop controlled by role decision
                        Loop<#body_expr>
                    }
                }
                Some(crate::ast::Condition::Custom(_expr)) => {
                    // Custom condition - runtime evaluation
                    quote! {
                        // Loop with custom condition
                        Loop<#body_expr>
                    }
                }
                Some(crate::ast::Condition::Fuel(_n)) => {
                    // Fuel-based bounding - max iterations
                    quote! {
                        // Loop with fuel bounding
                        Loop<#body_expr>
                    }
                }
                Some(crate::ast::Condition::YieldAfter(_n)) => {
                    // Yield after N steps
                    quote! {
                        // Loop with yield-after bounding
                        Loop<#body_expr>
                    }
                }
                Some(crate::ast::Condition::YieldWhen(_condition)) => {
                    // Yield when condition met
                    quote! {
                        // Loop with yield-when bounding
                        Loop<#body_expr>
                    }
                }
                None => {
                    // No condition specified - simple loop
                    quote! {
                        Loop<#body_expr>
                    }
                }
            }
        }

        LocalType::Rec {
            label: _label,
            body,
        } => {
            // Generate a recursive type using the label as the type name
            // This prevents infinite expansion by creating a named recursive type
            let body_expr = generate_type_expr(body);
            quote! {
                // Recursive type
                #body_expr
            }
        }

        LocalType::Var(label) => {
            // Reference to recursive type variable
            // Refers back to the enclosing Rec label
            // Inlined reference for code generation
            quote! { #label }
        }

        LocalType::End => {
            quote! { End }
        }

        LocalType::Timeout { duration: _, body } => {
            // Generate type for the body, ignoring timeout info for now
            generate_type_expr(body)
        }
    }
}

/// Generate a choice enum for Select/Branch
fn generate_choice_enum(branches: &[(Ident, LocalType)], _is_select: bool) -> TokenStream {
    let enum_name = format_ident!(
        "Choice{}",
        branches
            .iter()
            .map(|(l, _)| l.to_string())
            .collect::<String>()
    );

    let variants: Vec<TokenStream> = branches
        .iter()
        .map(|(label, local_type)| {
            let continuation = generate_type_expr(local_type);
            quote! {
                #label(#label, #continuation)
            }
        })
        .collect();

    quote! {
        {
            #[session]
            enum #enum_name {
                #(#variants),*
            }
            #enum_name
        }
    }
}

/// Generate complete Telltale code from a choreography
#[must_use]
pub fn generate_choreography_code(
    name: &str,
    roles: &[Role],
    local_types: &[(Role, LocalType)],
) -> TokenStream {
    let role_struct_defs = generate_role_structs(roles);
    let session_type_defs = local_types
        .iter()
        .map(|(role, local_type)| generate_session_type(role, local_type, name));

    // Generate runner functions and execute_as dispatch
    let runner_code = super::runner::generate_all_runners(name, roles, local_types);

    quote! {
        #role_struct_defs
        #(#session_type_defs)*

        #runner_code
    }
}

/// Generate choreography code with extension support
pub fn generate_choreography_code_with_extensions(
    choreography: &Choreography,
    local_types: &[(Role, LocalType)],
    extensions: &[Box<dyn ProtocolExtension>],
) -> TokenStream {
    // Generate base choreography code
    let base_code = generate_choreography_code(
        &choreography.name.to_string(),
        &choreography.roles,
        local_types,
    );

    // Generate extension-specific code
    let extension_code = generate_extension_code(extensions, choreography);

    // Combine base and extension code
    quote! {
        #base_code
        #extension_code
    }
}

/// Generate code for protocol extensions
fn generate_extension_code(
    extensions: &[Box<dyn ProtocolExtension>],
    choreography: &Choreography,
) -> TokenStream {
    if extensions.is_empty() {
        return quote! {};
    }

    let mut extension_impls = Vec::new();

    for extension in extensions {
        let context = crate::extensions::CodegenContext {
            choreography_name: &choreography.name.to_string(),
            roles: &choreography.roles,
            namespace: choreography.namespace.as_deref(),
        };
        let ext_code = extension.generate_code(&context);
        extension_impls.push(ext_code);
    }

    quote! {
        // Extension implementations
        #(#extension_impls)*

        // Extension registry setup
        pub fn create_extension_registry() -> ::telltale_choreography::extensions::ExtensionRegistry {
            let mut registry = ::telltale_choreography::extensions::ExtensionRegistry::new();

            // In a real implementation, this would register runtime extension handlers
            // For now, we just return the empty registry

            registry
        }
    }
}

/// Generate role struct definitions
fn generate_role_structs(roles: &[Role]) -> TokenStream {
    let _n = roles.len();
    let role_names: Vec<&Ident> = roles.iter().map(|r| r.name()).collect();

    // Generate Roles tuple struct
    let roles_struct = quote! {
        #[derive(Roles)]
        struct Roles(#(#role_names),*);
    };

    // Generate individual role structs with routes
    let role_structs = roles.iter().enumerate().map(|(i, role)| {
        let role_name = role.name();
        let other_roles: Vec<_> = roles
            .iter()
            .enumerate()
            .filter(|(j, _)| i != *j)
            .map(|(_, r)| r.name())
            .collect();

        if other_roles.is_empty() {
            // Single role (unusual but possible)
            quote! {
                #[derive(Role)]
                #[message(Label)]
                struct #role_name;
            }
        } else {
            let routes = other_roles.iter().map(|other| {
                quote! {
                    #[route(#other)] Channel
                }
            });

            quote! {
                #[derive(Role)]
                #[message(Label)]
                struct #role_name(#(#routes),*);
            }
        }
    });

    quote! {
        #roles_struct
        #(#role_structs)*
    }
}

/// Generate implementation functions for each role
#[must_use]
pub fn generate_role_implementations(
    role: &Role,
    local_type: &LocalType,
    protocol_name: &str,
) -> TokenStream {
    let role_name = role.name();
    let fn_name = format_ident!("{}_protocol", role_name.to_string().to_lowercase());
    let session_type = format_ident!("{}_{}", role_name, protocol_name);

    let impl_body = generate_implementation_body(local_type);

    quote! {
        async fn #fn_name(role: &mut #role_name) -> Result<()> {
            try_session(role, |s: #session_type<'_, _>| async move {
                #impl_body
                Ok(((), s))
            }).await
        }
    }
}

/// Generate the implementation body for a local type
fn generate_implementation_body(local_type: &LocalType) -> TokenStream {
    match local_type {
        LocalType::Send {
            message,
            continuation,
            ..
        } => {
            let msg_name = &message.name;
            let cont_impl = generate_implementation_body(continuation);

            quote! {
                let s = s.send(#msg_name(/* ... */)).await?;
                #cont_impl
            }
        }

        LocalType::Receive {
            message,
            continuation,
            ..
        } => {
            let msg_name = &message.name;
            let cont_impl = generate_implementation_body(continuation);

            quote! {
                let (#msg_name(value), s) = s.receive().await?;
                #cont_impl
            }
        }

        LocalType::Select { branches, .. } => {
            // Generate match on user choice
            let first_branch = &branches[0];
            let label = &first_branch.0;
            let cont_impl = generate_implementation_body(&first_branch.1);

            quote! {
                let s = s.select(#label(/* ... */)).await?;
                #cont_impl
            }
        }

        LocalType::Branch { branches, .. } => {
            let match_arms = branches.iter().map(|(label, local_type)| {
                let impl_body = generate_implementation_body(local_type);
                quote! {
                    Choice::#label(value, s) => {
                        #impl_body
                    }
                }
            });

            quote! {
                let s = match s.branch().await? {
                    #(#match_arms)*
                };
            }
        }

        LocalType::End => quote! {},

        _ => quote! { /* recursive types need special handling */ },
    }
}

/// Generate helper functions and types for the choreography
#[must_use]
pub fn generate_helpers(_name: &str, messages: &[MessageType]) -> TokenStream {
    let message_enum = if messages.is_empty() {
        quote! {}
    } else {
        let variants = messages.iter().map(|msg| {
            let name = &msg.name;
            quote! { #name(#name) }
        });

        quote! {
            #[derive(Message)]
            enum Label {
                #(#variants),*
            }
        }
    };

    let message_structs = messages.iter().map(|msg| {
        let name = &msg.name;
        if let Some(payload) = &msg.payload {
            quote! { struct #name #payload; }
        } else {
            quote! { struct #name; }
        }
    });

    quote! {
        #message_enum
        #(#message_structs)*

        type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;
        type Channel = Bidirectional<UnboundedSender<Label>, UnboundedReceiver<Label>>;
    }
}

/// Generate complete code from a choreography, with namespace support and annotations
#[must_use]
pub fn generate_choreography_code_with_namespacing(
    choreo: &Choreography,
    local_types: &[(Role, LocalType)],
) -> TokenStream {
    let inner_code = generate_choreography_code_with_annotations(
        &choreo.name.to_string(),
        &choreo.roles,
        local_types,
        choreo,
    );

    // Generate choreography-level annotation metadata
    let choreo_docs = generate_annotation_docs(choreo.get_attributes());
    let choreo_metadata =
        generate_annotation_metadata(&choreo.name.to_string(), choreo.get_attributes());

    match &choreo.namespace {
        Some(ns) => {
            let ns_ident = format_ident!("{}", ns);
            quote! {
                #choreo_docs
                #[allow(dead_code, unused_imports, unused_variables)]
                pub mod #ns_ident {
                    use super::*;

                    #choreo_metadata
                    #inner_code
                }
            }
        }
        None => {
            quote! {
                #choreo_docs
                #[allow(dead_code, unused_imports, unused_variables)]
                mod __generated_choreography {
                    use super::*;
                    #choreo_metadata
                    #inner_code
                }
                pub use __generated_choreography::*;
            }
        }
    }
}

/// Generate complete Telltale code from a choreography with annotation support
#[must_use]
pub fn generate_choreography_code_with_annotations(
    name: &str,
    roles: &[Role],
    local_types: &[(Role, LocalType)],
    choreo: &Choreography,
) -> TokenStream {
    let role_struct_defs = generate_role_structs(roles);
    let session_type_defs = local_types
        .iter()
        .map(|(role, local_type)| generate_session_type(role, local_type, name));

    // Generate runtime annotation accessors for the protocol
    let protocol_annotation_access = generate_runtime_annotation_access(name, &choreo.protocol);

    // Generate metadata for roles with annotations
    let role_metadata: Vec<TokenStream> = roles
        .iter()
        .filter(|role| role.index().is_some() || role.param().is_some())
        .map(|role| {
            let mut role_annotations = HashMap::new();
            if role.index().is_some() {
                role_annotations.insert("indexed".to_string(), "true".to_string());
            }
            if role.param().is_some() {
                role_annotations.insert("parameterized".to_string(), "true".to_string());
            }
            generate_annotation_metadata(&role.name().to_string(), &role_annotations)
        })
        .collect();

    quote! {
        #role_struct_defs
        #(#session_type_defs)*
        #protocol_annotation_access
        #(#role_metadata)*

        /// Protocol annotation summary
        pub mod annotations {
            use super::*;
            use std::collections::HashMap;

            /// Get all annotations in the protocol
            pub fn get_all_protocol_annotations() -> HashMap<String, HashMap<String, String>> {
                let mut all_annotations = HashMap::new();
                // This would be populated dynamically based on the protocol structure
                all_annotations
            }
        }
    }
}
