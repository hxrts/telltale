// Code generation from projected local types to Rumpsteak session types

use crate::ast::{Choreography, LocalType, MessageType, Protocol, Role};
use crate::extensions::ProtocolExtension;
use proc_macro2::{Ident, TokenStream};
use quote::{format_ident, quote};
use std::collections::HashMap;

/// Generate documentation comments from annotations
fn generate_annotation_docs(annotations: &HashMap<String, String>) -> TokenStream {
    if annotations.is_empty() {
        return quote! {};
    }

    let doc_lines: Vec<TokenStream> = annotations
        .iter()
        .map(|(key, value)| {
            if value == "true" {
                quote! { #[doc = concat!("@", #key)] }
            } else {
                quote! { #[doc = concat!("@", #key, ": ", #value)] }
            }
        })
        .collect();

    quote! { #(#doc_lines)* }
}

/// Generate metadata structure for annotations
fn generate_annotation_metadata(name: &str, annotations: &HashMap<String, String>) -> TokenStream {
    if annotations.is_empty() {
        return quote! {};
    }

    let metadata_name = format_ident!("{}Annotations", name);
    let annotation_fields: Vec<TokenStream> = annotations
        .keys()
        .map(|key| {
            let field_name = format_ident!("{}", key.to_lowercase());
            quote! {
                pub #field_name: &'static str,
            }
        })
        .collect();

    let annotation_values: Vec<TokenStream> = annotations
        .iter()
        .map(|(key, value)| {
            let field_name = format_ident!("{}", key.to_lowercase());
            quote! {
                #field_name: #value,
            }
        })
        .collect();

    quote! {
        /// Generated annotation metadata
        #[derive(Debug, Clone, Copy)]
        pub struct #metadata_name {
            #(#annotation_fields)*
        }

        impl #metadata_name {
            pub const INSTANCE: Self = Self {
                #(#annotation_values)*
            };
        }
    }
}

/// Generate attributes from specific annotation keys
#[allow(dead_code)]
fn generate_annotation_attributes(annotations: &HashMap<String, String>) -> TokenStream {
    let mut attrs = Vec::new();

    // Handle common annotation patterns
    if let Some(priority) = annotations.get("priority") {
        attrs.push(quote! { #[priority = #priority] });
    }

    if let Some(timeout) = annotations.get("timeout") {
        attrs.push(quote! { #[timeout = #timeout] });
    }

    if annotations.get("async").is_some_and(|v| v == "true") {
        attrs.push(quote! { #[async_trait] });
    }

    if let Some(retry_count) = annotations.get("retry") {
        attrs.push(quote! { #[retry = #retry_count] });
    }

    quote! { #(#attrs)* }
}

/// Generate runtime annotation accessor for a protocol node
fn generate_runtime_annotation_access(name: &str, protocol: &Protocol) -> TokenStream {
    let fn_name = format_ident!("get_{}_annotations", name.to_lowercase());
    let all_annotations = protocol.get_annotations();

    if all_annotations.is_empty() {
        return quote! {};
    }

    let annotation_map: Vec<TokenStream> = all_annotations
        .iter()
        .map(|(key, value)| {
            quote! { map.insert(#key.to_string(), #value.to_string()); }
        })
        .collect();

    quote! {
        /// Get runtime annotations for this protocol node
        pub fn #fn_name() -> std::collections::HashMap<String, String> {
            let mut map = std::collections::HashMap::new();
            #(#annotation_map)*
            map
        }
    }
}

/// Generate Rumpsteak session type definitions from a local type
#[must_use]
pub fn generate_session_type(
    role: &Role,
    local_type: &LocalType,
    protocol_name: &str,
) -> TokenStream {
    let type_name = format_ident!("{}_{}", role.name, protocol_name);
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
            let to_name = &to.name;
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
            let from_name = &from.name;
            let msg_name = &message.name;
            let cont = generate_type_expr(continuation);

            quote! {
                Receive<#from_name, #msg_name, #cont>
            }
        }

        LocalType::Select { to, branches } => {
            let to_name = &to.name;
            let choice_type = generate_choice_enum(branches, true);

            quote! {
                Select<#to_name, #choice_type>
            }
        }

        LocalType::Branch { from, branches } => {
            let from_name = &from.name;
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

/// Generate complete Rumpsteak code from a choreography
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
        pub fn create_extension_registry() -> ::rumpsteak_aura_choreography::extensions::ExtensionRegistry {
            let mut registry = ::rumpsteak_aura_choreography::extensions::ExtensionRegistry::new();

            // In a real implementation, this would register runtime extension handlers
            // For now, we just return the empty registry

            registry
        }
    }
}

/// Generate role struct definitions
fn generate_role_structs(roles: &[Role]) -> TokenStream {
    let _n = roles.len();
    let role_names: Vec<&Ident> = roles.iter().map(|r| &r.name).collect();

    // Generate Roles tuple struct
    let roles_struct = quote! {
        #[derive(Roles)]
        struct Roles(#(#role_names),*);
    };

    // Generate individual role structs with routes
    let role_structs = roles.iter().enumerate().map(|(i, role)| {
        let role_name = &role.name;
        let other_roles: Vec<_> = roles
            .iter()
            .enumerate()
            .filter(|(j, _)| i != *j)
            .map(|(_, r)| &r.name)
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
    let role_name = &role.name;
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

/// Generate complete Rumpsteak code from a choreography with annotation support
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
        .filter(|role| role.index.is_some() || role.param.is_some())
        .map(|role| {
            let mut role_annotations = HashMap::new();
            if role.index.is_some() {
                role_annotations.insert("indexed".to_string(), "true".to_string());
            }
            if role.param.is_some() {
                role_annotations.insert("parameterized".to_string(), "true".to_string());
            }
            generate_annotation_metadata(&role.name.to_string(), &role_annotations)
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

/// Generate dynamic role support structures for runtime role management
pub fn generate_dynamic_role_support(choreography: &Choreography) -> TokenStream {
    let dynamic_roles: Vec<_> = choreography
        .roles
        .iter()
        .filter(|role| role.is_dynamic() || role.is_symbolic())
        .collect();

    if dynamic_roles.is_empty() {
        return quote! {};
    }

    let choreo_name = &choreography.name;
    let runtime_struct_name = format_ident!("{}Runtime", choreo_name);

    // Generate DeviceId type alias (assuming this exists in the runtime)
    let device_id_type = quote! {
        type DeviceId = String; // This should be imported from the runtime system
    };

    // Generate role binding validation functions
    let validation_functions = dynamic_roles.iter().map(|role| {
        let role_name = &role.name;
        let validation_fn_name =
            format_ident!("validate_{}_count", role_name.to_string().to_lowercase());

        quote! {
            /// Validate role count for runtime bounds checking
            pub fn #validation_fn_name(count: u32) -> Result<(), String> {
                const MAX_ROLE_COUNT: u32 = 1024;

                if count > MAX_ROLE_COUNT {
                    return Err(format!("Role count {} exceeds maximum {}", count, MAX_ROLE_COUNT));
                }

                if count == 0 {
                    return Err("Role count cannot be zero".to_string());
                }

                Ok(())
            }
        }
    });

    // Generate role mapping functions
    let mapping_functions = dynamic_roles.iter().map(|role| {
        let role_name = &role.name;
        let map_fn_name = format_ident!("map_{}_instances", role_name.to_string().to_lowercase());
        let get_fn_name = format_ident!("get_{}_device", role_name.to_string().to_lowercase());

        quote! {
            /// Map role instances to device IDs
            pub fn #map_fn_name(&mut self, instances: Vec<DeviceId>) -> Result<(), String> {
                let role_name = stringify!(#role_name);

                // Validate instance count
                if let Some(expected_count) = self.role_counts.get(role_name) {
                    if instances.len() != *expected_count as usize {
                        return Err(format!(
                            "Expected {} instances for role {}, got {}",
                            expected_count, role_name, instances.len()
                        ));
                    }
                }

                const MAX_ROLE_INDEX: usize = 1023;

                // Store mappings with bounds checking
                for (index, device_id) in instances.into_iter().enumerate() {
                    if index > MAX_ROLE_INDEX {
                        return Err(format!("Role index {} exceeds maximum", index));
                    }

                    let key = format!("{}[{}]", role_name, index);
                    self.role_mappings.insert(key, device_id);
                }

                Ok(())
            }

            /// Get device ID for a specific role instance
            pub fn #get_fn_name(&self, index: u32) -> Option<&DeviceId> {
                const MAX_ROLE_INDEX: u32 = 1023;
                if index > MAX_ROLE_INDEX {
                    return None;
                }

                let key = format!("{}[{}]", stringify!(#role_name), index);
                self.role_mappings.get(&key)
            }
        }
    });

    quote! {
        /// Dynamic protocol runtime for managing role bindings and device mappings
        pub struct #runtime_struct_name {
            /// Role count bindings (role_name -> count)
            role_counts: std::collections::HashMap<String, u32>,
            /// Role to device mappings (role[index] -> device_id)
            role_mappings: std::collections::HashMap<String, DeviceId>,
            /// Index bindings for symbolic variables (var_name -> value)
            index_bindings: std::collections::HashMap<String, u32>,
        }

        impl #runtime_struct_name {
            /// Create a new runtime manager
            pub fn new() -> Self {
                Self {
                    role_counts: std::collections::HashMap::new(),
                    role_mappings: std::collections::HashMap::new(),
                    index_bindings: std::collections::HashMap::new(),
                }
            }

            /// Bind a symbolic role parameter to a concrete count
            pub fn bind_role_count(&mut self, role_name: &str, count: u32) -> Result<(), String> {
                const MAX_ROLE_COUNT: u32 = 1024;

                // Validate count bounds
                if count > MAX_ROLE_COUNT {
                    return Err(format!("Role count {} exceeds maximum {}", count, MAX_ROLE_COUNT));
                }

                if count == 0 {
                    return Err("Role count cannot be zero".to_string());
                }

                self.role_counts.insert(role_name.to_string(), count);
                Ok(())
            }

            /// Bind a symbolic index variable to a concrete value
            pub fn bind_index(&mut self, var_name: &str, value: u32) -> Result<(), String> {
                const MAX_ROLE_INDEX: u32 = 1023;

                if value > MAX_ROLE_INDEX {
                    return Err(format!("Index {} exceeds maximum {}", value, MAX_ROLE_INDEX));
                }

                self.index_bindings.insert(var_name.to_string(), value);
                Ok(())
            }

            /// Get the count for a role
            pub fn get_role_count(&self, role_name: &str) -> Option<u32> {
                self.role_counts.get(role_name).copied()
            }

            /// Get the value for an index variable
            pub fn get_index_binding(&self, var_name: &str) -> Option<u32> {
                self.index_bindings.get(var_name).copied()
            }

            /// Resolve a role expression to concrete device IDs
            pub fn resolve_role_targets(&self, role_expr: &str) -> Result<Vec<DeviceId>, String> {
                // Parse role expression like "Worker[*]", "Worker[0..3]", "Worker[i]"
                if let Some(wildcard_pos) = role_expr.find("[*]") {
                    let role_name = &role_expr[..wildcard_pos];

                    // Get all instances of this role
                    if let Some(count) = self.role_counts.get(role_name) {
                        let mut targets = Vec::new();
                        for i in 0..*count {
                            if let Some(device_id) = self.get_device_by_role_and_index(role_name, i) {
                                targets.push(device_id.clone());
                            }
                        }
                        return Ok(targets);
                    }
                }

                // Handle range expressions, concrete indices, symbolic variables, etc.
                // This is a simplified implementation - a full parser would be more robust
                Err(format!("Unsupported role expression: {}", role_expr))
            }

            /// Get device ID by role name and index
            fn get_device_by_role_and_index(&self, role_name: &str, index: u32) -> Option<&DeviceId> {
                let key = format!("{}[{}]", role_name, index);
                self.role_mappings.get(&key)
            }

            #(#validation_functions)*
            #(#mapping_functions)*
        }

        impl Default for #runtime_struct_name {
            fn default() -> Self {
                Self::new()
            }
        }

        #device_id_type
    }
}

/// Generate enhanced choreography code with dynamic role support
pub fn generate_choreography_code_with_dynamic_roles(
    choreography: &Choreography,
    local_types: &[(Role, LocalType)],
) -> TokenStream {
    let name = choreography.name.to_string();
    let base_code = generate_choreography_code(&name, &choreography.roles, local_types);
    let dynamic_support = generate_dynamic_role_support(choreography);

    if dynamic_support.is_empty() {
        base_code
    } else {
        quote! {
            #base_code

            /// Dynamic role management
            pub mod dynamic {
                use super::*;

                #dynamic_support
            }
        }
    }
}

// ============================================================================
// Topology Integration Code Generation
// ============================================================================

use crate::topology::{Location, Topology, TopologyMode};

/// Parsed inline topology definition for code generation
#[derive(Debug, Clone)]
pub struct InlineTopology {
    /// Name of the topology (e.g., "Dev", "Prod")
    pub name: String,
    /// The topology configuration
    pub topology: Topology,
}

/// Generate topology-aware protocol handlers
///
/// This generates:
/// - `Protocol::handler(role)` - Creates a TopologyHandler with local mode
/// - `Protocol::with_topology(topo, role)` - Creates a TopologyHandler with custom topology
/// - Named topology constants for inline definitions
#[must_use]
pub fn generate_topology_integration(
    choreography: &Choreography,
    inline_topologies: &[InlineTopology],
) -> TokenStream {
    let _protocol_name = &choreography.name;

    // Collect role names for validation
    let role_names: Vec<&Ident> = choreography.roles.iter().map(|r| &r.name).collect();
    let role_name_strs: Vec<String> = role_names.iter().map(|r| r.to_string()).collect();

    // Generate handler method
    let handler_method = generate_handler_method();

    // Generate with_topology method
    let with_topology_method = generate_with_topology_method();

    // Generate topology constants
    let topology_constants = generate_topology_constants(inline_topologies, &role_name_strs);

    // Generate role name validation
    let valid_roles_array = quote! {
        const VALID_ROLES: &[&str] = &[#(#role_name_strs),*];
    };

    quote! {
        /// Topology integration for the #protocol_name_str protocol
        pub mod topology {
            use super::*;
            use ::rumpsteak_aura_choreography::topology::{
                Location, Topology, TopologyBuilder, TopologyHandler, TopologyMode,
            };

            #valid_roles_array

            /// Validate that a role name is part of this protocol
            pub fn validate_role(role: &str) -> Result<(), String> {
                if VALID_ROLES.contains(&role) {
                    Ok(())
                } else {
                    Err(format!(
                        "Unknown role '{}' - valid roles are: {:?}",
                        role, VALID_ROLES
                    ))
                }
            }

            #handler_method
            #with_topology_method
            #topology_constants
        }
    }
}

/// Generate the `handler(role)` method that returns a local TopologyHandler
fn generate_handler_method() -> TokenStream {
    quote! {
        /// Create a handler for this protocol with local-mode topology.
        ///
        /// This is suitable for testing and single-process execution where
        /// all roles run in the same process using in-memory channels.
        ///
        /// # Arguments
        ///
        /// * `role` - The role name this handler will act as
        ///
        /// # Example
        ///
        /// ```ignore
        /// let handler = MyProtocol::handler("Alice");
        /// ```
        pub fn handler(role: impl Into<String>) -> Result<TopologyHandler, String> {
            let role_str = role.into();
            validate_role(&role_str)?;
            Ok(TopologyHandler::local(role_str))
        }
    }
}

/// Generate the `with_topology(topo, role)` method
fn generate_with_topology_method() -> TokenStream {
    quote! {
        /// Create a handler for this protocol with a custom topology.
        ///
        /// This allows specifying where each role is deployed, enabling
        /// distributed execution across multiple processes or machines.
        ///
        /// # Arguments
        ///
        /// * `topology` - The topology configuration
        /// * `role` - The role name this handler will act as
        ///
        /// # Example
        ///
        /// ```ignore
        /// let topology = Topology::builder()
        ///     .local_role("Alice")
        ///     .remote_role("Bob", "192.168.1.10:8080")
        ///     .build();
        ///
        /// let handler = MyProtocol::with_topology(topology, "Alice")?;
        /// ```
        pub fn with_topology(
            topology: Topology,
            role: impl Into<String>,
        ) -> Result<TopologyHandler, String> {
            let role_str = role.into();
            validate_role(&role_str)?;

            // Validate topology against protocol roles
            let validation = topology.validate(VALID_ROLES);
            if !validation.is_valid() {
                return Err(format!("Topology validation failed: {:?}", validation));
            }

            Ok(TopologyHandler::new(topology, role_str))
        }
    }
}

/// Generate named topology constants from inline definitions
fn generate_topology_constants(
    inline_topologies: &[InlineTopology],
    role_names: &[String],
) -> TokenStream {
    if inline_topologies.is_empty() {
        return quote! {};
    }

    let constants: Vec<TokenStream> = inline_topologies
        .iter()
        .map(|topo| {
            let _const_name = format_ident!("{}", topo.name.to_uppercase());
            let fn_name = format_ident!("{}", topo.name.to_lowercase());
            let handler_fn_name = format_ident!("{}_handler", topo.name.to_lowercase());

            // Generate the topology builder calls
            let builder_calls = generate_topology_builder(&topo.topology, role_names);

            quote! {
                /// Pre-configured topology: #const_name
                pub fn #fn_name() -> Topology {
                    #builder_calls
                }

                /// Get handler for the #const_name topology
                pub fn #handler_fn_name(role: impl Into<String>) -> Result<TopologyHandler, String> {
                    with_topology(#fn_name(), role)
                }
            }
        })
        .collect();

    quote! {
        /// Pre-configured topologies for this protocol
        pub mod topologies {
            use super::*;

            #(#constants)*
        }
    }
}

/// Generate topology builder code from a Topology
fn generate_topology_builder(topology: &Topology, _role_names: &[String]) -> TokenStream {
    let mut builder_calls = Vec::new();

    // Add mode if specified
    if let Some(ref mode) = topology.mode {
        let mode_call = match mode {
            TopologyMode::Local => quote! { .mode(TopologyMode::Local) },
            TopologyMode::PerRole => quote! { .mode(TopologyMode::PerRole) },
            TopologyMode::Kubernetes(ns) => {
                quote! { .mode(TopologyMode::Kubernetes(#ns.to_string())) }
            }
            TopologyMode::Consul(dc) => {
                quote! { .mode(TopologyMode::Consul(#dc.to_string())) }
            }
        };
        builder_calls.push(mode_call);
    }

    // Add role locations
    for (role, location) in &topology.locations {
        let location_call = match location {
            Location::Local => quote! { .local_role(#role) },
            Location::Remote(endpoint) => quote! { .remote_role(#role, #endpoint) },
            Location::Colocated(peer) => quote! { .colocated_role(#role, #peer) },
        };
        builder_calls.push(location_call);
    }

    // Add constraints
    for constraint in &topology.constraints {
        let constraint_call = match constraint {
            crate::topology::TopologyConstraint::Colocated(r1, r2) => {
                quote! { .colocated(#r1, #r2) }
            }
            crate::topology::TopologyConstraint::Separated(r1, r2) => {
                quote! { .separated(#r1, #r2) }
            }
            crate::topology::TopologyConstraint::Pinned(role, loc) => {
                let loc_expr = match loc {
                    Location::Local => quote! { Location::Local },
                    Location::Remote(ep) => quote! { Location::Remote(#ep.to_string()) },
                    Location::Colocated(p) => quote! { Location::Colocated(#p.to_string()) },
                };
                quote! { .pinned(#role, #loc_expr) }
            }
            crate::topology::TopologyConstraint::Region(role, region) => {
                quote! { .region(#role, #region) }
            }
        };
        builder_calls.push(constraint_call);
    }

    if builder_calls.is_empty() {
        quote! {
            TopologyBuilder::new().build()
        }
    } else {
        quote! {
            TopologyBuilder::new()
                #(#builder_calls)*
                .build()
        }
    }
}

/// Generate complete choreography code with topology integration
#[must_use]
pub fn generate_choreography_code_with_topology(
    choreography: &Choreography,
    local_types: &[(Role, LocalType)],
    inline_topologies: &[InlineTopology],
) -> TokenStream {
    let name = choreography.name.to_string();
    let base_code = generate_choreography_code(&name, &choreography.roles, local_types);
    let topology_code = generate_topology_integration(choreography, inline_topologies);

    // Generate runner code with topology awareness
    let runner_code = super::runner::generate_all_runners(&name, &choreography.roles, local_types);

    quote! {
        #base_code
        #runner_code
        #topology_code
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Choreography, Protocol};

    fn create_test_choreography() -> Choreography {
        use quote::format_ident;

        Choreography {
            name: format_ident!("TestProtocol"),
            namespace: None,
            roles: vec![
                Role::new(format_ident!("Alice")),
                Role::new(format_ident!("Bob")),
            ],
            protocol: Protocol::End,
            attrs: std::collections::HashMap::new(),
        }
    }

    #[test]
    fn test_generate_topology_integration_basic() {
        let choreography = create_test_choreography();
        let inline_topologies = vec![];

        let tokens = generate_topology_integration(&choreography, &inline_topologies);
        let code = tokens.to_string();

        // Should generate the topology module
        assert!(code.contains("pub mod topology"));
        // Should contain role validation
        assert!(code.contains("VALID_ROLES"));
        // Should contain handler function
        assert!(code.contains("pub fn handler"));
        // Should contain with_topology function
        assert!(code.contains("pub fn with_topology"));
    }

    #[test]
    fn test_generate_topology_integration_with_inline_topologies() {
        let choreography = create_test_choreography();

        let dev_topology = Topology::builder()
            .mode(TopologyMode::Local)
            .local_role("Alice")
            .local_role("Bob")
            .build();

        let prod_topology = Topology::builder()
            .remote_role("Alice", "alice.prod:8080")
            .remote_role("Bob", "bob.prod:8081")
            .build();

        let inline_topologies = vec![
            InlineTopology {
                name: "Dev".to_string(),
                topology: dev_topology,
            },
            InlineTopology {
                name: "Prod".to_string(),
                topology: prod_topology,
            },
        ];

        let tokens = generate_topology_integration(&choreography, &inline_topologies);
        let code = tokens.to_string();

        // Should generate topology constants module
        assert!(code.contains("pub mod topologies"));
        // Should generate dev topology function
        assert!(code.contains("pub fn dev"));
        // Should generate prod topology function
        assert!(code.contains("pub fn prod"));
        // Should generate handler functions for each
        assert!(code.contains("dev_handler"));
        assert!(code.contains("prod_handler"));
    }

    #[test]
    fn test_generate_handler_method() {
        let tokens = generate_handler_method();
        let code = tokens.to_string();

        assert!(code.contains("pub fn handler"));
        assert!(code.contains("TopologyHandler :: local"));
        assert!(code.contains("validate_role"));
    }

    #[test]
    fn test_generate_with_topology_method() {
        let tokens = generate_with_topology_method();
        let code = tokens.to_string();

        assert!(code.contains("pub fn with_topology"));
        assert!(code.contains("TopologyHandler :: new"));
        assert!(code.contains("topology . validate"));
    }

    #[test]
    fn test_generate_topology_builder_local_mode() {
        let topology = Topology::builder().mode(TopologyMode::Local).build();

        let tokens =
            generate_topology_builder(&topology, &["Alice".to_string(), "Bob".to_string()]);
        let code = tokens.to_string();

        assert!(code.contains("TopologyMode :: Local"));
    }

    #[test]
    fn test_generate_topology_builder_with_roles() {
        let topology = Topology::builder()
            .local_role("Alice")
            .remote_role("Bob", "localhost:8080")
            .build();

        let tokens =
            generate_topology_builder(&topology, &["Alice".to_string(), "Bob".to_string()]);
        let code = tokens.to_string();

        assert!(code.contains("local_role"));
        assert!(code.contains("remote_role"));
        assert!(code.contains("localhost:8080"));
    }

    #[test]
    fn test_generate_topology_builder_with_constraints() {
        let topology = Topology::builder()
            .local_role("Alice")
            .local_role("Bob")
            .colocated("Alice", "Bob")
            .separated("Alice", "Carol")
            .build();

        let tokens = generate_topology_builder(
            &topology,
            &["Alice".to_string(), "Bob".to_string(), "Carol".to_string()],
        );
        let code = tokens.to_string();

        assert!(code.contains("colocated"));
        assert!(code.contains("separated"));
    }

    #[test]
    fn test_generate_choreography_code_with_topology() {
        let choreography = create_test_choreography();
        let local_types = vec![
            (
                Role::new(format_ident!("Alice")),
                crate::ast::LocalType::End,
            ),
            (Role::new(format_ident!("Bob")), crate::ast::LocalType::End),
        ];
        let inline_topologies = vec![];

        let tokens = generate_choreography_code_with_topology(
            &choreography,
            &local_types,
            &inline_topologies,
        );
        let code = tokens.to_string();

        // Should contain role definitions
        assert!(code.contains("Alice") || code.contains("Roles"));
        // Should contain topology integration
        assert!(code.contains("pub mod topology"));
    }
}
