//! Dynamic role code generation.
//!
//! Generates runtime support structures for dynamic role management,
//! including role binding validation, device mapping, and symbolic resolution.

use crate::ast::Choreography;
use proc_macro2::{Ident, TokenStream};
use quote::{format_ident, quote};

use super::generate_choreography_code;

/// Generate dynamic role support structures for runtime role management
pub fn generate_dynamic_role_support(choreography: &Choreography) -> TokenStream {
    let dynamic_roles = collect_dynamic_roles(choreography);

    if dynamic_roles.is_empty() {
        return quote! {};
    }

    let choreo_name = &choreography.name;
    let runtime_struct_name = format_ident!("{}Runtime", choreo_name);
    let validation_functions = generate_validation_functions(&dynamic_roles);
    let mapping_functions = generate_mapping_functions(&dynamic_roles);
    let runtime_struct = generate_runtime_struct(
        &runtime_struct_name,
        &validation_functions,
        &mapping_functions,
    );
    let device_id_type = generate_device_id_alias();

    quote! { #runtime_struct #device_id_type }
}

fn collect_dynamic_roles(choreography: &Choreography) -> Vec<&crate::ast::Role> {
    choreography
        .roles
        .iter()
        .filter(|role| role.is_dynamic() || role.is_symbolic())
        .collect()
}

fn generate_validation_functions(dynamic_roles: &[&crate::ast::Role]) -> Vec<TokenStream> {
    dynamic_roles
        .iter()
        .map(|role| {
            let role_name = role.name();
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
        })
        .collect()
}

fn generate_mapping_functions(dynamic_roles: &[&crate::ast::Role]) -> Vec<TokenStream> {
    dynamic_roles
        .iter()
        .map(|role| {
            let role_name = role.name();
            let map_fn_name =
                format_ident!("map_{}_instances", role_name.to_string().to_lowercase());
            let get_fn_name = format_ident!("get_{}_device", role_name.to_string().to_lowercase());

            quote! {
                /// Map role instances to device IDs
                pub fn #map_fn_name(&mut self, instances: Vec<DeviceId>) -> Result<(), String> {
                    let role_name = stringify!(#role_name);

                    if let Some(expected_count) = self.role_counts.get(role_name) {
                        if instances.len() != *expected_count as usize {
                            return Err(format!(
                                "Expected {} instances for role {}, got {}",
                                expected_count, role_name, instances.len()
                            ));
                        }
                    }

                    const MAX_ROLE_INDEX: usize = 1023;
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
        })
        .collect()
}

fn generate_runtime_struct(
    runtime_struct_name: &Ident,
    validation_functions: &[TokenStream],
    mapping_functions: &[TokenStream],
) -> TokenStream {
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
                if let Some(wildcard_pos) = role_expr.find("[*]") {
                    let role_name = &role_expr[..wildcard_pos];
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
    }
}

fn generate_device_id_alias() -> TokenStream {
    quote! { type DeviceId = String; }
}

/// Generate enhanced choreography code with dynamic role support
pub fn generate_choreography_code_with_dynamic_roles(
    choreography: &Choreography,
    local_types: &[(crate::ast::Role, crate::ast::LocalType)],
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
