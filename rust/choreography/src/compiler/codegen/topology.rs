//! Topology integration code generation.
//!
//! Generates topology-aware protocol handlers that support local testing
//! and distributed deployment configurations.

use crate::ast::{Choreography, LocalType, Role};
use crate::topology::{Location, Topology, TopologyConstraint, TopologyMode};
use proc_macro2::{Ident, TokenStream};
use quote::{format_ident, quote};

use super::generate_choreography_code;

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
    let role_names: Vec<&Ident> = choreography.roles.iter().map(|r| r.name()).collect();
    let role_name_strs: Vec<String> = role_names.iter().map(|r| r.to_string()).collect();

    // Generate handler method
    let handler_method = generate_handler_method();

    // Generate with_topology method
    let with_topology_method = generate_with_topology_method(&role_name_strs);

    // Generate topology constants
    let topology_constants = generate_topology_constants(inline_topologies, &role_name_strs);

    quote! {
        /// Topology integration for the #protocol_name_str protocol
        pub mod topology {
            use super::*;
            use ::rumpsteak_aura_choreography::topology::{
                Location, Topology, TopologyBuilder, TopologyHandler, TopologyMode,
            };
            use ::rumpsteak_aura_choreography::{
                Datacenter, Namespace, Region, RoleName, TopologyEndpoint,
            };

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
        /// * `role` - The role this handler will act as
        ///
        /// # Example
        ///
        /// ```ignore
        /// let handler = MyProtocol::handler(Role::Alice);
        /// ```
        pub fn handler(role: Role) -> TopologyHandler {
            TopologyHandler::local(role.role_name())
        }
    }
}

/// Generate the `with_topology(topo, role)` method
fn generate_with_topology_method(role_names: &[String]) -> TokenStream {
    let role_name_literals: Vec<TokenStream> = role_names
        .iter()
        .map(|role| quote! { RoleName::from_static(#role) })
        .collect();

    quote! {
        /// Create a handler for this protocol with a custom topology.
        ///
        /// This allows specifying where each role is deployed, enabling
        /// distributed execution across multiple processes or machines.
        ///
        /// # Arguments
        ///
        /// * `topology` - The topology configuration
        /// * `role` - The role this handler will act as
        ///
        /// # Example
        ///
        /// ```ignore
        /// let topology = Topology::builder()
        ///     .local_role(RoleName::from_static("Alice"))
        ///     .remote_role(
        ///         RoleName::from_static("Bob"),
        ///         TopologyEndpoint::new("192.168.1.10:8080").unwrap(),
        ///     )
        ///     .build();
        ///
        /// let handler = MyProtocol::with_topology(topology, Role::Alice)?;
        /// ```
        pub fn with_topology(
            topology: Topology,
            role: Role,
        ) -> Result<TopologyHandler, String> {
            let roles = [#(#role_name_literals),*];

            // Validate topology against protocol roles
            let validation = topology.validate(&roles);
            if !validation.is_valid() {
                return Err(format!("Topology validation failed: {:?}", validation));
            }

            Ok(TopologyHandler::new(topology, role.role_name()))
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
                pub fn #handler_fn_name(role: Role) -> Result<TopologyHandler, String> {
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
                let ns_literal = ns.as_str();
                quote! { .mode(TopologyMode::Kubernetes(Namespace::new(#ns_literal).unwrap())) }
            }
            TopologyMode::Consul(dc) => {
                let dc_literal = dc.as_str();
                quote! { .mode(TopologyMode::Consul(Datacenter::new(#dc_literal).unwrap())) }
            }
        };
        builder_calls.push(mode_call);
    }

    // Add role locations
    for (role, location) in &topology.locations {
        let role_literal = role.as_str();
        let location_call = match location {
            Location::Local => quote! { .local_role(RoleName::from_static(#role_literal)) },
            Location::Remote(endpoint) => {
                let endpoint_literal = endpoint.as_str();
                quote! {
                    .remote_role(
                        RoleName::from_static(#role_literal),
                        TopologyEndpoint::new(#endpoint_literal).unwrap()
                    )
                }
            }
            Location::Colocated(peer) => {
                let peer_literal = peer.as_str();
                quote! {
                    .colocated_role(
                        RoleName::from_static(#role_literal),
                        RoleName::from_static(#peer_literal)
                    )
                }
            }
        };
        builder_calls.push(location_call);
    }

    // Add constraints
    for constraint in &topology.constraints {
        let constraint_call = match constraint {
            TopologyConstraint::Colocated(r1, r2) => {
                let r1_literal = r1.as_str();
                let r2_literal = r2.as_str();
                quote! {
                    .colocated(
                        RoleName::from_static(#r1_literal),
                        RoleName::from_static(#r2_literal)
                    )
                }
            }
            TopologyConstraint::Separated(r1, r2) => {
                let r1_literal = r1.as_str();
                let r2_literal = r2.as_str();
                quote! {
                    .separated(
                        RoleName::from_static(#r1_literal),
                        RoleName::from_static(#r2_literal)
                    )
                }
            }
            TopologyConstraint::Pinned(role, loc) => {
                let role_literal = role.as_str();
                let loc_expr = match loc {
                    Location::Local => quote! { Location::Local },
                    Location::Remote(ep) => {
                        let ep_literal = ep.as_str();
                        quote! { Location::Remote(TopologyEndpoint::new(#ep_literal).unwrap()) }
                    }
                    Location::Colocated(p) => {
                        let p_literal = p.as_str();
                        quote! { Location::Colocated(RoleName::from_static(#p_literal)) }
                    }
                };
                quote! { .pinned(RoleName::from_static(#role_literal), #loc_expr) }
            }
            TopologyConstraint::Region(role, region) => {
                let role_literal = role.as_str();
                let region_literal = region.as_str();
                quote! {
                    .region(
                        RoleName::from_static(#role_literal),
                        Region::new(#region_literal).unwrap()
                    )
                }
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
    let runner_code =
        crate::compiler::runner::generate_all_runners(&name, &choreography.roles, local_types);

    quote! {
        #base_code
        #runner_code
        #topology_code
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::Protocol;
    use crate::identifiers::RoleName;

    fn create_test_choreography() -> Choreography {
        use quote::format_ident;

        Choreography {
            name: format_ident!("TestProtocol"),
            namespace: None,
            roles: vec![
                Role::new(format_ident!("Alice")).unwrap(),
                Role::new(format_ident!("Bob")).unwrap(),
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
        // Should construct role names for validation
        assert!(code.contains("RoleName :: from_static"));
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
            .local_role(RoleName::from_static("Alice"))
            .local_role(RoleName::from_static("Bob"))
            .build();

        let prod_topology = Topology::builder()
            .remote_role(
                RoleName::from_static("Alice"),
                crate::identifiers::Endpoint::new("alice.prod:8080").unwrap(),
            )
            .remote_role(
                RoleName::from_static("Bob"),
                crate::identifiers::Endpoint::new("bob.prod:8081").unwrap(),
            )
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
        assert!(code.contains("role_name"));
    }

    #[test]
    fn test_generate_with_topology_method() {
        let tokens = generate_with_topology_method(&["Alice".to_string(), "Bob".to_string()]);
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
            .local_role(RoleName::from_static("Alice"))
            .remote_role(
                RoleName::from_static("Bob"),
                crate::identifiers::Endpoint::new("localhost:8080").unwrap(),
            )
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
            .local_role(RoleName::from_static("Alice"))
            .local_role(RoleName::from_static("Bob"))
            .colocated(
                RoleName::from_static("Alice"),
                RoleName::from_static("Bob"),
            )
            .separated(
                RoleName::from_static("Alice"),
                RoleName::from_static("Carol"),
            )
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
                Role::new(format_ident!("Alice")).unwrap(),
                crate::ast::LocalType::End,
            ),
            (
                Role::new(format_ident!("Bob")).unwrap(),
                crate::ast::LocalType::End,
            ),
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
