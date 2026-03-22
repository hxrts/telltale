// Choreography struct definition and validation

use super::{ChoiceGuard, Protocol, Role, ValidationError};
use proc_macro2::Ident;
use serde::{Deserialize, Serialize};
use std::collections::{BTreeSet, HashMap};

const ATTR_PROOF_BUNDLES: &str = "dsl.proof_bundles";
const ATTR_REQUIRED_PROOF_BUNDLES: &str = "dsl.required_proof_bundles";
const ATTR_INFERRED_REQUIRED_PROOF_BUNDLES: &str = "dsl.inferred_required_proof_bundles";
const ATTR_ROLE_SETS: &str = "dsl.role_sets";
const ATTR_TOPOLOGIES: &str = "dsl.topologies";
const ATTR_TYPE_DECLS: &str = "dsl.type_decls";
const ATTR_EFFECT_DECLS: &str = "dsl.effect_decls";
const ATTR_PROTOCOL_USES: &str = "dsl.protocol_uses";

/// Typed proof-bundle declaration metadata from DSL.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProofBundleDecl {
    /// Stable bundle name.
    pub name: String,
    /// Capabilities provided by this bundle.
    #[serde(default)]
    pub capabilities: Vec<String>,
    /// Optional bundle version.
    #[serde(default)]
    pub version: Option<String>,
    /// Optional bundle issuer.
    #[serde(default)]
    pub issuer: Option<String>,
    /// Optional constraints attached to the bundle.
    #[serde(default)]
    pub constraints: Vec<String>,
}

/// Typed role-set declaration metadata from DSL.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RoleSetDecl {
    /// Stable role-set name.
    pub name: String,
    /// Explicit members for this role-set.
    #[serde(default)]
    pub members: Vec<String>,
    /// Optional subset selector source role-set or family.
    #[serde(default)]
    pub subset_of: Option<String>,
    /// Optional subset selector start index (inclusive).
    #[serde(default)]
    pub subset_start: Option<u32>,
    /// Optional subset selector end index (exclusive).
    #[serde(default)]
    pub subset_end: Option<u32>,
}

/// Typed topology declaration metadata from DSL.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TopologyDecl {
    /// Topology kind (`cluster`, `ring`, `mesh`).
    pub kind: String,
    /// Topology name.
    pub name: String,
    /// Referenced members.
    #[serde(default)]
    pub members: Vec<String>,
}

/// DSL type declaration metadata.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TypeDecl {
    /// Declared type name.
    pub name: String,
    /// Whether this is a `type alias`.
    pub is_alias: bool,
    /// Right-hand side for aliases.
    #[serde(default)]
    pub alias_of: Option<String>,
    /// Union constructors for nominal sum types.
    #[serde(default)]
    pub constructors: Vec<TypeConstructorDecl>,
}

/// Constructor declaration for one nominal union type.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TypeConstructorDecl {
    /// Constructor name.
    pub name: String,
    /// Optional payload type rendered from source syntax.
    #[serde(default)]
    pub payload_type: Option<String>,
}

/// Nominal effect interface declaration metadata.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct EffectDecl {
    /// Effect interface name.
    pub name: String,
    /// Declared operations for this interface.
    #[serde(default)]
    pub operations: Vec<EffectOpDecl>,
}

/// Authority class for one nominal effect operation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, Default)]
#[serde(rename_all = "snake_case")]
pub enum EffectOpAuthorityClass {
    /// Operation may produce authoritative semantic evidence.
    Authoritative,
    /// Operation performs command work without itself proving semantic truth.
    #[default]
    Command,
    /// Operation is observational only and must not be consumed via `check`.
    Observe,
}

/// One operation in a nominal effect interface.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct EffectOpDecl {
    /// Operation name.
    pub name: String,
    /// Authority class attached to this operation.
    #[serde(default)]
    pub authority_class: EffectOpAuthorityClass,
    /// Input type as declared in DSL surface syntax.
    pub input_type: String,
    /// Output type as declared in DSL surface syntax.
    pub output_type: String,
}

/// Runtime-facing effect metadata derived from one nominal effect declaration.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RuntimeEffectMetadataDecl {
    /// Nominal effect interface name.
    pub interface_name: String,
    /// Nominal effect operation name.
    pub operation_name: String,
    /// Authority class attached to this operation.
    pub authority_class: EffectOpAuthorityClass,
    /// Runtime admissibility policy name.
    pub admissibility: String,
    /// Runtime totality policy name.
    pub totality: String,
    /// Runtime timeout policy name.
    pub timeout_policy: String,
    /// Runtime reentrancy policy name.
    pub reentrancy_policy: String,
    /// Runtime handler-domain name.
    pub handler_domain: String,
}

/// A complete choreographic protocol specification
#[derive(Debug)]
pub struct Choreography {
    /// Protocol name
    pub name: Ident,
    /// Optional namespace for the protocol
    pub namespace: Option<String>,
    /// Participating roles
    pub roles: Vec<Role>,
    /// The protocol specification
    pub protocol: Protocol,
    /// Metadata and attributes
    pub attrs: HashMap<String, String>,
}

impl Choreography {
    /// Get the qualified name of the choreography (namespace::name or just name)
    #[must_use]
    pub fn qualified_name(&self) -> String {
        match &self.namespace {
            Some(ns) => format!("{}::{}", ns, self.name),
            None => self.name.to_string(),
        }
    }

    /// Validate the choreography for correctness
    ///
    /// # Errors
    ///
    /// Returns [`ValidationError`] if the choreography is invalid (unused roles,
    /// malformed protocol, duplicate/missing proof bundles, or missing capabilities).
    pub fn validate(&self) -> Result<(), ValidationError> {
        // Check all roles are used
        for role in &self.roles {
            if !self.protocol.mentions_role(role) {
                return Err(ValidationError::UnusedRole(role.name().to_string()));
            }
        }

        // Check protocol is well-formed
        self.protocol.validate(&self.roles)?;
        self.validate_proof_bundles()?;
        self.validate_effect_surface()?;

        Ok(())
    }

    fn validate_proof_bundles(&self) -> Result<(), ValidationError> {
        let bundles = self.proof_bundles();
        let mut declared: BTreeSet<String> = BTreeSet::new();
        for bundle in &bundles {
            if !declared.insert(bundle.name.clone()) {
                return Err(ValidationError::DuplicateProofBundle(bundle.name.clone()));
            }
        }

        for required in self.required_proof_bundles() {
            if !declared.contains(&required) {
                return Err(ValidationError::MissingProofBundle(required));
            }
        }

        let required_caps = self.required_bundle_capabilities();
        for capability in self.required_vm_core_capabilities() {
            if !required_caps.contains(&capability) {
                return Err(ValidationError::MissingCapability(capability));
            }
        }

        Ok(())
    }

    fn validate_effect_surface(&self) -> Result<(), ValidationError> {
        let mut effect_names = BTreeSet::new();
        let mut effect_ops: HashMap<String, HashMap<String, EffectOpDecl>> = HashMap::new();
        for effect in self.effect_decls() {
            if !effect_names.insert(effect.name.clone()) {
                return Err(ValidationError::ExtensionError(format!(
                    "duplicate effect interface declaration `{}`",
                    effect.name
                )));
            }
            let mut ops = HashMap::new();
            for op in effect.operations {
                if ops.insert(op.name.clone(), op.clone()).is_some() {
                    return Err(ValidationError::ExtensionError(format!(
                        "duplicate effect operation `{}.{}`",
                        effect.name, op.name
                    )));
                }
            }
            effect_ops.insert(effect.name, ops);
        }

        let declared = effect_names;
        let used: BTreeSet<String> = self.protocol_uses().into_iter().collect();
        for effect in &used {
            if !declared.contains(effect) {
                return Err(ValidationError::ExtensionError(format!(
                    "protocol uses undeclared effect interface `{effect}`"
                )));
            }
        }

        fn validate_expr(
            expr: &super::AuthorityExpr,
            effect_ops: &HashMap<String, HashMap<String, EffectOpDecl>>,
            used: &BTreeSet<String>,
        ) -> Result<(), ValidationError> {
            match expr {
                super::AuthorityExpr::Check {
                    effect, operation, ..
                } => {
                    if !used.contains(effect) {
                        return Err(ValidationError::ExtensionError(format!(
                            "effect invocation `{effect}.{operation}` is not allowed without `uses {effect}`"
                        )));
                    }
                    let Some(ops) = effect_ops.get(effect) else {
                        return Err(ValidationError::ExtensionError(format!(
                            "effect invocation references undeclared interface `{effect}`"
                        )));
                    };
                    let Some(op_decl) = ops.get(operation) else {
                        return Err(ValidationError::ExtensionError(format!(
                            "effect invocation references undeclared operation `{effect}.{operation}`"
                        )));
                    };
                    if matches!(op_decl.authority_class, EffectOpAuthorityClass::Observe) {
                        return Err(ValidationError::ExtensionError(format!(
                            "effect invocation `{effect}.{operation}` is observational and may not be invoked with `check`"
                        )));
                    }
                    Ok(())
                }
                super::AuthorityExpr::Observe {
                    effect, operation, ..
                } => {
                    if !used.contains(effect) {
                        return Err(ValidationError::ExtensionError(format!(
                            "effect invocation `{effect}.{operation}` is not allowed without `uses {effect}`"
                        )));
                    }
                    let Some(ops) = effect_ops.get(effect) else {
                        return Err(ValidationError::ExtensionError(format!(
                            "effect invocation references undeclared interface `{effect}`"
                        )));
                    };
                    let Some(op_decl) = ops.get(operation) else {
                        return Err(ValidationError::ExtensionError(format!(
                            "effect invocation references undeclared operation `{effect}.{operation}`"
                        )));
                    };
                    if !matches!(op_decl.authority_class, EffectOpAuthorityClass::Observe) {
                        return Err(ValidationError::ExtensionError(format!(
                            "effect invocation `{effect}.{operation}` is not observational and may not be invoked with `observe`"
                        )));
                    }
                    Ok(())
                }
                super::AuthorityExpr::Var(_)
                | super::AuthorityExpr::Transfer { .. }
                | super::AuthorityExpr::Constructor { .. }
                | super::AuthorityExpr::Call { .. } => Ok(()),
            }
        }

        fn validate_protocol_effects(
            protocol: &Protocol,
            effect_ops: &HashMap<String, HashMap<String, EffectOpDecl>>,
            used: &BTreeSet<String>,
        ) -> Result<(), ValidationError> {
            match protocol {
                Protocol::Send { continuation, .. }
                | Protocol::Broadcast { continuation, .. }
                | Protocol::Extension { continuation, .. }
                | Protocol::Let { continuation, .. } => {
                    if let Protocol::Let { expr, .. } = protocol {
                        validate_expr(expr, effect_ops, used)?;
                    }
                    validate_protocol_effects(continuation, effect_ops, used)
                }
                Protocol::Choice { branches, .. } => {
                    for branch in branches {
                        if let Some(ChoiceGuard::Evidence {
                            effect, operation, ..
                        }) = &branch.guard
                        {
                            if !used.contains(effect) {
                                return Err(ValidationError::ExtensionError(format!(
                                    "effect guard `{effect}.{operation}` is not allowed without `uses {effect}`"
                                )));
                            }
                            let Some(ops) = effect_ops.get(effect) else {
                                return Err(ValidationError::ExtensionError(format!(
                                    "effect guard references undeclared interface `{effect}`"
                                )));
                            };
                            let Some(op_decl) = ops.get(operation) else {
                                return Err(ValidationError::ExtensionError(format!(
                                    "effect guard references undeclared operation `{effect}.{operation}`"
                                )));
                            };
                            if matches!(op_decl.authority_class, EffectOpAuthorityClass::Observe) {
                                return Err(ValidationError::ExtensionError(format!(
                                    "effect guard `{effect}.{operation}` is observational and may not be invoked with `check`"
                                )));
                            }
                        }
                        validate_protocol_effects(&branch.protocol, effect_ops, used)?;
                    }
                    Ok(())
                }
                Protocol::Case { expr, branches } => {
                    validate_expr(expr, effect_ops, used)?;
                    for branch in branches {
                        validate_protocol_effects(&branch.protocol, effect_ops, used)?;
                    }
                    Ok(())
                }
                Protocol::Timeout {
                    body,
                    on_timeout,
                    on_cancel,
                    ..
                } => {
                    validate_protocol_effects(body, effect_ops, used)?;
                    validate_protocol_effects(on_timeout, effect_ops, used)?;
                    if let Some(on_cancel) = on_cancel.as_deref() {
                        validate_protocol_effects(on_cancel, effect_ops, used)?;
                    }
                    Ok(())
                }
                Protocol::Loop { body, .. } | Protocol::Rec { body, .. } => {
                    validate_protocol_effects(body, effect_ops, used)
                }
                Protocol::Parallel { protocols } => {
                    for protocol in protocols {
                        validate_protocol_effects(protocol, effect_ops, used)?;
                    }
                    Ok(())
                }
                Protocol::Var(_) | Protocol::End => Ok(()),
            }
        }

        validate_protocol_effects(&self.protocol, &effect_ops, &used)
    }

    /// Get choreography-level attributes/annotations
    #[must_use]
    pub fn get_attributes(&self) -> &HashMap<String, String> {
        &self.attrs
    }

    /// Get mutable reference to choreography-level attributes
    pub fn get_attributes_mut(&mut self) -> &mut HashMap<String, String> {
        &mut self.attrs
    }

    /// Get a specific choreography attribute
    #[must_use]
    pub fn get_attribute(&self, key: &str) -> Option<&String> {
        self.attrs.get(key)
    }

    /// Set a choreography attribute
    pub fn set_attribute(&mut self, key: String, value: String) {
        self.attrs.insert(key, value);
    }

    /// Remove a choreography attribute
    pub fn remove_attribute(&mut self, key: &str) -> Option<String> {
        self.attrs.remove(key)
    }

    /// Check if choreography has a specific attribute
    #[must_use]
    pub fn has_attribute(&self, key: &str) -> bool {
        self.attrs.contains_key(key)
    }

    /// Get attribute as a specific type
    pub fn get_attribute_as<T>(&self, key: &str) -> Option<T>
    where
        T: std::str::FromStr,
    {
        self.get_attribute(key)?.parse().ok()
    }

    /// Get attribute as boolean
    pub fn get_attribute_as_bool(&self, key: &str) -> Option<bool> {
        let value = self.get_attribute(key)?;
        match value.to_lowercase().as_str() {
            "true" | "1" | "yes" | "on" => Some(true),
            "false" | "0" | "no" | "off" => Some(false),
            _ => None,
        }
    }

    /// Clear all choreography attributes
    pub fn clear_attributes(&mut self) {
        self.attrs.clear();
    }

    /// Count of choreography attributes
    pub fn attribute_count(&self) -> usize {
        self.attrs.len()
    }

    /// Get all attribute keys
    pub fn attribute_keys(&self) -> Vec<&String> {
        self.attrs.keys().collect()
    }

    /// Validate that required attributes are present
    pub fn validate_required_attributes(&self, required_keys: &[&str]) -> Result<(), Vec<String>> {
        let missing: Vec<String> = required_keys
            .iter()
            .filter(|&key| !self.has_attribute(key))
            .map(|&key| key.to_string())
            .collect();

        if missing.is_empty() {
            Ok(())
        } else {
            Err(missing)
        }
    }

    /// Find all protocol nodes with a specific annotation
    pub fn find_nodes_with_annotation(&self, key: &str) -> Vec<&Protocol> {
        let mut nodes = Vec::new();
        self.protocol.collect_nodes_with_annotation(key, &mut nodes);
        nodes
    }

    /// Find all protocol nodes with a specific annotation value
    pub fn find_nodes_with_annotation_value(&self, key: &str, value: &str) -> Vec<&Protocol> {
        let mut nodes = Vec::new();
        self.protocol
            .collect_nodes_with_annotation_value(key, value, &mut nodes);
        nodes
    }

    /// Count total annotations across the entire choreography
    pub fn total_annotation_count(&self) -> usize {
        self.attribute_count() + self.protocol.deep_annotation_count()
    }

    /// Set proof-bundle declarations for this choreography.
    pub fn set_proof_bundles(&mut self, bundles: &[ProofBundleDecl]) -> Result<(), String> {
        let encoded =
            serde_json::to_string(bundles).map_err(|e| format!("encode proof bundles: {e}"))?;
        self.attrs.insert(ATTR_PROOF_BUNDLES.to_string(), encoded);
        Ok(())
    }

    /// Get typed proof-bundle declarations.
    #[must_use]
    pub fn proof_bundles(&self) -> Vec<ProofBundleDecl> {
        self.attrs
            .get(ATTR_PROOF_BUNDLES)
            .and_then(|s| serde_json::from_str::<Vec<ProofBundleDecl>>(s).ok())
            .unwrap_or_default()
    }

    /// Set protocol-required proof bundles.
    pub fn set_required_proof_bundles(&mut self, required: &[String]) -> Result<(), String> {
        let encoded =
            serde_json::to_string(required).map_err(|e| format!("encode required bundles: {e}"))?;
        self.attrs
            .insert(ATTR_REQUIRED_PROOF_BUNDLES.to_string(), encoded);
        Ok(())
    }

    /// Get protocol-required proof bundles.
    #[must_use]
    pub fn required_proof_bundles(&self) -> Vec<String> {
        self.attrs
            .get(ATTR_REQUIRED_PROOF_BUNDLES)
            .and_then(|s| serde_json::from_str::<Vec<String>>(s).ok())
            .unwrap_or_default()
    }

    /// Set inferred protocol-required proof bundles.
    pub fn set_inferred_required_proof_bundles(
        &mut self,
        required: &[String],
    ) -> Result<(), String> {
        let encoded =
            serde_json::to_string(required).map_err(|e| format!("encode inferred bundles: {e}"))?;
        self.attrs
            .insert(ATTR_INFERRED_REQUIRED_PROOF_BUNDLES.to_string(), encoded);
        Ok(())
    }

    /// Get inferred protocol-required proof bundles.
    #[must_use]
    pub fn inferred_required_proof_bundles(&self) -> Vec<String> {
        self.attrs
            .get(ATTR_INFERRED_REQUIRED_PROOF_BUNDLES)
            .and_then(|s| serde_json::from_str::<Vec<String>>(s).ok())
            .unwrap_or_default()
    }

    /// Set role-set declarations for this choreography.
    pub fn set_role_sets(&mut self, role_sets: &[RoleSetDecl]) -> Result<(), String> {
        let encoded =
            serde_json::to_string(role_sets).map_err(|e| format!("encode role sets: {e}"))?;
        self.attrs.insert(ATTR_ROLE_SETS.to_string(), encoded);
        Ok(())
    }

    /// Get typed role-set declarations.
    #[must_use]
    pub fn role_sets(&self) -> Vec<RoleSetDecl> {
        self.attrs
            .get(ATTR_ROLE_SETS)
            .and_then(|s| serde_json::from_str::<Vec<RoleSetDecl>>(s).ok())
            .unwrap_or_default()
    }

    /// Set topology declarations for this choreography.
    pub fn set_topologies(&mut self, topologies: &[TopologyDecl]) -> Result<(), String> {
        let encoded =
            serde_json::to_string(topologies).map_err(|e| format!("encode topologies: {e}"))?;
        self.attrs.insert(ATTR_TOPOLOGIES.to_string(), encoded);
        Ok(())
    }

    /// Get typed topology declarations.
    #[must_use]
    pub fn topologies(&self) -> Vec<TopologyDecl> {
        self.attrs
            .get(ATTR_TOPOLOGIES)
            .and_then(|s| serde_json::from_str::<Vec<TopologyDecl>>(s).ok())
            .unwrap_or_default()
    }

    /// Set nominal type declarations for this choreography.
    pub fn set_type_decls(&mut self, decls: &[TypeDecl]) -> Result<(), String> {
        let encoded =
            serde_json::to_string(decls).map_err(|e| format!("encode type declarations: {e}"))?;
        self.attrs.insert(ATTR_TYPE_DECLS.to_string(), encoded);
        Ok(())
    }

    /// Get nominal type declarations.
    #[must_use]
    pub fn type_decls(&self) -> Vec<TypeDecl> {
        self.attrs
            .get(ATTR_TYPE_DECLS)
            .and_then(|s| serde_json::from_str::<Vec<TypeDecl>>(s).ok())
            .unwrap_or_default()
    }

    /// Set nominal effect interface declarations for this choreography.
    pub fn set_effect_decls(&mut self, decls: &[EffectDecl]) -> Result<(), String> {
        let encoded =
            serde_json::to_string(decls).map_err(|e| format!("encode effect declarations: {e}"))?;
        self.attrs.insert(ATTR_EFFECT_DECLS.to_string(), encoded);
        Ok(())
    }

    /// Get nominal effect interface declarations.
    #[must_use]
    pub fn effect_decls(&self) -> Vec<EffectDecl> {
        self.attrs
            .get(ATTR_EFFECT_DECLS)
            .and_then(|s| serde_json::from_str::<Vec<EffectDecl>>(s).ok())
            .unwrap_or_default()
    }

    /// Derive runtime-facing effect metadata from nominal effect declarations
    /// and protocol `uses` dependencies.
    #[must_use]
    pub fn runtime_effect_metadata(&self) -> Vec<RuntimeEffectMetadataDecl> {
        let used: BTreeSet<String> = self.protocol_uses().into_iter().collect();
        self.effect_decls()
            .into_iter()
            .flat_map(|effect| {
                let is_used = used.contains(effect.name.as_str());
                effect.operations.into_iter().map(move |op| {
                    let (
                        admissibility,
                        totality,
                        timeout_policy,
                        reentrancy_policy,
                        handler_domain,
                    ) = match op.authority_class {
                        EffectOpAuthorityClass::Authoritative => (
                            if is_used {
                                "declared_use_only"
                            } else {
                                "internal_only"
                            },
                            "may_block",
                            "inherit_operation_budget",
                            "reject_same_fragment",
                            if is_used { "external" } else { "internal" },
                        ),
                        EffectOpAuthorityClass::Command => (
                            if is_used {
                                "declared_use_only"
                            } else {
                                "internal_only"
                            },
                            "immediate",
                            "none",
                            "allow",
                            if is_used { "external" } else { "internal" },
                        ),
                        EffectOpAuthorityClass::Observe => (
                            if is_used {
                                "declared_use_only"
                            } else {
                                "internal_only"
                            },
                            "immediate",
                            "none",
                            "allow",
                            if is_used { "external" } else { "internal" },
                        ),
                    };
                    RuntimeEffectMetadataDecl {
                        interface_name: effect.name.clone(),
                        operation_name: op.name,
                        authority_class: op.authority_class,
                        admissibility: admissibility.to_string(),
                        totality: totality.to_string(),
                        timeout_policy: timeout_policy.to_string(),
                        reentrancy_policy: reentrancy_policy.to_string(),
                        handler_domain: handler_domain.to_string(),
                    }
                })
            })
            .collect()
    }

    /// Set explicit protocol effect dependencies.
    pub fn set_protocol_uses(&mut self, uses: &[String]) -> Result<(), String> {
        let encoded =
            serde_json::to_string(uses).map_err(|e| format!("encode protocol uses: {e}"))?;
        self.attrs.insert(ATTR_PROTOCOL_USES.to_string(), encoded);
        Ok(())
    }

    /// Get explicit protocol effect dependencies.
    #[must_use]
    pub fn protocol_uses(&self) -> Vec<String> {
        self.attrs
            .get(ATTR_PROTOCOL_USES)
            .and_then(|s| serde_json::from_str::<Vec<String>>(s).ok())
            .unwrap_or_default()
    }

    fn required_bundle_capabilities(&self) -> BTreeSet<String> {
        let required = self.required_proof_bundles();
        let required_set: BTreeSet<&str> = required.iter().map(String::as_str).collect();
        self.proof_bundles()
            .into_iter()
            .filter(|bundle| required_set.contains(bundle.name.as_str()))
            .flat_map(|bundle| bundle.capabilities.into_iter())
            .collect()
    }

    fn required_vm_core_capabilities(&self) -> BTreeSet<String> {
        fn collect(protocol: &Protocol, out: &mut BTreeSet<String>) {
            if let Some(cap) = protocol.get_annotation("required_capability") {
                out.insert(cap);
            }
            match protocol {
                Protocol::Send { continuation, .. }
                | Protocol::Broadcast { continuation, .. }
                | Protocol::Extension { continuation, .. } => collect(continuation, out),
                Protocol::Choice { branches, .. } => {
                    for branch in branches {
                        collect(&branch.protocol, out);
                    }
                }
                Protocol::Loop { body, .. } | Protocol::Rec { body, .. } => collect(body, out),
                Protocol::Let { continuation, .. } => collect(continuation, out),
                Protocol::Case { branches, .. } => {
                    for branch in branches {
                        collect(&branch.protocol, out);
                    }
                }
                Protocol::Timeout {
                    body,
                    on_timeout,
                    on_cancel,
                    ..
                } => {
                    collect(body, out);
                    collect(on_timeout, out);
                    if let Some(on_cancel) = on_cancel.as_deref() {
                        collect(on_cancel, out);
                    }
                }
                Protocol::Parallel { protocols } => {
                    for p in protocols {
                        collect(p, out);
                    }
                }
                Protocol::Var(_) | Protocol::End => {}
            }
        }

        let mut out = BTreeSet::new();
        collect(&self.protocol, &mut out);
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use quote::format_ident;

    #[test]
    fn proof_bundle_metadata_roundtrip() {
        let mut choreo = Choreography {
            name: format_ident!("RoundTrip"),
            namespace: None,
            roles: Vec::new(),
            protocol: Protocol::End,
            attrs: HashMap::new(),
        };
        let bundles = vec![
            ProofBundleDecl {
                name: "Base".to_string(),
                capabilities: vec!["delegation".to_string()],
                version: None,
                issuer: None,
                constraints: Vec::new(),
            },
            ProofBundleDecl {
                name: "Guard".to_string(),
                capabilities: vec!["guard_tokens".to_string()],
                version: None,
                issuer: None,
                constraints: Vec::new(),
            },
        ];
        let required = vec!["Base".to_string()];

        choreo
            .set_proof_bundles(&bundles)
            .expect("set proof bundles");
        choreo
            .set_required_proof_bundles(&required)
            .expect("set required bundles");

        assert_eq!(choreo.proof_bundles(), bundles);
        assert_eq!(choreo.required_proof_bundles(), required);
    }
}
