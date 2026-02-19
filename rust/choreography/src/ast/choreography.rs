// Choreography struct definition and validation

use super::{Protocol, Role, ValidationError};
use proc_macro2::Ident;
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};

const ATTR_PROOF_BUNDLES: &str = "dsl.proof_bundles";
const ATTR_REQUIRED_PROOF_BUNDLES: &str = "dsl.required_proof_bundles";

/// Typed proof-bundle declaration metadata from DSL.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProofBundleDecl {
    /// Stable bundle name.
    pub name: String,
    /// Capabilities provided by this bundle.
    #[serde(default)]
    pub capabilities: Vec<String>,
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
    pub fn qualified_name(&self) -> String {
        match &self.namespace {
            Some(ns) => format!("{}::{}", ns, self.name),
            None => self.name.to_string(),
        }
    }

    /// Validate the choreography for correctness
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

        Ok(())
    }

    fn validate_proof_bundles(&self) -> Result<(), ValidationError> {
        let bundles = self.proof_bundles();
        let mut declared: HashSet<String> = HashSet::new();
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

    /// Get choreography-level attributes/annotations
    pub fn get_attributes(&self) -> &HashMap<String, String> {
        &self.attrs
    }

    /// Get mutable reference to choreography-level attributes
    pub fn get_attributes_mut(&mut self) -> &mut HashMap<String, String> {
        &mut self.attrs
    }

    /// Get a specific choreography attribute
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
        self.attrs
            .insert(ATTR_PROOF_BUNDLES.to_string(), encoded);
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

    fn required_bundle_capabilities(&self) -> HashSet<String> {
        let required = self.required_proof_bundles();
        let required_set: HashSet<&str> = required.iter().map(String::as_str).collect();
        self.proof_bundles()
            .into_iter()
            .filter(|bundle| required_set.contains(bundle.name.as_str()))
            .flat_map(|bundle| bundle.capabilities.into_iter())
            .collect()
    }

    fn required_vm_core_capabilities(&self) -> HashSet<String> {
        fn collect(protocol: &Protocol, out: &mut HashSet<String>) {
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
                Protocol::Parallel { protocols } => {
                    for p in protocols {
                        collect(p, out);
                    }
                }
                Protocol::Var(_) | Protocol::End => {}
            }
        }

        let mut out = HashSet::new();
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
            },
            ProofBundleDecl {
                name: "Guard".to_string(),
                capabilities: vec!["guard_tokens".to_string()],
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
