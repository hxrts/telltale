// Choreography struct definition and validation

use super::{Protocol, Role, ValidationError};
use proc_macro2::Ident;
use std::collections::HashMap;

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
                return Err(ValidationError::UnusedRole(role.name.to_string()));
            }
        }

        // Check protocol is well-formed
        self.protocol.validate(&self.roles)?;

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
}
