//! String interning for hot runtime paths.

use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// Stable identifier for interned runtime strings.
pub type StringId = u32;

/// Runtime symbol table used to intern repeated role/label strings.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct SymbolTable {
    symbols: Vec<String>,
    index: HashMap<String, StringId>,
}

impl SymbolTable {
    /// Create an empty symbol table.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Intern a string and return its stable id.
    ///
    /// # Panics
    ///
    /// Panics if the symbol table exceeds `u32::MAX` entries.
    pub fn intern(&mut self, value: &str) -> StringId {
        if let Some(id) = self.index.get(value) {
            return *id;
        }
        let id = u32::try_from(self.symbols.len()).expect("symbol table overflow");
        let owned = value.to_string();
        self.symbols.push(owned.clone());
        self.index.insert(owned, id);
        id
    }

    /// Resolve an id to a string, if present.
    #[must_use]
    #[allow(clippy::as_conversions)]
    pub fn resolve(&self, id: StringId) -> Option<&str> {
        // u32 -> usize is always safe on 32-bit or larger platforms
        self.symbols.get(id as usize).map(String::as_str)
    }

    /// Number of interned symbols.
    #[must_use]
    pub fn len(&self) -> usize {
        self.symbols.len()
    }

    /// Whether the table is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.symbols.is_empty()
    }
}
