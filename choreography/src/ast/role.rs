//! Role definitions for choreographic protocols

use proc_macro2::{Ident, TokenStream};

/// A role (participant) in the choreography
///
/// Roles represent the different participants in a distributed protocol.
/// They can be simple (e.g., `Client`, `Server`) or parameterized
/// (e.g., `Worker[0]`, `Worker[N]` where the parameter can be a constant or variable).
///
/// # Examples
///
/// ```ignore
/// use quote::format_ident;
/// use rumpsteak_aura_choreography::Role;
///
/// // Simple role
/// let client = Role::new(format_ident!("Client"));
///
/// // Parameterized role with concrete index
/// let worker = Role::indexed(format_ident!("Worker"), 0);
/// ```
#[derive(Debug, Clone)]
pub struct Role {
    /// The name identifier of the role
    pub name: Ident,
    /// Optional index for parameterized roles (e.g., Worker with index 0)
    pub index: Option<usize>,
    /// Optional parameter expression for symbolic indices (e.g., Worker[N])
    pub param: Option<TokenStream>,
    /// Size of the role array (for Worker[N], this would be N)
    pub array_size: Option<TokenStream>,
}

// Manual implementations for PartialEq, Eq, and Hash
// TokenStream doesn't implement these traits, so we compare based on string representation
impl PartialEq for Role {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
            && self.index == other.index
            && self.param.as_ref().map(std::string::ToString::to_string)
                == other.param.as_ref().map(std::string::ToString::to_string)
            && self.array_size.as_ref().map(std::string::ToString::to_string)
                == other.array_size.as_ref().map(std::string::ToString::to_string)
    }
}

impl Eq for Role {}

impl std::hash::Hash for Role {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.name.hash(state);
        self.index.hash(state);
        if let Some(param) = &self.param {
            param.to_string().hash(state);
        }
        if let Some(size) = &self.array_size {
            size.to_string().hash(state);
        }
    }
}

impl Role {
    /// Create a new simple role with the given name
    #[must_use] 
    pub fn new(name: Ident) -> Self {
        Role {
            name,
            index: None,
            param: None,
            array_size: None,
        }
    }

    /// Create a new indexed role (e.g., Worker with index 0)
    #[must_use] 
    pub fn indexed(name: Ident, index: usize) -> Self {
        Role {
            name,
            index: Some(index),
            param: None,
            array_size: None,
        }
    }

    /// Create a parameterized role with symbolic parameter (e.g., Worker[N])
    #[must_use] 
    pub fn parameterized(name: Ident, param: TokenStream) -> Self {
        Role {
            name,
            index: None,
            param: Some(param.clone()),
            array_size: Some(param),
        }
    }

    /// Create a role array with a concrete size (e.g., Worker[3])
    #[must_use] 
    pub fn array(name: Ident, size: usize) -> Self {
        let size_token: TokenStream = size.to_string().parse().unwrap();
        Role {
            name,
            index: None,
            param: None,
            array_size: Some(size_token),
        }
    }

    /// Check if this role has an index
    #[must_use] 
    pub fn is_indexed(&self) -> bool {
        self.index.is_some()
    }

    /// Generate a Rust identifier for this role
    #[must_use] 
    pub fn to_ident(&self) -> Ident {
        self.name.clone()
    }

    /// Check if this role is parameterized (has either index or param)
    #[must_use] 
    pub fn is_parameterized(&self) -> bool {
        self.index.is_some() || self.param.is_some()
    }

    /// Check if this is a role array (declared with size like Worker[N])
    #[must_use] 
    pub fn is_array(&self) -> bool {
        self.array_size.is_some()
    }

    /// Check if this role instance matches the given role family
    ///
    /// For parameterized roles, this checks if the base name matches,
    /// ignoring specific indices. For example:
    /// - `Worker[0]` matches `Worker[N]`
    /// - `Worker[i]` matches `Worker[N]`
    /// - `Worker[1]` matches `Worker[3]` (if Worker[3] is the array declaration)
    /// - `Client` only matches `Client` (exact match for non-parameterized)
    #[must_use] 
    pub fn matches_family(&self, family: &Role) -> bool {
        // Names must match
        if self.name != family.name {
            return false;
        }

        // If the family is an array declaration (has array_size), any instance matches
        if family.is_array() {
            // Instance can have concrete index, symbolic param, or neither
            return self.is_indexed() || self.param.is_some() || !self.is_array();
        }

        // If the family has a param (symbolic like Worker[N]), indexed instances match
        if family.param.is_some() && (self.is_indexed() || self.param.is_some()) {
            return true;
        }

        // Otherwise, require exact match
        self == family
    }
}
