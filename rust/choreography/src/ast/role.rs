//! Role definitions for choreographic protocols

use proc_macro2::{Ident, TokenStream};

#[path = "role_ops.rs"]
mod ops;
pub use ops::RoleBoundsChecker;

/// Maximum allowed role count to prevent memory exhaustion
pub const MAX_ROLE_COUNT: u32 = 10_000;

/// Maximum allowed role index to prevent array bounds issues  
pub const MAX_ROLE_INDEX: u32 = MAX_ROLE_COUNT - 1;

/// Maximum allowed range size for role ranges
pub const MAX_RANGE_COUNT: u32 = 1_000;

/// Validation errors for dynamic role operations
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum RoleValidationError {
    #[error("Role count {count} exceeds maximum allowed {max}")]
    CountOverflow { count: u32, max: u32 },

    #[error("Role index {index} exceeds maximum allowed {max}")]
    IndexOverflow { index: u32, max: u32 },

    #[error("Range size {size} exceeds maximum allowed {max}")]
    RangeSizeOverflow { size: u32, max: u32 },

    #[error("Invalid range: start {start} >= end {end}")]
    InvalidRange { start: u32, end: u32 },

    #[error("Runtime role count must be bounded for safety")]
    UnboundedRuntime,

    #[error("Symbolic parameter '{param}' cannot be validated without runtime context")]
    SymbolicValidation { param: String },
}

/// Result type for role validation operations
pub type RoleValidationResult<T> = Result<T, RoleValidationError>;

/// Role parameter expression for dynamic role counts
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum RoleParam {
    /// Static count: `Worker[3]`
    Static(u32),
    /// Symbolic count: `Worker[N]`
    Symbolic(String),
    /// Runtime determined: `Worker[*]`
    Runtime,
}

/// Role index expression for role references
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum RoleIndex {
    /// Concrete index: `Worker[0]`
    Concrete(u32),
    /// Symbolic index: `Worker[i]`
    Symbolic(String),
    /// Wildcard: `Worker[*]` - all instances
    Wildcard,
    /// Range: `Worker[0..3]`
    Range(RoleRange),
}

/// Role range specification for role references
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RoleRange {
    /// Start of range (inclusive)
    pub start: RangeExpr,
    /// End of range (exclusive)
    pub end: RangeExpr,
}

/// Range expression (can be concrete or symbolic)
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum RangeExpr {
    /// Concrete value: 0, 3
    Concrete(u32),
    /// Symbolic value: i, N
    Symbolic(String),
}

/// A role (participant) in the choreography
///
/// Roles represent the different participants in a distributed protocol.
/// They can be simple (e.g., `Client`, `Server`) or parameterized
/// (e.g., `Worker[0]`, `Worker[N]` where the parameter can be a constant or variable).
///
/// # Examples
///
/// ```text
/// use quote::format_ident;
/// use telltale_choreography::{Role, RoleParam};
///
/// // Simple role
/// let client = Role::new(format_ident!("Client")).unwrap();
///
/// // Static parameterized role
/// let worker = Role::with_param(format_ident!("Worker"), RoleParam::Static(3)).unwrap();
///
/// // Dynamic role
/// let dynamic_worker = Role::with_param(format_ident!("Worker"), RoleParam::Runtime).unwrap();
/// ```
#[derive(Debug, Clone)]
pub struct Role {
    /// The name identifier of the role
    name: Ident,
    /// Optional parameter for role count/size
    param: Option<RoleParam>,
    /// Optional index for role references
    index: Option<RoleIndex>,
    /// Array size for code generation (e.g., for `Worker[N]`)
    array_size: Option<TokenStream>,
}

// Manual implementations for PartialEq, Eq, and Hash
impl PartialEq for Role {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
            && self.param == other.param
            && self.index == other.index
            && self
                .array_size
                .as_ref()
                .map(std::string::ToString::to_string)
                == other
                    .array_size
                    .as_ref()
                    .map(std::string::ToString::to_string)
    }
}

impl Eq for Role {}

impl std::hash::Hash for Role {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.name.hash(state);
        self.param.hash(state);
        self.index.hash(state);
        if let Some(size) = &self.array_size {
            size.to_string().hash(state);
        }
    }
}

impl Role {
    fn new_unchecked(
        name: Ident,
        param: Option<RoleParam>,
        index: Option<RoleIndex>,
        array_size: Option<TokenStream>,
    ) -> Self {
        Role {
            name,
            param,
            index,
            array_size,
        }
    }

    /// Create a new simple role with the given name
    pub fn new(name: Ident) -> RoleValidationResult<Self> {
        let role = Self::new_unchecked(name, None, None, None);
        role.validate()?;
        Ok(role)
    }

    /// Create a role with a parameter (e.g., `Worker[3]`, `Worker[N]`, `Worker[*]`)
    pub fn with_param(name: Ident, param: RoleParam) -> RoleValidationResult<Self> {
        let role = Self::new_unchecked(name, Some(param), None, None);
        role.validate()?;
        Ok(role)
    }

    /// Create a role reference with an index (e.g., `Worker[0]`, `Worker[i]`, `Worker[*]`)
    pub fn with_index(name: Ident, index: RoleIndex) -> RoleValidationResult<Self> {
        let role = Self::new_unchecked(name, None, Some(index), None);
        role.validate()?;
        Ok(role)
    }

    /// Create a role reference with both param and index
    pub fn with_param_and_index(
        name: Ident,
        param: RoleParam,
        index: RoleIndex,
    ) -> RoleValidationResult<Self> {
        let role = Self::new_unchecked(name, Some(param), Some(index), None);
        role.validate()?;
        Ok(role)
    }

    /// Create a new indexed role (e.g., Worker with index 0)
    pub fn indexed(name: Ident, index: usize) -> RoleValidationResult<Self> {
        let role_index = RoleIndex::safe_concrete(index as u32)?;
        let role = Self::new_unchecked(name, None, Some(role_index), None);
        role.validate()?;
        Ok(role)
    }

    /// Create a parameterized role with symbolic parameter (e.g., `Worker[N]`)
    pub fn parameterized(name: Ident, param: TokenStream) -> RoleValidationResult<Self> {
        let role = Self::new_unchecked(
            name,
            Some(RoleParam::Symbolic(param.to_string())),
            None,
            Some(param),
        );
        role.validate()?;
        Ok(role)
    }

    /// Create a role array with a concrete size (e.g., `Worker[3]`)
    pub fn array(name: Ident, size: usize) -> RoleValidationResult<Self> {
        let size_token: TokenStream = size.to_string().parse().unwrap();
        let role = Self::new_unchecked(
            name,
            Some(RoleParam::safe_static(size as u32)?),
            None,
            Some(size_token),
        );
        role.validate()?;
        Ok(role)
    }

    /// Get the role name identifier.
    #[must_use]
    pub fn name(&self) -> &Ident {
        &self.name
    }

    /// Get the role parameter if it exists.
    #[must_use]
    pub fn param(&self) -> Option<&RoleParam> {
        self.param.as_ref()
    }

    /// Get the role index if it exists.
    #[must_use]
    pub fn index(&self) -> Option<&RoleIndex> {
        self.index.as_ref()
    }

    /// Get the array size token if it exists.
    #[must_use]
    pub fn array_size(&self) -> Option<&TokenStream> {
        self.array_size.as_ref()
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

    /// Check if this is a role array (declared with size like `Worker[N]`)
    #[must_use]
    pub fn is_array(&self) -> bool {
        self.array_size.is_some() || matches!(self.param, Some(RoleParam::Static(_)))
    }

    /// Check if this role has dynamic parameterization (runtime count)
    #[must_use]
    pub fn is_dynamic(&self) -> bool {
        matches!(self.param, Some(RoleParam::Runtime))
    }

    /// Check if this role has symbolic parameterization
    #[must_use]
    pub fn is_symbolic(&self) -> bool {
        matches!(self.param, Some(RoleParam::Symbolic(_)))
    }

    /// Check if this role reference uses a wildcard index
    #[must_use]
    pub fn is_wildcard(&self) -> bool {
        matches!(self.index, Some(RoleIndex::Wildcard))
    }

    /// Check if this role reference uses a range index
    #[must_use]
    pub fn is_range(&self) -> bool {
        matches!(self.index, Some(RoleIndex::Range(_)))
    }

    /// Get the role parameter if it exists
    #[must_use]
    pub fn get_param(&self) -> Option<&RoleParam> {
        self.param.as_ref()
    }

    /// Get the role index if it exists
    #[must_use]
    pub fn get_index(&self) -> Option<&RoleIndex> {
        self.index.as_ref()
    }

    /// Get the static count for static parameterized roles
    #[must_use]
    pub fn get_static_count(&self) -> Option<u32> {
        match &self.param {
            Some(RoleParam::Static(count)) => Some(*count),
            _ => None,
        }
    }

    /// Get the symbolic name for symbolic parameterized roles
    #[must_use]
    pub fn get_symbolic_name(&self) -> Option<&str> {
        match &self.param {
            Some(RoleParam::Symbolic(name)) => Some(name),
            _ => None,
        }
    }

    /// Check if this role instance matches the given role family
    ///
    /// For parameterized roles, this checks if the base name matches,
    /// ignoring specific indices. For example:
    /// - `Worker[0]` matches `Worker[N]`
    /// - `Worker[i]` matches `Worker[N]`
    /// - `Worker[1]` matches `Worker[3]` (if `Worker[3]` is the array declaration)
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

        // If the family has a param (symbolic like `Worker[N]`), indexed instances match
        if family.param.is_some() && (self.is_indexed() || self.param.is_some()) {
            return true;
        }

        // Otherwise, require exact match
        self == family
    }

    /// Validate this role for security and safety constraints
    pub fn validate(&self) -> RoleValidationResult<()> {
        // Validate role parameter
        if let Some(param) = &self.param {
            param.validate()?;
        }

        // Validate role index
        if let Some(index) = &self.index {
            index.validate()?;
        }

        // Validate consistency between param and index
        if let (Some(param), Some(index)) = (&self.param, &self.index) {
            param.validate_with_index(index)?;
        }

        Ok(())
    }

    /// Create a safe static role with overflow checking
    pub fn safe_static(name: Ident, count: u32) -> RoleValidationResult<Self> {
        if count > MAX_ROLE_COUNT {
            return Err(RoleValidationError::CountOverflow {
                count,
                max: MAX_ROLE_COUNT,
            });
        }

        Role::with_param(name, RoleParam::Static(count))
    }

    /// Create a safe indexed role with overflow checking
    pub fn safe_indexed(name: Ident, index: u32) -> RoleValidationResult<Self> {
        if index > MAX_ROLE_INDEX {
            return Err(RoleValidationError::IndexOverflow {
                index,
                max: MAX_ROLE_INDEX,
            });
        }

        Role::with_index(name, RoleIndex::Concrete(index))
    }

    /// Create a safe range role with overflow checking
    pub fn safe_range(name: Ident, start: u32, end: u32) -> RoleValidationResult<Self> {
        let range = RoleRange {
            start: RangeExpr::Concrete(start),
            end: RangeExpr::Concrete(end),
        };
        range.validate()?;

        Role::with_index(name, RoleIndex::Range(range))
    }
}
