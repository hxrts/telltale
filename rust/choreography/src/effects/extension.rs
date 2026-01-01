//! Type-safe extension system for choreographic effects
//!
//! Extensions enable domain-specific effects (capabilities, budgets, logging, error handling)
//! while maintaining full type safety and algebraic effects composition.

use std::any::{Any, TypeId};
use std::fmt::Debug;

use crate::effects::RoleId;

/// Trait for type-safe extension effects
///
/// Extension effects are domain-specific effects that extend the core
/// choreography effect system. Each extension defines its own data type
/// and semantics while participating in the full effect lifecycle.
///
/// # Type Safety
///
/// Extensions are identified by `TypeId`, ensuring compile-time type safety
/// and preventing string-based errors. The type `Self` is the extension's
/// payload and must be clonable for effect algebra operations.
///
/// # Projection Semantics
///
/// Extensions must specify which roles participate via `participating_roles()`.
/// Only those roles will see the extension in their projected local types.
/// Extensions that return an empty vec are included in all role projections.
///
/// # Example
///
/// ```text
/// #[derive(Clone, Debug)]
/// pub struct ValidateCapability {
///     pub capability: String,
///     pub role: Role,
/// }
///
/// impl ExtensionEffect for ValidateCapability {
///     fn type_id(&self) -> TypeId {
///         TypeId::of::<Self>()
///     }
///
///     fn type_name(&self) -> &'static str {
///         "ValidateCapability"
///     }
///
///     fn participating_roles<R: RoleId>(&self) -> Vec<R> {
///         vec![self.role]
///     }
///
///     fn as_any(&self) -> &dyn Any {
///         self
///     }
///
///     fn as_any_mut(&mut self) -> &mut dyn Any {
///         self
///     }
///
///     fn clone_box(&self) -> Box<dyn ExtensionEffect> {
///         Box::new(self.clone())
///     }
/// }
/// ```
pub trait ExtensionEffect<R: RoleId>: Send + Sync + Debug {
    /// Get the TypeId of this extension type
    ///
    /// This is used for type-safe downcasting and extension discrimination.
    /// Typically implemented as `TypeId::of::<Self>()`.
    fn type_id(&self) -> TypeId;

    /// Get a human-readable name for this extension type
    ///
    /// Used in error messages and debugging. Should be the type name.
    fn type_name(&self) -> &'static str;

    /// Get the roles that participate in this extension effect
    ///
    /// # Projection Semantics
    ///
    /// Returns a vector of roles participating in the effect.
    ///
    /// - Empty vec: Extension appears in all role projections (global effect)
    /// - Non-empty: Extension appears only in specified role projections
    fn participating_roles(&self) -> Vec<R> {
        vec![] // Default: global extensions
    }

    /// Downcast to `&dyn Any` for type-safe casting
    fn as_any(&self) -> &dyn Any;

    /// Downcast to `&mut dyn Any` for type-safe mutable casting
    fn as_any_mut(&mut self) -> &mut dyn Any;

    /// Clone this extension into a boxed trait object
    ///
    /// Required for cloning `Effect` enum which contains `Box<dyn ExtensionEffect>`.
    fn clone_box(&self) -> Box<dyn ExtensionEffect<R>>;
}

/// Extension-specific errors
#[derive(Debug, Clone, thiserror::Error)]
pub enum ExtensionError {
    #[error("Unknown extension type: {type_name} (TypeId: {type_id:?})")]
    UnknownExtension {
        type_name: &'static str,
        type_id: TypeId,
    },

    #[error("Extension handler not registered for {type_name}")]
    HandlerNotRegistered { type_name: &'static str },

    #[error("Extension {type_name} failed: {error}")]
    ExecutionFailed {
        type_name: &'static str,
        error: String,
    },

    #[error("Type mismatch: expected {expected}, got {actual}")]
    TypeMismatch {
        expected: &'static str,
        actual: &'static str,
    },

    #[error("Handler already registered for extension type: {type_name}")]
    DuplicateHandler { type_name: &'static str },

    #[error("Cannot merge registries: duplicate handler for {type_name}")]
    MergeConflict { type_name: &'static str },
}
