//! Extension handler registry for type-safe extension dispatch

use crate::effects::extension::{ExtensionEffect, ExtensionError};
use crate::effects::{Endpoint, RoleId};
use std::any::TypeId;
use std::collections::HashMap;
use std::future::Future;
use std::pin::Pin;

/// Boxed future for async extension handlers
pub type BoxFuture<'a, T> = Pin<Box<dyn Future<Output = T> + Send + 'a>>;

/// Handler function type for extensions
///
/// Extension handlers receive:
/// - `&mut Endpoint`: Mutable endpoint for state/communication
/// - `&dyn ExtensionEffect`: The extension to handle (must downcast)
///
/// Handlers return `Result<(), ExtensionError>` and must handle
/// their extension type or return an error.
pub type ExtensionHandler<E, R> = Box<
    dyn for<'a> Fn(&'a mut E, &'a dyn ExtensionEffect<R>)
            -> BoxFuture<'a, Result<(), ExtensionError>>
        + Send
        + Sync,
>;

/// Registry of extension handlers for a choreography handler
///
/// Handlers must register extension types they support. Unregistered
/// extensions cause runtime errors (fail-fast behavior).
///
/// # Example
///
/// ```text
/// let mut registry = ExtensionRegistry::new();
/// registry.register::<ValidateCapability, _>(|ep, ext| {
///     Box::pin(async move {
///         let validate = ext.as_any()
///             .downcast_ref::<ValidateCapability>()
///             .ok_or_else(|| ExtensionError::TypeMismatch {
///                 expected: "ValidateCapability",
///                 actual: ext.type_name(),
///             })?;
///
///         // Validate capability logic here
///         ep.check_capability(&validate.capability)?;
///         Ok(())
///     })
/// });
/// ```
pub struct ExtensionRegistry<E: Endpoint, R: RoleId> {
    handlers: HashMap<TypeId, (ExtensionHandler<E, R>, &'static str)>,
}

impl<E: Endpoint, R: RoleId> ExtensionRegistry<E, R> {
    /// Create a new empty extension registry
    #[must_use]
    pub fn new() -> Self {
        Self {
            handlers: HashMap::new(),
        }
    }

    /// Register a handler for a specific extension type
    ///
    /// # Type Safety
    ///
    /// The handler receives `&dyn ExtensionEffect` and must downcast to `Ext`.
    /// The registry ensures the handler is only called for `Ext` instances.
    ///
    /// # Errors
    ///
    /// Returns `ExtensionError::DuplicateHandler` if a handler is already registered for type `Ext`.
    pub fn register<Ext, F>(&mut self, handler: F) -> Result<(), ExtensionError>
    where
        Ext: ExtensionEffect<R> + 'static,
        F: for<'a> Fn(
                &'a mut E,
                &'a dyn ExtensionEffect<R>,
            ) -> BoxFuture<'a, Result<(), ExtensionError>>
            + Send
            + Sync
            + 'static,
    {
        let type_id = TypeId::of::<Ext>();
        let type_name = std::any::type_name::<Ext>();
        if self.handlers.contains_key(&type_id) {
            return Err(ExtensionError::DuplicateHandler { type_name });
        }
        self.handlers
            .insert(type_id, (Box::new(handler), type_name));
        Ok(())
    }

    /// Handle an extension effect
    ///
    /// # Errors
    ///
    /// Returns `ExtensionError::HandlerNotRegistered` if no handler exists
    /// for the extension's type. This enforces fail-fast behavior for
    /// unknown extensions.
    pub async fn handle(
        &self,
        endpoint: &mut E,
        extension: &dyn ExtensionEffect<R>,
    ) -> Result<(), ExtensionError> {
        let type_id = extension.type_id();

        match self.handlers.get(&type_id) {
            Some((handler, _type_name)) => handler(endpoint, extension).await,
            None => Err(ExtensionError::HandlerNotRegistered {
                type_name: extension.type_name(),
            }),
        }
    }

    /// Check if a handler is registered for an extension type
    #[must_use]
    pub fn is_registered<Ext: ExtensionEffect<R> + 'static>(&self) -> bool {
        self.handlers.contains_key(&TypeId::of::<Ext>())
    }

    /// Merge another registry into this one
    ///
    /// # Errors
    ///
    /// Returns `ExtensionError::MergeConflict` if there are overlapping extension types.
    pub fn merge(&mut self, other: ExtensionRegistry<E, R>) -> Result<(), ExtensionError> {
        for (type_id, (handler, type_name)) in other.handlers {
            if self.handlers.contains_key(&type_id) {
                return Err(ExtensionError::MergeConflict { type_name });
            }
            self.handlers.insert(type_id, (handler, type_name));
        }
        Ok(())
    }
}

impl<E: Endpoint, R: RoleId> Default for ExtensionRegistry<E, R> {
    fn default() -> Self {
        Self::new()
    }
}

/// Trait for handlers that support extensions
///
/// This trait provides access to the extension registry. Handlers
/// should populate the registry during construction.
pub trait ExtensibleHandler: crate::effects::ChoreoHandler {
    /// Get the extension registry for this handler
    ///
    /// The interpreter uses this to dispatch extension effects.
    fn extension_registry(&self) -> &ExtensionRegistry<Self::Endpoint, Self::Role>;
}
