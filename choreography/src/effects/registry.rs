//! Extension handler registry for type-safe extension dispatch

use crate::effects::extension::{ExtensionEffect, ExtensionError};
use crate::effects::Endpoint;
use async_trait::async_trait;
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
pub type ExtensionHandler<E> = Box<
    dyn for<'a> Fn(&'a mut E, &'a dyn ExtensionEffect) -> BoxFuture<'a, Result<(), ExtensionError>>
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
/// ```ignore
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
pub struct ExtensionRegistry<E: Endpoint> {
    handlers: HashMap<TypeId, ExtensionHandler<E>>,
}

impl<E: Endpoint> ExtensionRegistry<E> {
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
    /// # Panics
    ///
    /// Panics if a handler is already registered for type `Ext`.
    pub fn register<Ext, F>(&mut self, handler: F)
    where
        Ext: ExtensionEffect + 'static,
        F: for<'a> Fn(
                &'a mut E,
                &'a dyn ExtensionEffect,
            ) -> BoxFuture<'a, Result<(), ExtensionError>>
            + Send
            + Sync
            + 'static,
    {
        let type_id = TypeId::of::<Ext>();
        if self.handlers.contains_key(&type_id) {
            panic!(
                "Extension handler already registered for type: {}",
                std::any::type_name::<Ext>()
            );
        }
        self.handlers.insert(type_id, Box::new(handler));
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
        extension: &dyn ExtensionEffect,
    ) -> Result<(), ExtensionError> {
        let type_id = extension.type_id();

        match self.handlers.get(&type_id) {
            Some(handler) => handler(endpoint, extension).await,
            None => Err(ExtensionError::HandlerNotRegistered {
                type_name: extension.type_name(),
            }),
        }
    }

    /// Check if a handler is registered for an extension type
    #[must_use]
    pub fn is_registered<Ext: ExtensionEffect + 'static>(&self) -> bool {
        self.handlers.contains_key(&TypeId::of::<Ext>())
    }

    /// Merge another registry into this one
    ///
    /// # Panics
    ///
    /// Panics if there are overlapping extension types.
    pub fn merge(&mut self, other: ExtensionRegistry<E>) {
        for (type_id, handler) in other.handlers {
            if self.handlers.contains_key(&type_id) {
                panic!("Cannot merge: duplicate extension type");
            }
            self.handlers.insert(type_id, handler);
        }
    }
}

impl<E: Endpoint> Default for ExtensionRegistry<E> {
    fn default() -> Self {
        Self::new()
    }
}

/// Trait for handlers that support extensions
///
/// This trait provides access to the extension registry. Handlers
/// should populate the registry during construction.
#[async_trait]
pub trait ExtensibleHandler {
    /// The endpoint type for this handler
    type Endpoint: Endpoint;

    /// Get the extension registry for this handler
    ///
    /// The interpreter uses this to dispatch extension effects.
    fn extension_registry(&self) -> &ExtensionRegistry<Self::Endpoint>;
}
