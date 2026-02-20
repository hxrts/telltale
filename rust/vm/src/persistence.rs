//! Persistence model aligned with Lean VM typeclasses.

use serde::{Deserialize, Serialize};

use crate::session::SessionId;

/// Persistence-model contract.
pub trait PersistenceModel {
    /// Persistent state representation.
    type PState: Clone;
    /// Delta representation for incremental updates.
    type Delta: Clone;

    /// Apply one delta to state.
    ///
    /// # Errors
    ///
    /// Returns an error if the delta cannot be applied.
    fn apply(state: &mut Self::PState, delta: &Self::Delta) -> Result<(), String>;

    /// Derive a delta between two states.
    ///
    /// # Errors
    ///
    /// Returns an error if derivation fails.
    fn derive(before: &Self::PState, after: &Self::PState) -> Result<Self::Delta, String>;

    /// Open-session lifecycle delta.
    #[must_use]
    fn open_delta(session: SessionId) -> Self::Delta;

    /// Close-session lifecycle delta.
    #[must_use]
    fn close_delta(session: SessionId) -> Self::Delta;

    /// Optional invoke-action delta.
    #[must_use]
    fn invoke_delta(_session: SessionId, _action: &str) -> Option<Self::Delta> {
        None
    }

    /// Lean-name compatibility wrapper.
    #[must_use]
    #[allow(non_snake_case)]
    fn openDelta(session: SessionId) -> Self::Delta {
        Self::open_delta(session)
    }

    /// Lean-name compatibility wrapper.
    #[must_use]
    #[allow(non_snake_case)]
    fn closeDelta(session: SessionId) -> Self::Delta {
        Self::close_delta(session)
    }

    /// Lean-name compatibility wrapper.
    #[must_use]
    #[allow(non_snake_case)]
    fn invokeDelta(session: SessionId, action: &str) -> Option<Self::Delta> {
        Self::invoke_delta(session, action)
    }
}

/// No-op persistence model useful for tests and default VM construction.
#[derive(Debug, Clone, Copy, Default, Serialize, Deserialize)]
pub struct NoopPersistence;

impl PersistenceModel for NoopPersistence {
    type PState = ();
    type Delta = ();

    fn apply(_state: &mut Self::PState, _delta: &Self::Delta) -> Result<(), String> {
        Ok(())
    }

    fn derive(_before: &Self::PState, _after: &Self::PState) -> Result<Self::Delta, String> {
        Ok(())
    }

    fn open_delta(_session: SessionId) -> Self::Delta {}

    fn close_delta(_session: SessionId) -> Self::Delta {}
}
