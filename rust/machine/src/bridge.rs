//! Cross-domain bridge traits for ProtocolMachine domain composition.
//!
//! These bridge traits are intentionally narrow translation layers. They should
//! be implemented as pure metadata lookups or deterministic projections, not as
//! places that mutate session-local ProtocolMachine state or perform async work. Host-side
//! mutation belongs behind the explicit ownership/ingress contract instead.

use crate::guard::{GuardLayer, LayerId};
use crate::identity::IdentityModel;
use crate::verification::VerificationModel;

/// Bridge from identity participants to guard layers.
pub trait IdentityGuardBridge<I: IdentityModel, G: GuardLayer> {
    /// Resolve guard layer for a participant without mutating runtime state.
    fn guard_layer_for_participant(&self, participant: &I::ParticipantId) -> LayerId;
}

/// Bridge from effect actions to guard costs/resources.
pub trait EffectGuardBridge<E, G: GuardLayer> {
    /// Cost label for one effect action without side effects.
    fn guard_cost_for_effect(&self, action: &E) -> G::Resource;
}

/// Bridge from effect actions to persistence deltas.
pub trait PersistenceEffectBridge<P, E> {
    /// Persistence delta derived from effect action without applying it.
    fn persistence_delta_for_effect(&self, action: &E) -> P;
}

/// Bridge from identity participants to persistence keys.
pub trait IdentityPersistenceBridge<I: IdentityModel, K> {
    /// Persistence key for participant without mutating storage.
    fn persistence_key_for_participant(&self, participant: &I::ParticipantId) -> K;
}

/// Bridge from identity participants to verification keys.
pub trait IdentityVerificationBridge<I: IdentityModel, V: VerificationModel> {
    /// Verification key for participant without mutating verification state.
    fn verification_key_for_participant(&self, participant: &I::ParticipantId) -> V::VerifyingKey;
}
