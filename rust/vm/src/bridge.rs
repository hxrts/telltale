//! Cross-domain bridge traits for VM domain composition.

use crate::guard::{GuardLayer, LayerId};
use crate::identity::IdentityModel;
use crate::verification::VerificationModel;

/// Bridge from identity participants to guard layers.
pub trait IdentityGuardBridge<I: IdentityModel, G: GuardLayer> {
    /// Resolve guard layer for a participant.
    fn guard_layer_for_participant(&self, participant: &I::ParticipantId) -> LayerId;
}

/// Bridge from effect actions to guard costs/resources.
pub trait EffectGuardBridge<E, G: GuardLayer> {
    /// Cost label for one effect action.
    fn guard_cost_for_effect(&self, action: &E) -> G::Resource;
}

/// Bridge from effect actions to persistence deltas.
pub trait PersistenceEffectBridge<P, E> {
    /// Persistence delta derived from effect action.
    fn persistence_delta_for_effect(&self, action: &E) -> P;
}

/// Bridge from identity participants to persistence keys.
pub trait IdentityPersistenceBridge<I: IdentityModel, K> {
    /// Persistence key for participant.
    fn persistence_key_for_participant(&self, participant: &I::ParticipantId) -> K;
}

/// Bridge from identity participants to verification keys.
pub trait IdentityVerificationBridge<I: IdentityModel, V: VerificationModel> {
    /// Verification key for participant.
    fn verification_key_for_participant(&self, participant: &I::ParticipantId) -> V::VerifyingKey;
}
