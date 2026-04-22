//! Machine-checkable transport contract ledger for the topology/transport boundary.
//!
//! This mirrors the handler-contract surface for first-party transports. It
//! separates:
//!
//! - semantic obligations required for the verified runtime guarantees
//! - operational choices that transports may vary while still preserving those
//!   obligations
//!
//! Third-party transports can still implement [`Transport`] without
//! participating in this ledger, but they remain outside the first-party
//! verified claim unless they separately satisfy and document the same
//! contract.

use thiserror::Error;

use super::TransportType;

/// Broad classification of what kind of transport surface is being documented.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TransportContractTier {
    /// A first-party transport used by shipped runtime paths.
    FirstPartyRuntime,
    /// A deterministic harness transport intended for testing/regression.
    ObservationalHarness,
}

/// How a transport becomes ready for message exchange.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TransportStartupMode {
    /// Ready immediately after construction.
    ReadyOnCreate,
    /// Starts itself in the background before first use.
    BackgroundWarmup,
    /// Requires an explicit `start()` call by the embedding code.
    ExplicitStart,
}

/// Semantic obligations of a first-party transport.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TransportSemanticContract {
    pub role_addressed_routing: bool,
    pub authenticated_peers: bool,
    pub per_peer_fifo_delivery: bool,
    pub fail_closed_unknown_role: bool,
    pub no_message_synthesis: bool,
    pub explicit_readiness_errors: bool,
    pub deterministic_for_regression: bool,
}

/// Operational choices that may vary while preserving the semantic contract.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TransportOperationalContract {
    pub transport_type: TransportType,
    pub startup_mode: TransportStartupMode,
    pub environment_resolved: bool,
}

/// Complete machine-checkable profile for a transport family.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TransportContractProfile {
    pub transport_name: &'static str,
    pub tier: TransportContractTier,
    pub semantics: TransportSemanticContract,
    pub operational: TransportOperationalContract,
    pub notes: Vec<&'static str>,
}

/// Profile consistency errors.
#[derive(Debug, Error, PartialEq, Eq)]
pub enum TransportContractViolation {
    #[error("first-party transports must route by role")]
    MissingRoleRouting,
    #[error("first-party transports must preserve per-peer FIFO delivery")]
    MissingPerPeerFifo,
    #[error("network transports must document whether peers are authenticated")]
    MissingPeerAuthenticationDisclosure,
    #[error("first-party transports must fail closed for unknown roles")]
    MissingFailClosedUnknownRole,
    #[error("first-party transports must not synthesize messages")]
    MessageSynthesisAllowed,
    #[error("background or explicit-start transports must expose readiness failures")]
    MissingReadinessErrors,
    #[error("observational harness transports must be deterministic for regression use")]
    NonDeterministicHarness,
}

/// Trait implemented by first-party transports that document their contract.
pub trait DocumentedTransportContract {
    fn contract_profile() -> TransportContractProfile
    where
        Self: Sized;
}

/// Validate that a transport profile is internally consistent.
pub fn validate_transport_contract_profile(
    profile: &TransportContractProfile,
) -> Result<(), TransportContractViolation> {
    match profile.tier {
        TransportContractTier::FirstPartyRuntime => {
            if !profile.semantics.role_addressed_routing {
                return Err(TransportContractViolation::MissingRoleRouting);
            }
            if !profile.semantics.per_peer_fifo_delivery {
                return Err(TransportContractViolation::MissingPerPeerFifo);
            }
            if !profile.semantics.fail_closed_unknown_role {
                return Err(TransportContractViolation::MissingFailClosedUnknownRole);
            }
            if !profile.semantics.no_message_synthesis {
                return Err(TransportContractViolation::MessageSynthesisAllowed);
            }
            if matches!(profile.operational.transport_type, TransportType::Tcp)
                && !profile
                    .notes
                    .iter()
                    .any(|note| note.contains("authenticated") || note.contains("trusted-network"))
            {
                return Err(TransportContractViolation::MissingPeerAuthenticationDisclosure);
            }
        }
        TransportContractTier::ObservationalHarness => {
            if !profile.semantics.deterministic_for_regression {
                return Err(TransportContractViolation::NonDeterministicHarness);
            }
        }
    }

    if matches!(
        profile.operational.startup_mode,
        TransportStartupMode::BackgroundWarmup | TransportStartupMode::ExplicitStart
    ) && !profile.semantics.explicit_readiness_errors
    {
        return Err(TransportContractViolation::MissingReadinessErrors);
    }

    Ok(())
}

/// Convenience helper for compile-time discoverable transport profile checks.
pub fn validated_transport_contract_profile<T>(
) -> Result<TransportContractProfile, TransportContractViolation>
where
    T: DocumentedTransportContract,
{
    let profile = T::contract_profile();
    validate_transport_contract_profile(&profile)?;
    Ok(profile)
}
