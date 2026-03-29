//! Machine-checkable handler contract ledger for the algebraic-effects boundary.
//!
//! This module is the contract document for `ChoreoHandler` and runtime extension
//! dispatch. It separates:
//!
//! - protocol semantics that every conforming handler must preserve
//! - transport policy choices that handlers are still free to choose
//!
//! The contract is intentionally narrow. It does not try to prove arbitrary
//! handlers correct. Instead, it gives every important runtime handler a
//! structured profile that tests and CI can validate mechanically.

use thiserror::Error;

/// Broad classification of what kind of behavioral surface a handler exposes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HandlerContractTier {
    /// A handler that can execute the full typed protocol surface.
    FullProtocol,
    /// A harness that is intentionally observational or partial.
    ObservationalHarness,
}

/// Delivery substrate chosen by a handler implementation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DeliveryModel {
    InMemoryChannels,
    ScriptedHarness,
    SessionBoundary,
    NoTransport,
}

/// How retries are introduced.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RetryPolicy {
    None,
    ExternalMiddleware,
}

/// How timeouts are enforced.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TimeoutPolicy {
    EnforcingRoleOnly,
    PassThrough,
}

/// Extension dispatch support model.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExtensionDispatchMode {
    Unsupported,
    RegisteredOnlyTypeExact,
}

/// Semantic obligations of a `ChoreoHandler`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProtocolSemanticContract {
    pub typed_send_recv_roundtrip: bool,
    pub exact_choice_label_preservation: bool,
    pub fail_closed_transport_errors: bool,
    pub timeouts_scoped_to_enforcing_role: bool,
    pub deterministic_for_regression: bool,
    pub can_materialize_values: bool,
}

/// Transport-policy choices a handler is allowed to vary.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TransportPolicyContract {
    pub delivery_model: DeliveryModel,
    pub retry_policy: RetryPolicy,
    pub timeout_policy: TimeoutPolicy,
}

/// Contract for runtime extension dispatch.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExtensionDispatchContract {
    pub mode: ExtensionDispatchMode,
    pub fail_closed_when_unregistered: bool,
    pub type_exact_before_side_effects: bool,
}

/// Complete machine-checkable profile for a handler family.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HandlerContractProfile {
    pub handler_name: &'static str,
    pub tier: HandlerContractTier,
    pub semantics: ProtocolSemanticContract,
    pub transport: TransportPolicyContract,
    pub extension_dispatch: ExtensionDispatchContract,
    pub notes: Vec<&'static str>,
}

/// Contract profile must be internally consistent before tests can trust it.
#[derive(Debug, Error, PartialEq, Eq)]
pub enum HandlerContractViolation {
    #[error("full-protocol handlers must preserve typed send/recv round trips")]
    MissingTypedRoundtrip,
    #[error("full-protocol handlers must preserve exact choice labels")]
    MissingChoicePreservation,
    #[error("full-protocol handlers must fail closed on transport/dispatch errors")]
    MissingFailClosedErrors,
    #[error("full-protocol handlers must be able to materialize values")]
    MissingValueMaterialization,
    #[error("timeout policy says enforcing-role only, but semantics do not")]
    TimeoutPolicyMismatch,
    #[error("observational harnesses must be deterministic for regression use")]
    NonDeterministicHarness,
    #[error("registered extension dispatch must fail closed when unregistered")]
    NonFailClosedExtensionDispatch,
    #[error("registered extension dispatch must validate type before side effects")]
    NonExactExtensionDispatch,
}

/// Trait implemented by handlers that document their runtime contract.
pub trait DocumentedHandlerContract {
    fn contract_profile() -> HandlerContractProfile
    where
        Self: Sized;
}

/// Validate that a documented profile is self-consistent.
pub fn validate_handler_contract_profile(
    profile: &HandlerContractProfile,
) -> Result<(), HandlerContractViolation> {
    if profile.transport.timeout_policy == TimeoutPolicy::EnforcingRoleOnly
        && !profile.semantics.timeouts_scoped_to_enforcing_role
    {
        return Err(HandlerContractViolation::TimeoutPolicyMismatch);
    }

    match profile.tier {
        HandlerContractTier::FullProtocol => {
            if !profile.semantics.typed_send_recv_roundtrip {
                return Err(HandlerContractViolation::MissingTypedRoundtrip);
            }
            if !profile.semantics.exact_choice_label_preservation {
                return Err(HandlerContractViolation::MissingChoicePreservation);
            }
            if !profile.semantics.fail_closed_transport_errors {
                return Err(HandlerContractViolation::MissingFailClosedErrors);
            }
            if !profile.semantics.can_materialize_values {
                return Err(HandlerContractViolation::MissingValueMaterialization);
            }
        }
        HandlerContractTier::ObservationalHarness => {
            if !profile.semantics.deterministic_for_regression {
                return Err(HandlerContractViolation::NonDeterministicHarness);
            }
        }
    }

    if profile.extension_dispatch.mode == ExtensionDispatchMode::RegisteredOnlyTypeExact {
        if !profile.extension_dispatch.fail_closed_when_unregistered {
            return Err(HandlerContractViolation::NonFailClosedExtensionDispatch);
        }
        if !profile.extension_dispatch.type_exact_before_side_effects {
            return Err(HandlerContractViolation::NonExactExtensionDispatch);
        }
    }

    Ok(())
}

/// Convenience helper for compile-time discoverable handler profile checks.
pub fn validated_contract_profile<H>() -> Result<HandlerContractProfile, HandlerContractViolation>
where
    H: DocumentedHandlerContract,
{
    let profile = H::contract_profile();
    validate_handler_contract_profile(&profile)?;
    Ok(profile)
}
