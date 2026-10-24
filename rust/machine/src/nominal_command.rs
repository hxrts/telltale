//! Nominal command descriptors and the original coroutine continuation.
//!
//! Descriptors and replies are serializable observations. The continuation is
//! not: only an actually resident coroutine may retain the issued occurrence.

use serde::{Deserialize, Serialize};
use std::num::NonZeroU64;

use crate::effect::EffectFailure;
use crate::instr::{Reg, PC};
use crate::owned::OwnedSession;
use crate::session::{SessionId, SessionStore};

/// Source-declared Unit command or authoritative readiness signature.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct NominalCommandDeclaration {
    /// Declared interface, admitted through the original protocol `uses`.
    pub interface: String,
    /// Exact operation on that interface.
    pub operation: String,
    /// Whether the declaration permits a pending result.
    pub may_block: bool,
    /// Exact predicate required for an authoritative readiness result.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub readiness_predicate: Option<String>,
}

/// Static invocation operands. These are not a live owner or continuation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct NominalCommandCall {
    /// Exact declaration which must also occur in the image manifest.
    pub declaration: NominalCommandDeclaration,
    /// Selected canonical OperationDeclaration name.
    pub enclosing_operation: String,
    /// Exact source agreement profile; first command slice admits NoAgreement only.
    pub agreement_profile: crate::semantic_objects::AgreementProfile,
    /// Explicit source execution role, equal to that operation's owner role.
    pub role: String,
    /// Named progress contract selected by the enclosing operation.
    pub progress_contract: String,
    /// Original named progress window selected by the enclosing operation.
    pub progress_window: String,
    /// Actual configured tick budget for that selected window; never physical time.
    pub budget_ticks: NonZeroU64,
    /// Register receiving the exact typed success payload, or String on Err.
    pub result: Reg,
    /// Executable success continuation.
    pub on_ok: PC,
    /// Executable application-error continuation.
    pub on_err: PC,
}

impl NominalCommandCall {
    /// The first executable command slice cannot implement stronger agreement.
    /// This check also governs manually constructed and deserialized images.
    pub(crate) fn supported_agreement(&self) -> bool {
        use crate::semantic_objects::{
            AgreementEvidenceKind, AgreementLevel, AgreementRule, OperationVisibility,
        };
        let profile = &self.agreement_profile;
        self.declaration
            .readiness_predicate
            .as_ref()
            .map_or(true, |predicate| {
                predicate
                    == &format!(
                        "{}.{}",
                        self.declaration.interface, self.declaration.operation
                    )
                    && self.declaration.may_block
            })
            && !profile.profile_name.is_empty()
            && profile.visibility == OperationVisibility::Immediate
            && profile.rule == AgreementRule::NoAgreement
            && profile.usable_at == AgreementLevel::None
            && profile.finalized_at == AgreementLevel::None
            && profile.required_evidence_kind == AgreementEvidenceKind::Witness
    }
}

/// Typed callback observation for the exact admitted result declaration.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct NominalCommandRequest {
    /// Original issued effect occurrence; not an ownership capability.
    pub invocation: u64,
    /// Actual session selected by the executing coroutine.
    pub session: SessionId,
    /// Actual coroutine, not a caller supplied role lookup.
    pub coroutine: usize,
    /// Exact admitted nominal declaration.
    pub declaration: NominalCommandDeclaration,
    /// Actual role at the invocation boundary.
    pub role: String,
}

/// Strongly typed callback payload. A Boolean never grants readiness authority.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum NominalCommandValue {
    /// Ordinary command application result.
    Bool(bool),
    /// Registry-issued evidence, validated and consumed only at gated commit.
    Readiness(telltale_types::ReadinessWitness),
}

impl NominalCommandValue {
    /// Require the exact source-declared payload and predicate; not issuance proof.
    pub(crate) fn require_declaration(
        &self,
        declaration: &NominalCommandDeclaration,
    ) -> Result<(), EffectFailure> {
        match (self, &declaration.readiness_predicate) {
            (Self::Bool(_), None) => Ok(()),
            (Self::Readiness(witness), Some(predicate))
                if predicate == &format!("{}.{}", declaration.interface, declaration.operation)
                    && declaration.may_block
                    && &witness.predicate_ref == predicate =>
            {
                Ok(())
            }
            _ => Err(EffectFailure::contract_violation(
                "nominal result does not match its declared readiness predicate/type",
            )),
        }
    }

    pub(crate) fn value(&self) -> crate::coroutine::Value {
        match self {
            Self::Bool(value) => crate::coroutine::Value::Bool(*value),
            Self::Readiness(witness) => crate::coroutine::Value::Readiness(witness.clone()),
        }
    }
}

/// Application result. Host failures remain distinct EffectFailure outcomes.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct NominalCommandReply {
    /// Must match the original live invocation, including on retry/replay.
    pub invocation: u64,
    /// Declared application result, not a host execution failure.
    pub result: Result<NominalCommandValue, String>,
}

/// Private live continuation retained only by its original coroutine.
/// Serde/checkpoint data cannot create one.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PendingNominalContinuation {
    pub(crate) invocation: u64,
    pub(crate) coroutine: usize,
    pub(crate) pc: PC,
    pub(crate) call: NominalCommandCall,
    pub(crate) owner: OwnedSession,
    pub(crate) issued_at: u64,
    pub(crate) handler_identity: String,
    pub(crate) validation_failure: Option<EffectFailure>,
    pub(crate) returned: Option<Result<NominalCommandValue, String>>,
}

impl PendingNominalContinuation {
    pub(crate) fn require_handler_identity(&self, actual: &str) -> Result<(), EffectFailure> {
        if self.handler_identity != actual {
            return Err(EffectFailure::contract_violation(
                "nominal invocation changed the original semantic handler identity",
            ));
        }
        Ok(())
    }

    pub(crate) fn validate_identity_at(
        &self,
        session: SessionId,
        coroutine: usize,
        pc: PC,
        call: &NominalCommandCall,
        tick: u64,
    ) -> Result<(), EffectFailure> {
        if self.owner.session_id() != session
            || self.coroutine != coroutine
            || self.pc != pc
            || self.call != *call
        {
            return Err(EffectFailure::contract_violation(
                "nominal continuation does not belong to this invocation",
            ));
        }
        let endpoint = self
            .issued_at
            .checked_add(self.call.budget_ticks.get())
            .ok_or_else(|| {
                EffectFailure::contract_violation("original nominal progress endpoint overflowed")
            })?;
        // Model OutstandingEffect.withinBudgetAt admits the endpoint itself.
        if tick > endpoint {
            return Err(EffectFailure::contract_violation(
                "original nominal progress window expired",
            ));
        }
        Ok(())
    }

    pub(crate) fn validate(
        &self,
        sessions: &SessionStore,
        session: SessionId,
        coroutine: usize,
        pc: PC,
        call: &NominalCommandCall,
        tick: u64,
    ) -> Result<(), EffectFailure> {
        self.validate_identity_at(session, coroutine, pc, call, tick)?;
        sessions
            .validate_ownership_capability(self.owner.capability())
            .map_err(|error| EffectFailure::contract_violation(error.to_string()))
    }
}

#[cfg(test)]
mod readiness_encoding_tests {
    use super::*;
    use crate::serialization::{binary_decode, binary_encode};

    fn witness() -> telltale_types::ReadinessWitness {
        telltale_types::ReadinessWitness {
            witness_id: 7,
            session_id: 2,
            owner_id: "original".into(),
            generation: 3,
            scope: telltale_types::OwnershipScope::Session,
            predicate_ref: "Host.ready".into(),
        }
    }

    #[test]
    fn explicit_typed_nominal_payload_round_trips_json_and_binary() {
        for value in [
            NominalCommandValue::Bool(true),
            NominalCommandValue::Readiness(witness()),
        ] {
            let reply = NominalCommandReply {
                invocation: 9,
                result: Ok(value),
            };
            let json = serde_json::to_vec(&reply).expect("typed JSON");
            assert_eq!(
                serde_json::from_slice::<NominalCommandReply>(&json).expect("decode JSON"),
                reply
            );
            let bytes = binary_encode(&reply).expect("canonical binary");
            assert_eq!(
                binary_decode::<NominalCommandReply>(&bytes).expect("decode binary"),
                reply
            );
        }
        assert!(
            serde_json::from_str::<NominalCommandReply>(r#"{"invocation":9,"result":{"Ok":true}}"#)
                .is_err(),
            "unversioned old draft Boolean shape is not typed evidence"
        );
    }

    #[test]
    fn readiness_result_cannot_substitute_a_foreign_predicate_or_immediate_class() {
        let mut declaration = NominalCommandDeclaration {
            interface: "Host".into(),
            operation: "ready".into(),
            may_block: true,
            readiness_predicate: Some("Host.ready".into()),
        };
        let genuine_shape = NominalCommandValue::Readiness(witness());
        assert!(
            genuine_shape.require_declaration(&declaration).is_ok(),
            "shape check is not registry issuance proof"
        );
        declaration.readiness_predicate = Some("Other.ready".into());
        let mut foreign = witness();
        foreign.predicate_ref = "Other.ready".into();
        assert!(NominalCommandValue::Readiness(foreign)
            .require_declaration(&declaration)
            .is_err());
        declaration.readiness_predicate = Some("Host.ready".into());
        declaration.may_block = false;
        assert!(genuine_shape.require_declaration(&declaration).is_err());
        declaration.may_block = true;
        assert!(NominalCommandValue::Bool(true)
            .require_declaration(&declaration)
            .is_err());
        declaration.readiness_predicate = None;
        assert!(NominalCommandValue::Bool(true)
            .require_declaration(&declaration)
            .is_ok());
    }

    #[test]
    fn appended_readiness_keeps_existing_value_and_type_discriminants() {
        use crate::coroutine::Value;
        use telltale_types::ValType;
        let values = [
            Value::Unit,
            Value::Nat(1),
            Value::Bool(true),
            Value::Str("x".into()),
            Value::Prod(Box::new(Value::Unit), Box::new(Value::Unit)),
            Value::Endpoint(crate::instr::Endpoint {
                sid: 1,
                role: "A".into(),
            }),
        ];
        let types = [
            ValType::Unit,
            ValType::Bool,
            ValType::Nat,
            ValType::String,
            ValType::Prod(Box::new(ValType::Unit), Box::new(ValType::Unit)),
            ValType::Chan {
                sid: 1,
                role: "A".into(),
            },
        ];
        for (index, (value, ty)) in values.iter().zip(types.iter()).enumerate() {
            let tag = u32::try_from(index)
                .expect("small stable index")
                .to_le_bytes();
            assert_eq!(&binary_encode(value).expect("value")[..4], &tag);
            assert_eq!(&binary_encode(ty).expect("type")[..4], &tag);
            assert_eq!(
                binary_decode::<Value>(&binary_encode(value).expect("value"))
                    .expect("value roundtrip"),
                *value
            );
            assert_eq!(
                binary_decode::<ValType>(&binary_encode(ty).expect("type"))
                    .expect("type roundtrip"),
                *ty
            );
        }
        assert_eq!(
            &binary_encode(&Value::Readiness(witness())).expect("new value")[..4],
            &6_u32.to_le_bytes()
        );
        assert_eq!(
            &binary_encode(&ValType::Readiness).expect("new type")[..4],
            &6_u32.to_le_bytes()
        );
    }
}

/// Resource-free observation of the actual original coroutine continuation.
/// This never contains an owned-session handle and cannot restore one.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct NominalContinuationView {
    /// Original canonical occurrence.
    pub invocation: u64,
    /// Original instruction PC in the role program.
    pub original_pc: PC,
    /// Exact original static call, including selected profile and window.
    pub call: NominalCommandCall,
    /// Original logical issuance tick.
    pub issued_at: u64,
    /// Admitted semantic handler identity, not physical provider identity.
    pub handler_identity: String,
    /// Actual staged application result, retained through commit refusal.
    pub returned: Option<Result<NominalCommandValue, String>>,
    /// Original semantic owner observation for every nominal call. These data
    /// cannot recreate the actual opaque holder retained by the coroutine.
    pub original_owner: crate::session::OwnershipCapability,
    /// Original owner observation on the readiness-specific view.
    pub readiness_owner: Option<crate::session::OwnershipCapability>,
    /// Original semantic validation refusal retained alongside the staged result.
    /// This observation neither replaces the first execution failure nor grants authority.
    pub validation_failure: Option<EffectFailure>,
}

impl crate::coroutine::Coroutine {
    /// Observe the actual retained continuation without exposing or issuing its
    /// live owner. Serialized observations cannot reconstruct the private holder.
    #[must_use]
    pub fn nominal_continuation_view(&self) -> Option<NominalContinuationView> {
        self.nominal_continuation
            .as_ref()
            .map(|original| NominalContinuationView {
                invocation: original.invocation,
                original_pc: original.pc,
                call: original.call.clone(),
                issued_at: original.issued_at,
                handler_identity: original.handler_identity.clone(),
                returned: original.returned.clone(),
                original_owner: original.owner.capability().clone(),
                readiness_owner: original
                    .call
                    .declaration
                    .readiness_predicate
                    .as_ref()
                    .map(|_| original.owner.capability().clone()),
                validation_failure: original.validation_failure.clone(),
            })
    }
}
