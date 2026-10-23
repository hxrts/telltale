import Runtime.ProtocolMachine.Model.Effects

set_option autoImplicit false
namespace Runtime.Tests.InvokeOutcomeAcceptance
open Runtime.ProtocolMachine.Model

example (state : List String) :
    (EffectOutcome.mk .success (some (.invokeStep state))).invokeStepState = some state := rfl

example (kind message : String) (response : Option EffectResponse) :
    (EffectOutcome.mk (.failure kind message) response).invokeStepState = none := rfl

example (response : Option EffectResponse) :
    (EffectOutcome.mk .blocked response).invokeStepState = none := rfl

example (kind message role : String) (state : List String) (response : Option EffectResponse) :
    (EffectOutcome.mk (.failure kind message) response).acceptedStatusFor (.invokeStep role state)
      = .failure kind message := rfl

example (role : String) (state : List String) :
    (EffectOutcome.mk .success (some .release)).acceptedStatusFor (.invokeStep role state)
      = .failure "contract_violation" "effect response kind does not match the original request" := rfl

example (role : String) (state : List String) :
    (EffectOutcome.mk .success (some (.receive state))).acceptedStatusFor (.invokeStep role state)
      = .failure "contract_violation" "effect response kind does not match the original request" := rfl

/-- Envelope acceptance requires the actual typed result to match its declaration.
This does not issue an owner, consume readiness, or acknowledge host settlement. -/
theorem matching_nominal_result_accepts_original_invocation
    (request : NominalCommandRequest) (result : Except String NominalCommandValue)
    (hmatches : ∀ value, result = .ok value →
      value.matchesDeclaration request.declaration = true) :
    (EffectOutcome.mk .success (some (.nominalCommand ⟨request.invocation, result⟩))).acceptedStatusFor
      (.nominalCommand request) = .success := by
  cases result with
  | error message => simp [EffectOutcome.acceptedStatusFor]
  | ok value => simp [EffectOutcome.acceptedStatusFor, hmatches value rfl]

/-- Boolean application results belong to plain command declarations. -/
theorem plain_bool_result_accepts_original_invocation
    (request : NominalCommandRequest) (value : Bool)
    (hplain : request.declaration.readinessPredicate = none) :
    (EffectOutcome.mk .success
      (some (.nominalCommand ⟨request.invocation, .ok (.bool value)⟩))).acceptedStatusFor
      (.nominalCommand request) = .success := by
  simp [EffectOutcome.acceptedStatusFor, NominalCommandValue.matchesDeclaration, hplain]

/-- A matching, well-formed readiness envelope is not a live registry admission. -/
theorem typed_readiness_result_matches_declared_predicate
    (request : NominalCommandRequest) (witness : SessionTypes.ReadinessWitness)
    (predicate : String)
    (hselected : request.declaration.readinessPredicate = some predicate)
    (hwellformed : request.declaration.readinessWellFormed = true)
    (hpredicate : witness.predicateRef = predicate) :
    (EffectOutcome.mk .success
      (some (.nominalCommand ⟨request.invocation, .ok (.readiness witness)⟩))).acceptedStatusFor
      (.nominalCommand request) = .success := by
  simp [EffectOutcome.acceptedStatusFor, NominalCommandValue.matchesDeclaration,
    hselected, hwellformed, hpredicate]

/-- Application Err is accepted as that original error, not business success. -/
theorem application_error_envelope_retains_original_error
    (request : NominalCommandRequest) (message : String) :
    let outcome := EffectOutcome.mk .success
      (some (.nominalCommand ⟨request.invocation, .error message⟩))
    outcome.acceptedStatusFor (.nominalCommand request) = .success ∧
      outcome.response = some (.nominalCommand ⟨request.invocation, .error message⟩) := by
  simp [EffectOutcome.acceptedStatusFor]

/-- A Boolean cannot stand in for a selected readiness result. -/
theorem bool_for_readiness_result_is_refused
    (request : NominalCommandRequest) (value : Bool) (predicate : String)
    (hselected : request.declaration.readinessPredicate = some predicate) :
    (EffectOutcome.mk .success
      (some (.nominalCommand ⟨request.invocation, .ok (.bool value)⟩))).acceptedStatusFor
      (.nominalCommand request) = .failure "contract_violation"
        "nominal result does not match its declared readiness predicate/type" := by
  simp [EffectOutcome.acceptedStatusFor, NominalCommandValue.matchesDeclaration, hselected]

/-- Equal occurrence IDs do not repair a foreign readiness predicate. -/
theorem foreign_readiness_predicate_is_refused
    (request : NominalCommandRequest) (witness : SessionTypes.ReadinessWitness)
    (predicate : String)
    (hselected : request.declaration.readinessPredicate = some predicate)
    (hforeign : witness.predicateRef ≠ predicate) :
    (EffectOutcome.mk .success
      (some (.nominalCommand ⟨request.invocation, .ok (.readiness witness)⟩))).acceptedStatusFor
      (.nominalCommand request) = .failure "contract_violation"
        "nominal result does not match its declared readiness predicate/type" := by
  simp [EffectOutcome.acceptedStatusFor, NominalCommandValue.matchesDeclaration,
    hselected, hforeign]

/-- A matching predicate cannot repair a malformed selected declaration. -/
theorem malformed_readiness_declaration_is_refused
    (request : NominalCommandRequest) (witness : SessionTypes.ReadinessWitness)
    (predicate : String)
    (hselected : request.declaration.readinessPredicate = some predicate)
    (hmalformed : request.declaration.readinessWellFormed = false) :
    (EffectOutcome.mk .success
      (some (.nominalCommand ⟨request.invocation, .ok (.readiness witness)⟩))).acceptedStatusFor
      (.nominalCommand request) = .failure "contract_violation"
        "nominal result does not match its declared readiness predicate/type" := by
  simp [EffectOutcome.acceptedStatusFor, NominalCommandValue.matchesDeclaration,
    hselected, hmalformed]

/-- Foreign occurrence refusal precedes acceptance of any typed result branch. -/
theorem wrong_nominal_invocation_is_refused
    (request : NominalCommandRequest) (replyId : Nat)
    (result : Except String NominalCommandValue) (hforeign : replyId ≠ request.invocation) :
    (EffectOutcome.mk .success
      (some (.nominalCommand ⟨replyId, result⟩))).acceptedStatusFor
      (.nominalCommand request) = .failure "contract_violation"
        "nominal reply belongs to a different invocation" := by
  simp [EffectOutcome.acceptedStatusFor, Ne.symm hforeign]

example (request : NominalCommandRequest) (kind message : String)
    (response : Option EffectResponse) :
    (EffectOutcome.mk (.failure kind message) response).acceptedStatusFor (.nominalCommand request)
      = .failure kind message := rfl

example (request : NominalCommandRequest) (response : Option EffectResponse) :
    (EffectOutcome.mk .blocked response).acceptedStatusFor (.nominalCommand request) = .blocked := rfl

end Runtime.Tests.InvokeOutcomeAcceptance
