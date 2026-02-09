import Runtime.VM.Model.TypeClasses

/-!
# VM Output-Condition Model

Core model types for output-condition commit gating.

- `OutputConditionClaim`: predicate id + optional witness reference + output digest.
- `OutputConditionCheck`: verifier decision logged in VM state for replay/audit.
 -/

set_option autoImplicit false

universe u

structure OutputConditionClaim where
  -- Stable predicate identifier (id/hash string in V1).
  predicateRef : String
  -- Optional witness payload reference (opaque in V1).
  witnessRef : Option String := none
  -- Opaque digest/summary of the candidate output.
  outputDigest : Value := .unit
  deriving Repr, DecidableEq

structure OutputConditionCheck where
  -- Checked claim payload.
  claim : OutputConditionClaim
  -- Deterministic verifier outcome.
  passed : Bool
  deriving Repr, DecidableEq

inductive OutputConditionPolicy where
  -- Disable output-condition gating.
  | disabled
  -- Accept every claim.
  | allowAll
  -- Reject every claim.
  | denyAll
  -- Accept only predicates in the allow-list.
  | allowList (predicates : List String)
  deriving Repr, DecidableEq

def OutputConditionPolicy.accepts (p : OutputConditionPolicy) (claim : OutputConditionClaim) : Bool :=
  match p with
  | .disabled => true
  | .allowAll => true
  | .denyAll => false
  | .allowList preds => preds.contains claim.predicateRef

structure OutputConditionConfig where
  -- Policy-level gate.
  policy : OutputConditionPolicy := .allowAll
  -- Optional deterministic verifier override.
  verify : OutputConditionClaim → Bool := fun claim => policy.accepts claim
