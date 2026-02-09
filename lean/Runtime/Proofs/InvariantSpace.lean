import Runtime.Proofs.ProgressApi
import Runtime.VM.Model.OutputCondition

set_option autoImplicit false

/-! # Runtime.Proofs.InvariantSpace

Proof-carrying invariant-space bundle for VM theorem derivation.
-/

namespace Runtime
namespace Proofs

universe u v

section

variable {ν : Type u} [VerificationModel ν]

/-- Classical transport witness expected by transported theorem adapters. -/
structure ClassicalTransportWitness (State : Type v) where
  coherent : State → Prop
  harmony : Prop
  finiteState : Prop

/-- Output-condition witness expected by theorem-pack adapters. -/
structure OutputConditionWitness where
  verify : OutputConditionClaim → Bool
  accepted : OutputConditionClaim → Prop := fun _ => True
  sound : ∀ claim, verify claim = true → accepted claim

/-- Core VM invariant space:
- optional liveness bundle (enables termination/progress theorems when provided),
- optional classical transport witness for theorem transport,
- optional output-condition witness for predicate-gated output semantics. -/
structure VMInvariantSpace (store₀ : SessionStore ν) (State : Type v) where
  liveness? : Option (VMLivenessBundle store₀) := none
  classicalWitness? : Option (ClassicalTransportWitness State) := none
  outputConditionWitness? : Option OutputConditionWitness := none

/-- Attach a liveness bundle to an invariant space. -/
def VMInvariantSpace.withLiveness
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpace store₀ State)
    (bundle : VMLivenessBundle store₀) : VMInvariantSpace store₀ State :=
  { space with liveness? := some bundle }

/-- True iff an invariant space carries a liveness bundle. -/
def VMInvariantSpace.hasLiveness
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpace store₀ State) : Bool :=
  space.liveness?.isSome

/-- Attach a classical witness to an invariant space. -/
def VMInvariantSpace.withClassicalWitness
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpace store₀ State)
    (w : ClassicalTransportWitness State) : VMInvariantSpace store₀ State :=
  { space with classicalWitness? := some w }

/-- True iff an invariant space carries a classical transport witness. -/
def VMInvariantSpace.hasClassicalWitness
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpace store₀ State) : Bool :=
  space.classicalWitness?.isSome

/-- Attach an output-condition witness to an invariant space. -/
def VMInvariantSpace.withOutputConditionWitness
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpace store₀ State)
    (w : OutputConditionWitness) : VMInvariantSpace store₀ State :=
  { space with outputConditionWitness? := some w }

/-- True iff an invariant space carries output-condition witness evidence. -/
def VMInvariantSpace.hasOutputConditionWitness
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpace store₀ State) : Bool :=
  space.outputConditionWitness?.isSome

end

end Proofs
end Runtime
