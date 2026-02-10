import Runtime.Proofs.TheoremPack.Artifacts

/-! # Runtime.Proofs.TheoremPack.API

Public facade for theorem-pack construction and inventory.

Downstream modules should prefer this API layer over directly importing
builder/artifact internals.
-/

namespace Runtime
namespace Proofs
namespace TheoremPackAPI

universe u v

variable {ν : Type u} [VerificationModel ν]

/-- API alias: build theorem-pack artifacts from a profile space. -/
abbrev mk
    {store₀ : SessionStore ν} {State : Type v}
    {space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State} :
    VMTheoremPack (space := space) :=
  buildVMTheoremPack (space := space)

/-- API alias: compact capability inventory. -/
abbrev capabilities
    {store₀ : SessionStore ν} {State : Type v}
    {space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State}
    (pack : VMTheoremPack (space := space)) : List (String × Bool) :=
  theoremInventory (space := space) pack

/-- API alias: capability inventory augmented with determinism flags. -/
abbrev capabilitiesWithDeterminism
    {store₀ : SessionStore ν} {State : Type v}
    {space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State}
    (pack : VMTheoremPack (space := space))
    (determinism : VMDeterminismArtifacts) : List (String × Bool) :=
  theoremInventoryWithDeterminism (space := space) pack determinism

end TheoremPackAPI
end Proofs
end Runtime
