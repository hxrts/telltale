import Protocol.Typing.Core.Environments.CoreDefs

/-! # Protocol.Typing.Core.Environments.Disjointness

Right-side disjointness closure lemmas.
-/

/-
The Problem. Final disjointness lemmas on right-side subsets/dom-subsets are
used by framing proofs but need not live in the large core definitions file.

Solution Structure. Isolates the two right-side disjointness closure lemmas.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section

theorem DisjointS_of_subset_right {S₁ S₂ S₂' : SEnv} :
    SEnvSubset S₂' S₂ →
    DisjointS S₁ S₂ →
    DisjointS S₁ S₂' := by
  intro hSub hDisj x T₁ T₂ hL1 hL2
  exact hDisj x T₁ T₂ hL1 (hSub hL2)

theorem DisjointS_of_domsubset_right {S₁ S₂ S₂' : SEnv} :
    SEnvDomSubset S₂' S₂ →
    DisjointS S₁ S₂ →
    DisjointS S₁ S₂' := by
  intro hSub hDisj x T₁ T₂ hL1 hL2
  obtain ⟨T₂', hL2'⟩ := hSub hL2
  exact hDisj x T₁ T₂' hL1 hL2'


end
