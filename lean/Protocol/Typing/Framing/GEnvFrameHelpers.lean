import Protocol.Environments.Core
import Protocol.Typing.MergeLemmas

/-
The Problem. Provide small, reusable framing helpers for GEnv framing proofs
so right/left modules can share disjointness facts.

Solution Structure. Two focused lemmas: updating preserves disjointness and
splits inherit disjointness from the whole environment.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section

/-! ## Shared Helpers -/

/-- Helper: updateG preserves disjointness against a framed GEnv. -/
lemma disjointG_updateG_left
    {G Gfr : GEnv} {e : Endpoint} {L L0 : LocalType} :
    lookupG G e = some L0 →
    DisjointG G Gfr →
    DisjointG (updateG G e L) Gfr := by
  -- Use session-of inclusion after update to keep disjointness.
  intro hG hDisj
  have hEq := SessionsOf_updateG_eq (G:=G) (e:=e) (L:=L) (L':=L0) hG
  have hSub : SessionsOf (updateG G e L) ⊆ SessionsOf G := by
    intro s hs
    simpa [hEq] using hs
  exact DisjointG_of_subset_left hSub hDisj

/-- Helper: a par split inherits disjointness from the full GEnv. -/
lemma disjointG_split_frame_right
    {Sown : OwnedEnv} {G Gfr : GEnv} (split : ParSplit Sown.left G) :
    DisjointG G Gfr →
    DisjointG split.G1 Gfr ∧ DisjointG split.G2 Gfr := by
  -- Push disjointness through the session-of subsets of the split.
  intro hDisj
  have hSubG1 : SessionsOf split.G1 ⊆ SessionsOf G := by
    intro s hs
    simpa [split.hG] using SessionsOf_append_left (G₂:=split.G2) hs
  have hSubG2 : SessionsOf split.G2 ⊆ SessionsOf G := by
    intro s hs
    simpa [split.hG] using SessionsOf_append_right (G₁:=split.G1) hs
  exact ⟨DisjointG_of_subset_left hSubG1 hDisj, DisjointG_of_subset_left hSubG2 hDisj⟩
