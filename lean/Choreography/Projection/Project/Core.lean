import Choreography.Projection.Projectb
import Choreography.Projection.Trans
import Choreography.Projection.Blind
import SessionCoTypes.EQ2

/-! # Choreography.Projection.Project.Core

Core projection API and projectability predicates.

## Expose

The following definitions form the semantic interface for proofs:

- `Projectable`: projectability predicate for globals
- `ProjectableClosedWellFormed`: closed/wellFormed + projectable bundle
- `ProjectableClosedWellFormedBlind`: axiom-free version using blindness
- `projectR?`: proof-carrying projection
- `projectR?_some_implies_projectb`: inversion lemma for projectR?
- `projectR?_sound`: soundness of projectR?
- `CProject_unguarded_trans`: helper for mu-unguarded case
-/

/-
The Problem. Provide a minimal, proof-carrying API for projection that proofs can rely on
without importing the entire inductive development.

Solution Structure. We isolate the projectability predicates and the proof-carrying
projection function `projectR?`, along with a small helper lemma used in mu cases.
-/

namespace Choreography.Projection.Project

open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
open Choreography.Projection.Trans
open Choreography.Projection.Projectb
open SessionCoTypes.EQ2

/-! ## Projectability -/

/-- A global type is projectable if every role has some CProject witness. -/
def Projectable (g : GlobalType) : Prop :=
  -- Require a projection witness for every role.
  ∀ role, ∃ lt, CProject g role lt

/-- Closed + well-formed globals that are projectable. -/
def ProjectableClosedWellFormed (g : GlobalType) : Prop :=
  g.isClosed = true ∧ g.wellFormed = true ∧ Projectable g

/-- Closed + well-formed + blind globals. This is the axiom-free version:
    blindness ensures projectability without needing an axiom. -/
def ProjectableClosedWellFormedBlind (g : GlobalType) : Prop :=
  g.isClosed = true ∧ g.wellFormed = true ∧ Blind.isBlind g = true

/-- ProjectableClosedWellFormedBlind implies ProjectableClosedWellFormed.
    This uses the blindness theorem to derive projectability without axioms. -/
theorem ProjectableClosedWellFormedBlind_implies_ProjectableClosedWellFormed
    {g : GlobalType} (h : ProjectableClosedWellFormedBlind g) :
    ProjectableClosedWellFormed g := by
  obtain ⟨hclosed, hwf, hblind⟩ := h
  refine ⟨hclosed, hwf, ?_⟩
  -- Use the blindness theorem to derive Projectable
  have hwfb : Blind.WellFormedBlind g = true := by
    simp only [Blind.WellFormedBlind, Bool.and_eq_true]
    exact ⟨⟨hclosed, hwf⟩, hblind⟩
  exact Blind.projectable_of_wellFormedBlind g hwfb

/-- Extract the Projectable component from ProjectableClosedWellFormedBlind. -/
theorem Projectable_of_ProjectableClosedWellFormedBlind
    {g : GlobalType} (h : ProjectableClosedWellFormedBlind g) :
    Projectable g :=
  (ProjectableClosedWellFormedBlind_implies_ProjectableClosedWellFormed h).2.2

/-! ## Core Projection API -/

/-- Unguardedness preservation for trans (under non-empty comms). -/
theorem CProject_unguarded_trans {g : GlobalType} {role : String} {lt : LocalTypeR} {v : String}
    (hproj : CProject g role lt) (hne : g.allCommsNonEmpty = true) (hguard : lt.isGuarded v = false) :
    (trans g role).isGuarded v = false := by
  -- Collapse the CProject witness to equality with trans, then rewrite.
  have htrans : trans g role = lt := trans_eq_of_CProject g role lt hproj hne
  simpa [htrans] using hguard

/-- Proof-carrying projection: returns the local type with a proof that CProject holds.
    Uses `trans` to compute the candidate and `projectb` to validate.
    Returns `some` iff projection succeeds. -/
def projectR? (g : GlobalType) (role : String) : Option { lt : LocalTypeR // CProject g role lt } :=
  -- Compute the candidate and validate it with projectb.
  let candidate := trans g role
  if h : projectb g role candidate = true then
    -- Success case: return the candidate with its CProject proof.
    some ⟨candidate, projectb_sound g role candidate h⟩
  else
    -- Failure case: projection does not validate.
    none

/-- Inversion lemma: if projectR? returns some, then projectb was true. -/
theorem projectR?_some_implies_projectb {g : GlobalType} {role : String}
    {result : { lt : LocalTypeR // CProject g role lt }}
    (hsome : projectR? g role = some result) :
    projectb g role result.val = true := by
  -- Unfold projectR? and analyze the projectb decision.
  simp only [projectR?] at hsome
  by_cases hproj : projectb g role (trans g role) = true
  · simp only [hproj, ↓reduceDIte, Option.some.injEq] at hsome
    cases result with
    | mk val property =>
        simp only [Subtype.mk.injEq] at hsome
        subst hsome
        exact hproj
  · -- In this case, projectR? returns none, but hsome says it's some - contradiction
    rw [dif_neg hproj] at hsome
    exact nomatch hsome

/-- Soundness: if projectR? returns some, then CProject holds. -/
theorem projectR?_sound {g : GlobalType} {role : String}
    {result : { lt : LocalTypeR // CProject g role lt }}
    (_h : projectR? g role = some result) :
    CProject g role result.val := by
  -- The dependent pair returned by projectR? carries the CProject proof.
  exact result.property

end Choreography.Projection.Project
