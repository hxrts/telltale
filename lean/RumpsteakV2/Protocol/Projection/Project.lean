import RumpsteakV2.Protocol.Projection.Projectb
import RumpsteakV2.Protocol.Projection.Trans
import RumpsteakV2.Protocol.CoTypes.EQ2

/-! # RumpsteakV2.Protocol.Projection.Project

Proof-carrying projection API for V2.

## Expose

The following definitions form the semantic interface for proofs:

- `projectR?`: proof-carrying projection (returns projection with CProject proof)
- `projectR?_some_iff_CProject`: specification lemma
- `projectR?_sound`: soundness (some implies CProject)
- `projectR?_complete`: completeness (CProject implies some)
-/

namespace RumpsteakV2.Protocol.Projection.Project

open RumpsteakV2.Protocol.GlobalType
open RumpsteakV2.Protocol.LocalTypeR
open RumpsteakV2.Protocol.Projection.Trans
open RumpsteakV2.Protocol.Projection.Projectb
open RumpsteakV2.Protocol.CoTypes.EQ2

/-- Proof-carrying projection: returns the local type with a proof that CProject holds.
    Uses `trans` to compute the candidate and `projectb` to validate.
    Returns `some` iff projection succeeds. -/
def projectR? (g : GlobalType) (role : String) : Option { lt : LocalTypeR // CProject g role lt } :=
  let candidate := trans g role
  if h : projectb g role candidate = true then
    some ⟨candidate, projectb_sound g role candidate h⟩
  else
    none

/-- Inversion lemma: if projectR? returns some, then projectb was true. -/
theorem projectR?_some_implies_projectb {g : GlobalType} {role : String}
    {result : { lt : LocalTypeR // CProject g role lt }}
    (hsome : projectR? g role = some result) :
    projectb g role result.val = true := by
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
    exact False.elim (Option.noConfusion hsome)

/-- Soundness: if projectR? returns some, then CProject holds. -/
theorem projectR?_sound {g : GlobalType} {role : String}
    {result : { lt : LocalTypeR // CProject g role lt }}
    (_h : projectR? g role = some result) :
    CProject g role result.val :=
  result.property

/-! ## Projection-EQ2 Congruence Lemmas

The following lemmas establish that CProject and trans interact coherently with EQ2.
These correspond to key lemmas from the Coq development:
- `proj_proj`: if CProject g p e, then EQ2 e (trans g p)
- `Project_EQ2`: if CProject g p e0 and EQ2 e0 e1, then CProject g p e1 -/

/-- If CProject g role lt holds, then lt is EQ2-equivalent to trans g role.

This axiom corresponds to the Coq lemma `proj_proj` from indProj.v (lines 221-260).
The proof uses coinduction with case analysis on role participation:

1. **Participant case** (role is sender or receiver):
   - By induction on the participation path (`part_of_all2`)
   - For comm head: trans computes send/recv, CProject gives the same structure
   - For comm async: IH on the enabled branch continuation
   - For mu: unfold and use IH with substitution

2. **Non-participant case** (role is neither sender nor receiver):
   - trans computes by taking first branch's projection
   - CProject requires all branches to project identically (for non-participants)
   - Therefore trans g role = the unique projection
   - Result: EQ2 lt (trans g role) by EQ2_refl

The proof requires coinductive reasoning on EQ2 combined with structural
induction on participation, which interacts with the unfolding of mu types. -/
axiom CProject_implies_EQ2_trans (g : GlobalType) (role : String) (lt : LocalTypeR)
    (h : CProject g role lt) : EQ2 lt (trans g role)

/-- CProject is preserved under EQ2 equivalence.

This axiom corresponds to the Coq lemma `Project_EQ2` from indProj.v (lines 263-300).
The proof uses coinduction with case analysis on role participation:

1. **Participant case** (role is sender or receiver):
   - By induction on the participation path (`part_of_all2`)
   - For comm head: e0 and e1 have same structure (by EQ2), so CProject transfers
   - For comm async: IH on continuations, EQ2 gives matching continuations
   - For mu: unfold both sides using EQ2_unfold, apply IH

2. **Non-participant case**:
   - CProject requires projection to a unique type (all branches identical)
   - EQ2 equivalence means the projections are observationally equal
   - Therefore CProject holds for the EQ2-equivalent type

The proof requires coinductive reasoning on both CProject and EQ2, tracking
how their unfoldings interact for mu types. -/
axiom CProject_EQ2 (g : GlobalType) (role : String) (e0 e1 : LocalTypeR)
    (hproj : CProject g role e0) (heq : EQ2 e0 e1) : CProject g role e1

/-- trans produces a valid projection when CProject holds for some candidate.

This is a direct corollary of `CProject_implies_EQ2_trans` and `CProject_EQ2`:
- From h : CProject g role lt, we get EQ2 lt (trans g role)
- By CProject_EQ2 applied to h and this EQ2, we get CProject g role (trans g role)

The key insight is that for non-participants in a choice, all branches must
project to the same local type. The trans function picks the first branch's
projection as representative. Since all branches must agree (by the CProject
constraint), this representative satisfies the projection relation. -/
theorem trans_CProject (g : GlobalType) (role : String) (lt : LocalTypeR)
    (h : CProject g role lt) : CProject g role (trans g role) := by
  have heq : EQ2 lt (trans g role) := CProject_implies_EQ2_trans g role lt h
  exact CProject_EQ2 g role lt (trans g role) h heq

/-- trans computes the canonical projection when CProject holds. -/
theorem trans_is_projection (g : GlobalType) (role : String) (lt : LocalTypeR)
    (h : CProject g role lt) :
    projectb g role (trans g role) = true :=
  projectb_complete g role (trans g role) (trans_CProject g role lt h)

/-- Completeness: if CProject holds, then projectR? returns some. -/
theorem projectR?_complete (g : GlobalType) (role : String) (lt : LocalTypeR)
    (h : CProject g role lt) :
    ∃ result, projectR? g role = some result := by
  unfold projectR?
  have hproj : projectb g role (trans g role) = true := trans_is_projection g role lt h
  simp only [hproj, ↓reduceDIte]
  exact ⟨⟨trans g role, projectb_sound g role (trans g role) hproj⟩, rfl⟩

/-- Specification: projectR? returns some iff CProject holds for some local type. -/
theorem projectR?_some_iff_CProject (g : GlobalType) (role : String) :
    (∃ result, projectR? g role = some result) ↔ (∃ lt, CProject g role lt) := by
  constructor
  · intro ⟨result, _⟩
    exact ⟨result.val, result.property⟩
  · intro ⟨lt, h⟩
    exact projectR?_complete g role lt h

end RumpsteakV2.Protocol.Projection.Project
