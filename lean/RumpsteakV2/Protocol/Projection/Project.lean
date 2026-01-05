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

### Proof Strategy

The proof uses coinduction on EQ2 with the relation:
```
CProjectTransRel lt cand := ∃ g role, CProject g role lt ∧ cand = trans g role
```

For most cases (end, var, comm-sender, comm-receiver), the structure of CProject
and trans match directly:
- `CProject .end role .end` and `trans .end role = .end` → EQ2F trivially True
- `CProject (.var t) role (.var t)` and `trans (.var t) role = .var t` → names equal
- Participant comm cases: CProject gives send/recv with BranchesProjRel,
  trans gives send/recv with transBranches, structures match

### Blocked Cases

**mu case:** When `CProject (.mu t body) role (.mu t candBody)` and
`trans (.mu t body) role = .mu t (trans body role)`:
- EQ2F for two mu types requires showing unfolding pairs are related:
  1. `(candBody.substitute t (.mu t candBody), .mu t (trans body role))`
  2. `(.mu t candBody, (trans body role).substitute t (...))`
- These substituted types don't directly correspond to any CProject/trans pair
- Need a helper lemma: CProject_substitute or trans_substitute_EQ2
- The Coq proof uses pcofix (parametrized coinduction) to handle this

**empty branches case:** For non-participant with empty branches:
- CProject's AllBranchesProj is vacuously true for any lt
- trans returns .end
- Need EQ2F lt .end, but lt is unconstrained
- This may indicate a gap in the CProject definition for edge cases

**nested non-participant case:** For non-participant where first branch is also
a non-participant comm:
- Requires well-founded recursion on global type size
- Standard coinduction postfix proof doesn't capture this pattern

### Required Sub-Lemmas

1. `CProject_substitute`: If `CProject body role candBody`, then
   `CProject (body.substitute t (mu t body)) role (candBody.substitute t (mu t candBody))`

2. `trans_substitute_EQ2`: Trans commutes with substitution up to EQ2:
   `EQ2 (trans (g.substitute t repl) role) ((trans g role).substitute t (trans repl role))`

### Coq Reference

See `subject_reduction/theories/Projection/indProj.v:221-260` for the Coq proof
which uses `pcofix CIH` (parametrized coinduction from paco library). -/
axiom CProject_implies_EQ2_trans (g : GlobalType) (role : String) (lt : LocalTypeR)
    (h : CProject g role lt) : EQ2 lt (trans g role)

/-- CProject is preserved under EQ2 equivalence.

This axiom corresponds to the Coq lemma `Project_EQ2` from indProj.v (lines 263-300).

### Proof Strategy

The proof uses coinduction on CProject with the relation:
```
EQ2_CProject_Rel g role e1 := ∃ e0, CProject g role e0 ∧ EQ2 e0 e1
```

### Case Analysis

**Participant case** (role is sender or receiver):
- By induction on the participation path
- For comm head: e0 = send/recv with some branches, e1 must have same top-level
  structure (by EQ2), so CProject transfers with BranchesRel from EQ2
- For mu: EQ2_unfold gives EQ2 on unfolded types, apply IH

**Non-participant case**:
- CProject requires AllBranchesProj: all branch continuations project to e0
- EQ2 e0 e1 means e1 is observationally equal to e0
- For each branch, we need CProject cont role e1
- This follows by IH on continuations + EQ2 transitivity

### Blocked Cases

**mu case with different binders:** When g = mu t body and e0 = mu t' body0:
- EQ2 (mu t' body0) e1 could have e1 = mu s' body1 with s' ≠ t'
- Need to show CProject (mu t body) role (mu s' body1)
- This requires tracking how EQ2's mu unfolding interacts with CProject

**Branch-wise EQ2 lifting:** For participant comm cases:
- EQ2 gives BranchesRel EQ2 on branch continuations
- Need to transfer CProject branch-by-branch
- Requires BranchesRel to lift through CProject correctly

### Coq Reference

See `subject_reduction/theories/Projection/indProj.v:263-300` for the Coq proof
which uses `pcofix CIH` with participation predicates. -/
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
