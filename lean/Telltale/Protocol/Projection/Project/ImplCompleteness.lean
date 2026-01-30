import Telltale.Protocol.Projection.Project.ImplCompPostfix

/-! # Project ImplCompleteness

Completeness of the projection API: CProject implies projectR? returns some.
-/

set_option linter.unnecessarySimpa false

namespace Telltale.Protocol.Projection.Project

open Telltale.Protocol.GlobalType
open Telltale.Protocol.LocalTypeR
open Telltale.Protocol.Projection.Trans
open Telltale.Protocol.Projection.Projectb
open Telltale.Protocol.CoTypes.EQ2
open Telltale.Protocol.CoTypes.EQ2Props
open Telltale.Protocol.CoTypes.EQ2Paco
open Paco
open Telltale.Protocol.Participation

/-! ## Notes: EQ2-Closed Projection

CProject is preserved under EQ2 equivalence.

This corresponds to the Coq lemma `Project_EQ2` from indProj.v (lines 263-300).

### Proof Strategy

The proof uses coinduction on CProject with the relation:
```
EQ2_CProject_Rel g role e1 := ∃ e0, CProject g role e0 ∧ EQ2 e0 e1
```

### Case Analysis

**Participant case** (role is sender or receiver):
- By induction on the participation path
- For comm head: e0 = send/recv with some branches, e1 must have the same top-level
  form (by EQ2), so CProject transfers with BranchesRel from EQ2
- For mu: EQ2_unfold gives EQ2 on unfolded types, apply IH

**Non-participant case**:
- CProject requires AllBranchesProj: all branch continuations project to e0
- EQ2 e0 e1 means e1 is observationally equal to e0
- For each branch, we need CProject cont role e1
- This follows by IH on continuations + EQ2 transitivity

### Blocked Cases

The fundamental issue is that CProjectF requires the candidate local type to have
the same top-level constructor as dictated by the global type:
- g = end → candidate = end
- g = var t → candidate = var t
- g = mu t body → candidate = mu t' candBody (with t = t')
- g = comm (sender case) → candidate = send
- g = comm (receiver case) → candidate = recv

But EQ2 allows relating types with different constructors via mu unfolding.
When EQ2 e0 e1 holds with e0 having the "right" constructor but e1 being a mu
(or vice versa), the standard coinduction approach fails.

**Specific blocked cases:**

1. **end-mu / var-mu / send-mu / recv-mu**: When CProject gives e0 with a specific
   constructor but EQ2 e0 e1 where e1 is a mu that unfolds to that constructor.
   CProjectF requires exact constructor matching, but e1 has the wrong constructor.

2. **mu-mu with different binders:** EQ2 allows (.mu t body) ~ (.mu s body') with t ≠ s,
   but CProjectF requires the binder name to match the global type's binder.

3. **mu to non-mu:** When e0 is a mu but e1 unfolds to end/var/send/recv.
   CProjectF requires e1 to be a mu to match g = mu.

The Coq proof uses parametrized coinduction (pcofix) which can "remember" that
e0 and e1 are EQ2-equivalent across unfolding steps, resolving these cases.

### Coq Reference

See `subject_reduction/theories/Projection/indProj.v:263-300` for the Coq proof
which uses `pcofix CIH` with participation predicates.

### Semantic Soundness

If `CProject g role e0` holds and `EQ2 e0 e1` (i.e., e0 and e1 are observationally
equivalent under equi-recursive equality), then `CProject g role e1` must hold.
This is because:
1. CProject captures the structure of projecting a global type to a local type
2. EQ2 is an observational equivalence that respects all session type behaviors
3. If e0 satisfies the projection constraints and e1 behaves identically to e0,
   then e1 must also satisfy the projection constraints

The key insight is that EQ2 is a congruence: it preserves structure while allowing
mu-unfolding. The projection relation is defined coinductively, so any finite
observation of e1 can be matched by the corresponding observation of e0.

**Proof strategy using coinduction:**
1. Define witness relation: `∃ e0, CProject g role e0 ∧ EQ2 e0 e1`
2. Show it's a post-fixpoint of CProjectF
3. Use extraction lemmas to convert EQ2 structure to constructor information about e1
4. Apply CProject_coind

The proof requires case analysis on the global type `g` and using the appropriate
EQ2 extraction lemmas (`EQ2.end_right_implies_UnfoldsToEnd`, etc.) to extract
the shape of `e1` from `EQ2 e0 e1`.

**Challenge**: CProjectF requires exact constructor matching (e.g., `.end` matches `.end`),
but EQ2 allows mu-wrapping (e.g., `EQ2 .end (.mu t .end)`). The extraction lemmas give
`UnfoldsTo*` predicates, but we need exact constructor equality for CProjectF.

**Possible approaches**:
1. Strengthen extraction lemmas to provide constructor equality (not just unfolding)
2. Use Bisim.toBisim and prove CProject is closed under Bisim
3. Modify CProjectF to accept mu-wrapped candidates (major change)
4. Prove auxiliary lemmas showing EQ2 preserves "canonical forms" for each constructor

We now proceed without this EQ2-closed projection scaffold and rely on the
`trans_eq_of_CProject` path for constructing `trans` projections. -/

/-- CProject implies EQ2 between the candidate and `trans` (wrapper lemma). -/
theorem CProject_implies_EQ2_trans (g : GlobalType) (role : String) (lt : LocalTypeR)
    (h : CProject g role lt) (hwf : g.wellFormed = true) : EQ2 lt (Trans.trans g role) :=
  CProject_implies_EQ2_trans_thm g role lt h hwf

/-- BranchesRel for EQ2 implies branch-wise EQ2.

If BranchesProjRel CProject gbs role lbs holds, and gbs are transBranches'd,
then the local branches are EQ2-related. -/
private theorem BranchesProjRel_implies_BranchesRel_EQ2_cons
    {gLabel : Label} {gCont : GlobalType} {lLabel : Label} {lCont : LocalTypeR}
    {gbs_tail : List (Label × GlobalType)} {lbs_tail : List (Label × LocalTypeR)}
    (role : String)
    (hlab : gLabel = lLabel) (hproj : CProject gCont role lCont)
    (hwf : ∀ gb, gb ∈ (gLabel, gCont) :: gbs_tail → gb.2.wellFormed = true)
    (htail : BranchesRel EQ2 lbs_tail (transBranches gbs_tail role)) :
    BranchesRel EQ2 ((lLabel, lCont) :: lbs_tail)
      (transBranches ((gLabel, gCont) :: gbs_tail) role) := by
  -- Use head well-formedness to relate the head continuation via trans.
  have hwf_head : (gLabel, gCont).2.wellFormed = true := by
    exact hwf (gLabel, gCont) (by simp)
  have heq : EQ2 lCont (Trans.trans gCont role) :=
    CProject_implies_EQ2_trans _ _ _ hproj hwf_head
  have htail' :
      List.Forall₂ (fun a b => a.1 = b.1 ∧ EQ2 a.2 b.2)
        lbs_tail (transBranches gbs_tail role) := by
    simpa [BranchesRel] using htail
  have htb :
      transBranches ((gLabel, gCont) :: gbs_tail) role =
        (gLabel, trans gCont role) :: transBranches gbs_tail role := by
    simp [transBranches]
  have hcons :
      List.Forall₂ (fun a b => a.1 = b.1 ∧ EQ2 a.2 b.2)
        ((lLabel, lCont) :: lbs_tail)
        ((gLabel, trans gCont role) :: transBranches gbs_tail role) :=
    List.Forall₂.cons ⟨hlab.symm, by simpa using heq⟩ htail'
  simpa [BranchesRel, htb] using hcons

/-- BranchesProjRel implies branch-wise EQ2 on transBranches. -/
theorem BranchesProjRel_implies_BranchesRel_EQ2
    (gbs : List (Label × GlobalType)) (role : String)
    (lbs : List (Label × LocalTypeR)) (hwf : ∀ gb, gb ∈ gbs → gb.2.wellFormed = true)
    (h : BranchesProjRel CProject gbs role lbs) :
    BranchesRel EQ2 lbs (transBranches gbs role) := by
  -- By induction on BranchesProjRel, show each pair is EQ2-related
  induction h with
  | nil =>
      simp [BranchesRel, transBranches]
  | cons hpair hrest ih =>
      rename_i gb lb gbs_tail lbs_tail
      cases gb with
      | mk gLabel gCont =>
          cases lb with
          | mk lLabel lCont =>
              rcases hpair with ⟨hlab, hproj⟩
              have hwf_tail : ∀ gb', gb' ∈ gbs_tail → gb'.2.wellFormed = true := by
                intro gb' hmem'
                exact hwf gb' (List.mem_cons_of_mem _ hmem')
              have htail : BranchesRel EQ2 lbs_tail (transBranches gbs_tail role) := ih hwf_tail
              exact BranchesProjRel_implies_BranchesRel_EQ2_cons role hlab hproj hwf htail

/-- AllBranchesProj with trans gives EQ2.

For non-participants, AllBranchesProj CProject gbs role lt means all branches
project to lt. The trans of the first branch should be EQ2 to lt. -/
private theorem AllBranchesProj_implies_EQ2_trans_cons
    (sender receiver role : String) (first : Label × GlobalType) (rest : List (Label × GlobalType))
    (lt : LocalTypeR) (hns : role ≠ sender) (hnr : role ≠ receiver)
    (hall : AllBranchesProj CProject (first :: rest) role lt)
    (hwf : (GlobalType.comm sender receiver (first :: rest)).wellFormed = true) :
    EQ2 lt (trans (GlobalType.comm sender receiver (first :: rest)) role) := by
  -- Use the head branch projection and relate it to trans.
  have hproj : CProject first.2 role lt := hall first (by simp)
  have hwf_first : first.2.wellFormed = true :=
    GlobalType.wellFormed_comm_branches sender receiver (first :: rest) hwf first (by simp)
  have heq : EQ2 lt (Trans.trans first.2 role) :=
    CProject_implies_EQ2_trans _ _ _ hproj hwf_first
  -- Non-participants project to the first branch.
  have htrans : trans (GlobalType.comm sender receiver (first :: rest)) role =
      trans first.2 role := by
    simpa using trans_comm_other sender receiver role (first :: rest) hns hnr
  simpa [htrans] using heq

/-- AllBranchesProj on a non-empty comm list yields EQ2 with trans. -/
theorem AllBranchesProj_implies_EQ2_trans
    (sender receiver role : String) (gbs : List (Label × GlobalType)) (lt : LocalTypeR)
    (hns : role ≠ sender) (hnr : role ≠ receiver)
    (hall : AllBranchesProj CProject gbs role lt)
    (hne : gbs ≠ [])
    (hwf : (GlobalType.comm sender receiver gbs).wellFormed = true) :
    EQ2 lt (trans (GlobalType.comm sender receiver gbs) role) := by
  -- Reduce to the non-empty branch case.
  cases gbs with
  | nil => exact (hne rfl).elim
  | cons first rest =>
      exact AllBranchesProj_implies_EQ2_trans_cons sender receiver role first rest lt hns hnr hall hwf

/-! ## Projection API Completeness -/

/-- trans produces a valid projection when CProject holds for some candidate.

This follows from `trans_eq_of_CProject`: trans computes the same local type
whenever CProject holds and all comms are non-empty.

The key insight is that for non-participants in a choice, all branches must
project to the same local type. The trans function picks the first branch's
projection as representative. Since all branches must agree (by the CProject
constraint), this representative satisfies the projection relation.

Requires `wellFormed` assumption (matching Coq's global invariants). -/
theorem trans_CProject
    (_hend : ∀ e, EQ2 .end e → e = .end)
    (_hvar : ∀ t e, EQ2 (.var t) e → e = .var t)
    (_hsend : ∀ p bs e, EQ2 (.send p bs) e →
      ∃ cs, e = .send p cs ∧ BranchesRel EQ2 bs cs)
    (_hrecv : ∀ p bs e, EQ2 (.recv p bs) e →
      ∃ cs, e = .recv p cs ∧ BranchesRel EQ2 bs cs)
    (_hmu : ∀ t body e, EQ2 (.mu t body) e →
      ∃ body', e = .mu t body' ∧ EQ2 body body')
    (g : GlobalType) (role : String) (lt : LocalTypeR)
    (h : CProject g role lt) (hwf : g.wellFormed = true) : CProject g role (trans g role) := by
  -- Use trans_eq_of_CProject to replace the candidate with trans.
  have hne : g.allCommsNonEmpty = true := by
    simp only [GlobalType.wellFormed, Bool.and_eq_true] at hwf
    exact hwf.1.1.2
  have htrans_eq : trans g role = lt := trans_eq_of_CProject g role lt h hne
  simpa [htrans_eq] using h

/-- trans computes the canonical projection when CProject holds. -/
theorem trans_is_projection
    (hend : ∀ e, EQ2 .end e → e = .end)
    (hvar : ∀ t e, EQ2 (.var t) e → e = .var t)
    (hsend : ∀ p bs e, EQ2 (.send p bs) e →
      ∃ cs, e = .send p cs ∧ BranchesRel EQ2 bs cs)
    (hrecv : ∀ p bs e, EQ2 (.recv p bs) e →
      ∃ cs, e = .recv p cs ∧ BranchesRel EQ2 bs cs)
    (hmu : ∀ t body e, EQ2 (.mu t body) e →
      ∃ body', e = .mu t body' ∧ EQ2 body body')
    (g : GlobalType) (role : String) (lt : LocalTypeR)
    (h : CProject g role lt) (hwf : g.wellFormed = true) :
    projectb g role (trans g role) = true := by
    -- Reduce to projectb_complete with the trans_CProject witness.
    have hne : g.allCommsNonEmpty = true := by
      -- wellFormed = (((allVarsBound ∧ allCommsNonEmpty) ∧ noSelfComm) ∧ isProductive)
      simp only [GlobalType.wellFormed, Bool.and_eq_true] at hwf
      exact hwf.1.1.2
    exact projectb_complete g role (trans g role)
      (trans_CProject hend hvar hsend hrecv hmu g role lt h hwf) hne

/-- Completeness: if CProject holds, then projectR? returns some.

Requires `wellFormed` assumption (matching Coq's global invariants). -/
theorem projectR?_complete
    (hend : ∀ e, EQ2 .end e → e = .end)
    (hvar : ∀ t e, EQ2 (.var t) e → e = .var t)
    (hsend : ∀ p bs e, EQ2 (.send p bs) e →
      ∃ cs, e = .send p cs ∧ BranchesRel EQ2 bs cs)
    (hrecv : ∀ p bs e, EQ2 (.recv p bs) e →
      ∃ cs, e = .recv p cs ∧ BranchesRel EQ2 bs cs)
    (hmu : ∀ t body e, EQ2 (.mu t body) e →
      ∃ body', e = .mu t body' ∧ EQ2 body body')
    (g : GlobalType) (role : String) (lt : LocalTypeR)
    (h : CProject g role lt) (hwf : g.wellFormed = true) :
    ∃ result, projectR? g role = some result := by
  -- Unfold projectR? and plug in trans_is_projection.
  unfold projectR?
  have hproj : projectb g role (trans g role) = true :=
    trans_is_projection hend hvar hsend hrecv hmu g role lt h hwf
  simp only [hproj, ↓reduceDIte]
  exact ⟨⟨trans g role, projectb_sound g role (trans g role) hproj⟩, rfl⟩

/-- Specification: projectR? returns some iff CProject holds for some local type.

Note: The forward direction (some → CProject) requires no wellFormedness assumption.
The reverse direction (CProject → some) requires `wellFormed`. -/
theorem projectR?_some_iff_CProject
    (hend : ∀ e, EQ2 .end e → e = .end)
    (hvar : ∀ t e, EQ2 (.var t) e → e = .var t)
    (hsend : ∀ p bs e, EQ2 (.send p bs) e →
      ∃ cs, e = .send p cs ∧ BranchesRel EQ2 bs cs)
    (hrecv : ∀ p bs e, EQ2 (.recv p bs) e →
      ∃ cs, e = .recv p cs ∧ BranchesRel EQ2 bs cs)
    (hmu : ∀ t body e, EQ2 (.mu t body) e →
      ∃ body', e = .mu t body' ∧ EQ2 body body')
    (g : GlobalType) (role : String) (hwf : g.wellFormed = true) :
    (∃ result, projectR? g role = some result) ↔ (∃ lt, CProject g role lt) := by
  -- Split directions; forward is immediate, backward uses projectR?_complete.
  constructor
  · intro ⟨result, _⟩
    exact ⟨result.val, result.property⟩
  · intro ⟨lt, h⟩
    exact projectR?_complete hend hvar hsend hrecv hmu g role lt h hwf


end Telltale.Protocol.Projection.Project
