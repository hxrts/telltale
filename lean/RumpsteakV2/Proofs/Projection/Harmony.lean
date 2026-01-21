import RumpsteakV2.Semantics.EnvStep
import RumpsteakV2.Protocol.Projection.Projectb
import RumpsteakV2.Protocol.Projection.Project
import RumpsteakV2.Protocol.Participation
import RumpsteakV2.Protocol.CoTypes.EQ2
import RumpsteakV2.Protocol.CoTypes.EQ2Paco
import RumpsteakV2.Protocol.Projection.ProjSubst
import RumpsteakV2.Proofs.Safety.Determinism
import RumpsteakV2.Proofs.Projection.MuUnfoldLemmas
import RumpsteakV2.Proofs.Projection.SubstEndUnguarded

/-! # RumpsteakV2.Proofs.Projection.Harmony

Harmony between global steps and environment steps.

## Expose

The following definitions form the semantic interface for proofs:

- `Claims`: bundle of harmony properties
- `step_harmony`: global step induces matching env step
- `proj_trans_other_step`: non-participant projection unchanged after step

## Technical Debt Summary (7 sorries, 0 axioms in this file)

**MAJOR PROGRESS**: Axiom `trans_branches_coherent` ELIMINATED!
Coherence is now proven from first principles using participation structure, following Coq's proof strategy.

**Mu-unfolding (from MuUnfoldLemmas.lean):**
- `EQ2_mu_crossed_unfold_left`: **PROVEN** via proj_subst + EQ2_mu_self_unfold
- `EQ2_mu_crossed_unfold_right`: **PROVEN** via proj_subst + EQ2_mu_to_unfold
- `EQ2_mu_unguarded_to_end`: **PROVEN** (vacuously true - hypotheses contradict when s ≠ t)
- `EQ2_end_to_mu_unguarded`: **PROVEN** (vacuously true for closed types)

**Closedness theorems (PROVEN in GlobalType.lean):**
- `GlobalType.isClosed_substitute_mu`: **PROVEN** - mu-unfolding preserves closedness
- `GlobalType.isClosed_comm_branches`: **PROVEN** - closed comm has closed branches

**Proven coinductive theorems:**
- `subst_end_unguarded_eq2_end`: **PROVEN** in SubstEndUnguarded.lean via UnfoldsToEnd induction
- `trans_subst_comm`: **PROVEN** using paco coinduction (requires closedness)
- `EQ2_trans`: **PROVEN** imported from EQ2.lean

**Remaining Axioms:** None (sender/receiver lemmas proven via head-action predicate)

**COHERENCE PROOF COMPLETE (modulo helper lemmas):**
- `trans_branches_coherent_EQ2`: **PROVEN** using participation structure
  - Case 1 (non-participant): Uses `EQ_end` - all branches project to .end
  - Case 2 (participant): Uses `part_of_all2` - uniform participation (2 sorries for extraction)
- `trans_produces_CProject`: Bridges trans to CProject (uses coherence)
- `branches_project_coherent`: Extracts EQ2 equivalence from AllBranchesProj (3 sorries)

**Inherited from MuUnfoldLemmas.lean (via ProjSubst.lean):**
4. `proj_subst`: Projection-substitution commutation (Coq indProj.v:173)

**Key changes from Coq alignment:**
- `trans` now checks `(trans body role).isGuarded t` instead of `lcontractive body`
- This matches Coq's `eguarded` check on the projected type, not the global type
- Non-contractive projections are replaced with `.end` by construction
- The old `step_noncontr_impossible` axiom was removed (it was false for nested mu)
- All theorems require closedness of global types (standard for protocol verification)

**Next steps:** propagate the head-action predicate (`action_pred`) through callers
if they need sender/receiver projections beyond the head-communication case.
-/

namespace RumpsteakV2.Proofs.Projection.Harmony

open RumpsteakV2.Protocol.GlobalType
open RumpsteakV2.Protocol.LocalTypeR
open RumpsteakV2.Protocol.Projection.Projectb
open RumpsteakV2.Protocol.Projection.Project
  (EQ_end part_of2_or_end CProject_implies_EQ2_trans Projectable ProjectableClosedWellFormed)
open RumpsteakV2.Protocol.Participation (part_of2 part_of_all2 part_of_all2_comm_inv not_part_of2_comm)
open RumpsteakV2.Protocol.CoTypes.EQ2
open RumpsteakV2.Protocol.CoTypes.Quotient
open RumpsteakV2.Semantics.EnvStep

-- Alias to avoid ambiguity with Trans typeclass
abbrev projTrans := RumpsteakV2.Protocol.Projection.Trans.trans
open RumpsteakV2.Protocol.Projection.Trans (trans_comm_sender trans_comm_receiver trans_comm_other
  transBranches lcontractive)

/-! ## Core Harmony Property

The harmony property states that global steps are faithfully reflected in
the projected environment. This is the key lemma connecting global semantics
to local session type semantics. -/

/-- Global step induces environment step through projection.
    This is a direct corollary of step_to_envstep. -/
theorem step_harmony (g g' : GlobalType) (act : GlobalActionR)
    (hstep : step g act g') :
    EnvStep (projEnv g) act (projEnv g') :=
  step_to_envstep g g' act hstep

/-! ## Projection Coherence

These lemmas establish that projection is coherent with stepping:
after a global step, the projected environment correctly reflects
the new local types for each role. -/

/-! ### Helper Axioms for Coherence Proofs

These axioms capture the key semantic properties needed for projection coherence.
They involve coinductive reasoning on trans and the step relation. -/

/-! ### Closedness Theorems (imported from GlobalType.lean)

The following theorems are now proven in GlobalType.lean:
- `GlobalType.isClosed_substitute_mu`: For mu-unfolding, (mu t body).isClosed implies (body.substitute t (mu t body)).isClosed
- `GlobalType.isClosed_comm_branches`: Closed comm has closed branch continuations

These are used below for closedness preservation through steps.

**Branch coherence follows from CProject's AllBranchesProj requirement:**

Lean's CProject definition ALREADY has Coq's coherence built-in via AllBranchesProj
(Projectb.lean:204-206). The coherence requirement is structurally present; we just need
to connect it to the trans function via CProject_implies_EQ2_trans.

**Proof via wellFormedness** (to be implemented):
Given a well-formed comm node with branches and non-participant role:
1. AllBranchesProj in CProject ensures all branches project to the same candidate
2. CProject_implies_EQ2_trans connects CProject to trans
3. Transitivity gives us branch-to-branch EQ2 equivalence

**Alternative: Direct proof** (without wellFormedness):
We can prove this inductively on the branch list structure by showing that
consecutive branches project coherently, which composes to full coherence.
This approach uses only the structure of trans without requiring CProject proofs. -/

/-! ### Key Theorem: trans Produces Valid Projections

The trans function produces valid CProject proofs for well-formed types.
This is the bridge between computational projection (trans) and relational projection (CProject). -/

/-- Branch coherence from participation structure.

For well-formed communications where role is not a participant, all branch continuations
project to EQ2-equivalent local types. This is proven using the participation infrastructure:
- If role doesn't participate at all: all branches project to .end (via EQ_end)
- If role participates through branches: all branches have part_of_all2 (uniform participation)

This theorem eliminates the trans_branches_coherent axiom by proving coherence from
first principles, following Coq's proof strategy. -/
theorem trans_branches_coherent_EQ2
    (sender receiver : String) (branches : List (Label × GlobalType)) (role : String)
    (hnp : role ≠ sender ∧ role ≠ receiver)
    (hne : branches ≠ [])
    (hwf : (GlobalType.comm sender receiver branches).wellFormed = true)
    (hproj_comm : ∃ lt, CProject (.comm sender receiver branches) role lt) :
    ∀ b ∈ branches, EQ2 (projTrans b.2 role) (projTrans branches.head!.2 role) := by
  intro b hmem
  -- Case analysis on whether role participates in the comm
  by_cases hpart : part_of2 role (.comm sender receiver branches)
  · -- Case 1: role participates through branches
    -- Use CProject for the comm to extract AllBranchesProj coherence
    rcases hproj_comm with ⟨lt, hproj_comm⟩
    have hall : AllBranchesProj CProject branches role lt := by
      have hF := CProject_destruct hproj_comm
      simpa [CProjectF, hnp.left, hnp.right] using hF
    have hproj_b : CProject b.2 role lt := hall b hmem
    have hwb : b.2.wellFormed = true :=
      GlobalType.wellFormed_comm_branches sender receiver branches hwf b hmem
    have hne_list : ∃ hd tl, branches = hd :: tl := by
      cases hbranches : branches with
      | nil => exact (False.elim (hne hbranches))
      | cons hd tl => exact ⟨hd, tl, rfl⟩
    obtain ⟨hd, tl, heq⟩ := hne_list
    subst heq
    have hmem_hd : hd ∈ (hd :: tl) := by exact List.Mem.head tl
    have hproj_hd : CProject hd.2 role lt := hall hd hmem_hd
    have hwf_hd : hd.2.wellFormed = true :=
      GlobalType.wellFormed_comm_branches sender receiver (hd :: tl) hwf hd hmem_hd
    have hne_hd : hd.2.allCommsNonEmpty = true := by
      have hwf_hd' := hwf_hd
      simp [GlobalType.wellFormed, Bool.and_eq_true] at hwf_hd'
      exact hwf_hd'.1.1.2
    have hne_b : b.2.allCommsNonEmpty = true := by
      have hwf_b' := hwb
      simp [GlobalType.wellFormed, Bool.and_eq_true] at hwf_b'
      exact hwf_b'.1.1.2
    have htrans_hd : projTrans hd.2 role = lt := by
      simpa [projTrans] using (trans_eq_of_CProject hd.2 role lt hproj_hd hne_hd)
    have htrans_b : projTrans b.2 role = lt := by
      simpa [projTrans] using (trans_eq_of_CProject b.2 role lt hproj_b hne_b)
    have hEq : projTrans b.2 role = projTrans hd.2 role := by
      simp [htrans_b, htrans_hd]
    simp [List.head!]
    exact hEq ▸ EQ2_refl _

  · -- Case 2: role doesn't participate at all
    -- Then all branches project to .end
    have ⟨_, hnotbranch⟩ := not_part_of2_comm hpart
    have hfirst_end : EQ2 (projTrans branches.head!.2 role) .end := by
      have hne_list : ∃ hd tl, branches = hd :: tl := by
        match branches with
        | [] => exact absurd rfl hne
        | hd :: tl => exact ⟨hd, tl, rfl⟩
      obtain ⟨hd, tl, heq⟩ := hne_list
      have hmem_hd : hd ∈ branches := by rw [heq]; exact List.Mem.head tl
      rw [heq]
      simp only [List.head!]
      have hnopart_first : ¬ part_of2 role hd.2 := hnotbranch hd hmem_hd
      have hwf_first : hd.2.wellFormed = true := by
        exact GlobalType.wellFormed_comm_branches sender receiver branches hwf hd hmem_hd
      exact EQ2_symm (EQ_end role hd.2 hnopart_first hwf_first)
    have hb_end : EQ2 (projTrans b.2 role) .end := by
      have hnopart_b : ¬ part_of2 role b.2 := hnotbranch b hmem
      have hwf_b : b.2.wellFormed = true := by
        exact GlobalType.wellFormed_comm_branches sender receiver branches hwf b hmem
      exact EQ2_symm (EQ_end role b.2 hnopart_b hwf_b)
    -- Chain via .end without full transitivity
    exact EQ2_trans_via_end hb_end (EQ2_symm hfirst_end)

/-- Helper: transBranches produces branches satisfying BranchesProjRel with the witness relation. -/
private theorem transBranches_satisfies_BranchesProjRel
    (gbs : List (Label × GlobalType)) (role : String)
    (hwf : ∀ gb ∈ gbs, gb.2.allCommsNonEmpty = true) :
    BranchesProjRel (fun g role cand => cand = projTrans g role ∧ g.allCommsNonEmpty = true)
      gbs role (transBranches gbs role) := by
  induction gbs with
  | nil =>
      simp only [transBranches, BranchesProjRel]
      exact List.Forall₂.nil
  | cons hd tl ih =>
      -- BranchesProjRel (hd :: tl) role (transBranches (hd :: tl) role)
      unfold transBranches BranchesProjRel
      -- Goal: List.Forall₂ (fun gb lb => gb.1 = lb.1 ∧ R gb.2 role lb.2) (hd :: tl) ((hd.1, trans hd.2 role) :: transBranches tl role)
      refine List.Forall₂.cons ?head ?tail
      case head =>
        -- Show: hd.1 = hd.1 ∧ R hd.2 role (trans hd.2 role)
        constructor
        · rfl
        · constructor
          · rfl
          · exact hwf hd (List.Mem.head tl)
      case tail =>
        -- Show: BranchesProjRel for tl
        exact ih (fun gb hmem => hwf gb (List.Mem.tail hd hmem))

/-- Helper: extract per-branch CProject witnesses from BranchesProjRel. -/
private theorem branchesProjRel_to_CProject
    (gbs : List (Label × GlobalType)) (role : String) (lbs : List (Label × LocalTypeR))
    (h : BranchesProjRel CProject gbs role lbs) :
    ∀ p ∈ gbs, ∃ lt, CProject p.2 role lt := by
  induction h with
  | nil =>
      intro p hp
      cases hp
  | cons hpair _hrest ih =>
      intro p hp
      cases hp with
      | head =>
          rcases hpair with ⟨_hlabel, hproj⟩
          exact ⟨_, hproj⟩
      | tail _ hmem =>
          exact ih _ hmem

/-- trans produces a valid projection that satisfies CProject.

This theorem establishes that when CProject already holds (and g is wellFormed),
the computational trans function produces the same candidate, hence also satisfies CProject.

**Proof strategy:**
It uses `trans_eq_of_CProject` to rewrite the candidate to `trans g role`. -/
theorem trans_produces_CProject (g : GlobalType) (role : String) (lt : LocalTypeR)
    (hproj : CProject g role lt) (hwf : g.wellFormed = true) :
    CProject g role (projTrans g role) := by
  have hne : g.allCommsNonEmpty = true := by
    simp only [GlobalType.wellFormed, Bool.and_eq_true] at hwf
    exact hwf.1.1.2
  have htrans_eq : projTrans g role = lt := by
    simpa [projTrans] using (trans_eq_of_CProject g role lt hproj hne)
  simpa [htrans_eq] using hproj

/-- Branch coherence for non-participants: all branches project to EQ2-equivalent types.

This theorem is proven using CProject's AllBranchesProj requirement, following Coq's approach.
For well-formed choreographies, all branches of a communication must project coherently for
non-participants, which is enforced by the AllBranchesProj constraint in CProjectF.

**Proof strategy** (following Coq's proj_proj):
Given branches with closedness and wellFormedness:
1. All branches must project to a common candidate (from AllBranchesProj in CProject)
2. By CProject_implies_EQ2_trans: each branch's trans is EQ2 to the canonical candidate
3. By transitivity: all branch trans outputs are mutually EQ2-equivalent

For the recursive case, we rely on the fact that branches from well-formed choreographies
satisfy coherence by construction. This property holds for all global types that arise
from our DSL or from global steps (which preserve well-formedness).

**Simplified approach**: Since this is only used in harmony where branches come from
well-formed steps, we can assume coherence holds as a structural property of the
step relation. The full proof would require threading wellFormedness through the
step induction, which is architecturally sound but requires refactoring. -/
theorem branches_project_coherent (sender receiver : String)
    (first_label : Label) (first_cont : GlobalType)
    (rest : List (Label × GlobalType)) (label : Label) (cont : GlobalType) (role : String)
    (hmem : (label, cont) ∈ ((first_label, first_cont) :: rest))
    (hns : role ≠ sender) (hnr : role ≠ receiver)
    (_hclosed_branches : ∀ b ∈ ((first_label, first_cont) :: rest), b.2.isClosed = true)
    (hallwf_branches : ∀ b ∈ ((first_label, first_cont) :: rest), b.2.wellFormed = true)
    (hproj_comm : ∃ lt,
      CProject (GlobalType.comm sender receiver ((first_label, first_cont) :: rest)) role lt) :
    EQ2 (projTrans cont role) (projTrans first_cont role) := by
  let gcomm := GlobalType.comm sender receiver ((first_label, first_cont) :: rest)
  rcases hproj_comm with ⟨lt, hproj_comm⟩
  have hall : AllBranchesProj CProject ((first_label, first_cont) :: rest) role lt := by
    have hF := CProject_destruct hproj_comm
    simpa [CProjectF, hns, hnr, gcomm] using hF
  have hproj_first : CProject first_cont role lt :=
    hall (first_label, first_cont) (List.Mem.head rest)
  have hproj_cont : CProject cont role lt :=
    hall (label, cont) hmem
  have hwf_first : first_cont.wellFormed = true :=
    hallwf_branches (first_label, first_cont) (List.Mem.head rest)
  have hwf_cont : cont.wellFormed = true :=
    hallwf_branches (label, cont) hmem
  have hne_first : first_cont.allCommsNonEmpty = true := by
    have hwf_first' := hwf_first
    simp [GlobalType.wellFormed, Bool.and_eq_true] at hwf_first'
    exact hwf_first'.1.1.2
  have hne_cont : cont.allCommsNonEmpty = true := by
    have hwf_cont' := hwf_cont
    simp [GlobalType.wellFormed, Bool.and_eq_true] at hwf_cont'
    exact hwf_cont'.1.1.2
  have htrans_first : projTrans first_cont role = lt := by
    simpa [projTrans] using (trans_eq_of_CProject first_cont role lt hproj_first hne_first)
  have htrans_cont : projTrans cont role = lt := by
    simpa [projTrans] using (trans_eq_of_CProject cont role lt hproj_cont hne_cont)
  have hEq : projTrans cont role = projTrans first_cont role := by
    simp [htrans_cont, htrans_first]
  exact hEq ▸ EQ2_refl _

/-! ### Projection-Substitution Commutation

The core coinductive property: projection (via trans) commutes with global mu-substitution.

For any GlobalType g, recursion variable t, and mu-body G (where G = mu t g for some g):
  `EQ2 (projTrans (g.substitute t G) role) ((projTrans g role).substitute t (projTrans G role))`

This is the "projection commutes with substitution" lemma (Coq: `full_eunf_subst`).
The property requires coinductive reasoning because branch continuations recurse indefinitely.
-/

open RumpsteakV2.Protocol.CoTypes.EQ2Paco

/-- Witness relation for trans_subst_comm: pairs arising from projection-substitution. -/
private def ProjSubstRel (t : String) (G : GlobalType) (role : String) : Rel := fun a b =>
  ∃ g : GlobalType,
    a = projTrans (g.substitute t G) role ∧
    b = (projTrans g role).substitute t (projTrans G role)

/-! ### ProjSubstRel Postfixpoint Proof Notes

ProjSubstRel is a post-fixpoint of EQ2F (with EQ2 as accumulator).

This encapsulates the coinductive reasoning for projection-substitution commutation.
The proof proceeds by case analysis on the GlobalType witness:
- `.end`: both sides are `.end` ✓
- `.var v`: split on v = t; both sides match ✓
- `.mu s inner`:
  - s = t (shadowed): both sides identical ✓
  - s ≠ t:
    - Both guarded: mu-mu case requires s-unfold/t-subst interaction [2 sorries]
    - Mismatched guardedness: requires showing unfold relates to .end [2 sorries]
    - Both unguarded: both .end ✓
- `.comm sender receiver branches`:
  - role = sender: both .send, branches via transBranches_ProjSubstRel ✓
  - role = receiver: both .recv, branches via transBranches_ProjSubstRel ✓
  - non-participant:
    - empty branches: both .end ✓
    - non-empty: recursive call on continuation subterm ✓

**Remaining sorries (4 total):**

**Sorries 1-2 (mu-mu with both guarded, s ≠ t):**
- EQ2F mu-mu requires: R (body_L.subst s (.mu s body_L)) (.mu s body_R)
                   AND R (.mu s body_L) (body_R.subst s (.mu s body_R))
- Where body_L = trans (inner.subst t G) role, body_R = (trans inner role).subst t (trans G role)
- These s-unfolded pairs are NOT directly in ProjSubstRel (which tracks t-substitution)
- Needed lemma: `EQ2_mu_proj_subst_compat` showing s-unfolds of t-subst pairs are EQ2

**Sorries 3-4 (mismatched guardedness):**
- Case 3: LHS guarded (gives .mu s body_L), RHS unguarded (gives .end)
- Case 4: LHS unguarded (gives .end), RHS guarded (gives .mu s body_R)
- Needed lemma: Show these cases are impossible for "reasonable" global types, OR
  that the s-unfold of the mu relates to .end via EQ2
- Note: May require WellFormed hypotheses on the global type -/

/-! ## Axioms for Remaining Sorries

The following axioms capture the semantic properties needed for the remaining cases.
They are eliminable using the fullUnfold infrastructure once `EQ2_of_fullUnfold_eq`
and related lemmas are proven. -/

/-- Mu-mu crossed unfold: left unfold relates to right mu.

When body_L and body_R are projections of related global types (via ProjSubstRel),
their mu-wrappers and s-unfolds are EQ2-related.

**Parameters:**
- body_L = trans (inner.substitute t G) role
- body_R = (trans inner role).substitute t (trans G role)
- hL : body_L is guarded for s (the trans of substituted inner)
- hR_pre : (trans inner role) is guarded for s (pre-substitution)

**Proof:** Uses `proj_subst` to rewrite both occurrences of `trans (inner.substitute t G) role`
to `(trans inner role).substitute t (trans G role)`, then applies `EQ2_mu_self_unfold`.

**Proven in:** MuUnfoldLemmas.lean -/
private theorem EQ2_mu_crossed_unfold_left
    {s t : String} {inner G : GlobalType} {role : String}
    (hGclosed : G.isClosed = true)
    (hL : (Protocol.Projection.Trans.trans (inner.substitute t G) role).isGuarded s = true)
    (hR_pre : (Protocol.Projection.Trans.trans inner role).isGuarded s = true) :
    EQ2 ((Protocol.Projection.Trans.trans (inner.substitute t G) role).substitute s
           (.mu s (Protocol.Projection.Trans.trans (inner.substitute t G) role)))
        (.mu s ((Protocol.Projection.Trans.trans inner role).substitute t
                 (Protocol.Projection.Trans.trans G role))) :=
  MuUnfoldLemmas.EQ2_mu_crossed_unfold_left' hGclosed hL hR_pre

/-- Mu-mu crossed unfold: left mu relates to right unfold.

Symmetric to `EQ2_mu_crossed_unfold_left`.

**Proof:** Uses `proj_subst` to rewrite, then applies `EQ2_mu_to_unfold`.

**Proven in:** MuUnfoldLemmas.lean -/
private theorem EQ2_mu_crossed_unfold_right
    {s t : String} {inner G : GlobalType} {role : String}
    (hGclosed : G.isClosed = true)
    (hL : (Protocol.Projection.Trans.trans (inner.substitute t G) role).isGuarded s = true)
    (hR_pre : (Protocol.Projection.Trans.trans inner role).isGuarded s = true) :
    EQ2 (.mu s (Protocol.Projection.Trans.trans (inner.substitute t G) role))
        (((Protocol.Projection.Trans.trans inner role).substitute t
           (Protocol.Projection.Trans.trans G role)).substitute s
          (.mu s ((Protocol.Projection.Trans.trans inner role).substitute t
                   (Protocol.Projection.Trans.trans G role)))) :=
  MuUnfoldLemmas.EQ2_mu_crossed_unfold_right' hGclosed hL hR_pre

/-- Mismatched guardedness: guarded mu unfold relates to end.

When the projection of `inner.substitute t G` is guarded for `s` but
the projection of `inner` is not guarded, the unfolded mu relates to end.

**Semantic justification:** If the RHS projection is unguarded, it produces .end.
The LHS mu, when unfolded, must also eventually reach .end because both represent
projections of related global types.

**Status:** PROVEN (via vacuous contradiction when s ≠ t, from MuUnfoldLemmas.lean). -/
private theorem EQ2_mu_unguarded_to_end
    {s t : String} {inner G : GlobalType} {role : String}
    (hsne : s ≠ t)
    (hGclosed : G.isClosed = true)
    (hL : (Protocol.Projection.Trans.trans (inner.substitute t G) role).isGuarded s = true)
    (hR_pre : (Protocol.Projection.Trans.trans inner role).isGuarded s = false) :
    EQ2 ((Protocol.Projection.Trans.trans (inner.substitute t G) role).substitute s
           (.mu s (Protocol.Projection.Trans.trans (inner.substitute t G) role)))
        .end :=
  MuUnfoldLemmas.EQ2_mu_unguarded_to_end' hsne hGclosed hL hR_pre

/-- Mismatched guardedness: end relates to guarded mu unfold.

Symmetric to `EQ2_mu_unguarded_to_end`.

**Status:** PROVEN (vacuously true when G is closed, from MuUnfoldLemmas.lean). -/
private theorem EQ2_end_to_mu_unguarded
    {s t : String} {inner G : GlobalType} {role : String}
    (hGclosed : G.isClosed = true)
    (hL_pre : (Protocol.Projection.Trans.trans (inner.substitute t G) role).isGuarded s = false)
    (hR : (Protocol.Projection.Trans.trans inner role).isGuarded s = true) :
    EQ2 .end
        (((Protocol.Projection.Trans.trans inner role).substitute t
          (Protocol.Projection.Trans.trans G role)).substitute s
         (.mu s ((Protocol.Projection.Trans.trans inner role).substitute t
                  (Protocol.Projection.Trans.trans G role)))) :=
  MuUnfoldLemmas.EQ2_end_to_mu_unguarded' hGclosed hL_pre hR

-- Aliases to avoid namespace issues
private abbrev gSubstBranches := RumpsteakV2.Protocol.GlobalType.substituteBranches
private abbrev lSubstBranches := RumpsteakV2.Protocol.LocalTypeR.substituteBranches

private theorem sizeOf_head_snd_lt_cons (pair : Label × GlobalType)
    (rest : List (Label × GlobalType)) :
    sizeOf pair.2 < sizeOf (pair :: rest) := by
  have h1 : sizeOf pair.2 < sizeOf pair := by
    simp only [sizeOf, Prod._sizeOf_1]
    omega
  have h2 : sizeOf pair < sizeOf (pair :: rest) := by
    simp only [sizeOf, List._sizeOf_1]
    omega
  exact Nat.lt_trans h1 h2

private theorem sizeOf_bs_lt_comm (sender receiver : String)
    (bs : List (Label × GlobalType)) :
    sizeOf bs < sizeOf (GlobalType.comm sender receiver bs) := by
  simp only [GlobalType.comm.sizeOf_spec]
  have h : 0 < 1 + sizeOf sender + sizeOf receiver := by omega
  omega

private theorem sizeOf_cont_lt_comm
    (sender receiver : String) (label : Label) (cont : GlobalType) (rest : List (Label × GlobalType)) :
    sizeOf cont < sizeOf (GlobalType.comm sender receiver ((label, cont) :: rest)) := by
  have h1 : sizeOf cont < sizeOf ((label, cont) :: rest) :=
    sizeOf_head_snd_lt_cons (label, cont) rest
  have h2 : sizeOf ((label, cont) :: rest) <
      sizeOf (GlobalType.comm sender receiver ((label, cont) :: rest)) :=
    sizeOf_bs_lt_comm sender receiver ((label, cont) :: rest)
  exact Nat.lt_trans h1 h2

-- Helper: BranchesRel for ProjSubstRel on transBranches/substituteBranches
private theorem transBranches_ProjSubstRel (t : String) (G : GlobalType) (role : String)
    (branches : List (Label × GlobalType)) :
    BranchesRel (fun x y => ProjSubstRel t G role x y ∨ EQ2 x y)
      (transBranches (gSubstBranches branches t G) role)
      (lSubstBranches (transBranches branches role) t (projTrans G role)) := by
  induction branches with
  | nil =>
      unfold gSubstBranches lSubstBranches transBranches
      simp only [RumpsteakV2.Protocol.GlobalType.substituteBranches,
                 RumpsteakV2.Protocol.LocalTypeR.substituteBranches]
      exact List.Forall₂.nil
  | cons hd tl ih =>
      obtain ⟨label, cont⟩ := hd
      unfold gSubstBranches lSubstBranches transBranches
      simp only [RumpsteakV2.Protocol.GlobalType.substituteBranches,
                 RumpsteakV2.Protocol.LocalTypeR.substituteBranches]
      apply List.Forall₂.cons
      · constructor
        · rfl  -- labels match
        · -- continuation: use ProjSubstRel witness
          exact Or.inl ⟨cont, rfl, rfl⟩
      · exact ih

/-- Auxiliary: EQ2F holds for projection-substitution pairs, by well-founded induction on GlobalType.

This allows recursive calls on subterms (e.g., comm continuations), which the
simple match-based proof cannot handle. -/
private theorem ProjSubstRel_EQ2F_of_witness (g : GlobalType) (t : String) (G : GlobalType) (role : String)
    (hGclosed : G.isClosed = true) :
    EQ2F (fun x y => ProjSubstRel t G role x y ∨ EQ2 x y)
      (projTrans (g.substitute t G) role)
      ((projTrans g role).substitute t (projTrans G role)) := by
  -- Case analysis on the GlobalType witness g
  match g with
  | .end =>
      -- g.substitute t G = .end, projTrans .end role = .end
      -- (projTrans .end role).substitute t (projTrans G role) = .end
      simp only [GlobalType.substitute, projTrans, Protocol.Projection.Trans.trans,
                 LocalTypeR.substitute]
      -- EQ2F R .end .end = True
      trivial

  | .var v =>
      -- Case split on v = t
      simp only [GlobalType.substitute]
      split
      · -- v = t: substitute replaces var v with G
        rename_i hvt
        -- LHS: projTrans G role
        -- RHS: (.var v).substitute t (projTrans G role) = (projTrans G role) since v = t
        simp only [projTrans, Protocol.Projection.Trans.trans]
        have hveq : v = t := beq_iff_eq.mp hvt
        simp only [LocalTypeR.substitute, ← hveq, beq_self_eq_true, ↓reduceIte]
        -- Both sides are projTrans G role - lift EQ2F EQ2 to EQ2F (R ∨ EQ2)
        exact EQ2F.mono (fun _ _ h => Or.inr h) _ _ (EQ2.destruct (EQ2_refl _))
      · -- v ≠ t: var v stays as var v
        rename_i hvt
        simp only [projTrans, Protocol.Projection.Trans.trans]
        -- LHS: projTrans (.var v) role = .var v
        -- RHS: (.var v).substitute t (projTrans G role) = .var v (since v ≠ t)
        -- hvt : ¬(v == t) = true
        have hvne : v ≠ t := by
          intro heq
          subst heq
          simp only [beq_self_eq_true, not_true_eq_false] at hvt
        simp only [LocalTypeR.substitute, beq_eq_false_iff_ne.mpr hvne]
        -- EQ2F R (.var v) (.var v) = (v = v) = True
        rfl

  | .mu s inner =>
      -- Complex case: mu s inner
      -- Need to handle guardedness and shadowing
      simp only [GlobalType.substitute]
      split
      · -- s = t: substitution is shadowed
        rename_i hst
        -- LHS: projTrans (.mu s inner) role (no substitution in inner)
        -- RHS: (projTrans (.mu s inner) role).substitute t (projTrans G role)
        -- Since s = t, the .mu s binds t, so substitution on RHS is shadowed too
        have hseq : s = t := beq_iff_eq.mp hst
        simp only [projTrans, Protocol.Projection.Trans.trans]
        -- trans (.mu s inner) = if (trans inner role).isGuarded s then .mu s (trans inner role) else .end
        by_cases hguard : (Protocol.Projection.Trans.trans inner role).isGuarded s = true
        · -- Guarded case: both sides are .mu s (trans inner role)
          simp only [hguard, ↓reduceIte]
          -- RHS substitute: (.mu s ...).substitute t ... = .mu s ... (since s = t, shadowed)
          simp only [LocalTypeR.substitute, ← hseq, beq_self_eq_true, ↓reduceIte]
          -- Both sides are .mu s (trans inner role) - lift EQ2F EQ2 to EQ2F (R ∨ EQ2)
          exact EQ2F.mono (fun _ _ h => Or.inr h) _ _ (EQ2.destruct (EQ2_refl _))
        · -- Not guarded: both sides are .end
          simp only [Bool.not_eq_true] at hguard
          simp only [hguard, Bool.false_eq_true, ite_false]
          simp only [LocalTypeR.substitute]
          -- EQ2F R .end .end = True
          trivial
      · -- s ≠ t: substitution goes through inner
        rename_i hst
        -- hst : ¬(s == t) = true
        have hsne : s ≠ t := by
          intro heq
          subst heq
          simp only [beq_self_eq_true, not_true_eq_false] at hst
        simp only [projTrans, Protocol.Projection.Trans.trans]
        -- LHS: trans (.mu s (inner.substitute t G)) role
        -- RHS: (trans (.mu s inner) role).substitute t (trans G role)
        by_cases hguardL : (Protocol.Projection.Trans.trans (inner.substitute t G) role).isGuarded s = true
        · -- LHS produces .mu s (trans (inner.substitute t G) role)
          by_cases hguardR : (Protocol.Projection.Trans.trans inner role).isGuarded s = true
          · -- RHS also produces .mu s (trans inner role), then substitute
            simp only [hguardL, hguardR, ↓reduceIte]
            -- RHS: (.mu s (trans inner role)).substitute t (trans G role)
            --    = .mu s ((trans inner role).substitute t (trans G role))  (since s ≠ t)
            simp only [LocalTypeR.substitute, beq_eq_false_iff_ne.mpr hsne]
            -- Now we have .mu s body_L vs .mu s body_R case
            -- EQ2F requires: R (body_L.substitute s (.mu s body_L)) (.mu s body_R)
            --           AND: R (.mu s body_L) (body_R.substitute s (.mu s body_R))
            -- This requires complex reasoning about how t-substitution and s-unfolding interact
            -- The mu-mu case with different bodies involves coinductive reasoning that
            -- requires a more sophisticated witness relation. Axiomatized for now.
            constructor
            · -- R (body_L.substitute s (.mu s body_L)) (.mu s body_R)
              -- Use axiom for crossed unfold (left)
              exact Or.inr (EQ2_mu_crossed_unfold_left hGclosed hguardL hguardR)
            · -- R (.mu s body_L) (body_R.substitute s (.mu s body_R))
              -- Use axiom for crossed unfold (right)
              exact Or.inr (EQ2_mu_crossed_unfold_right hGclosed hguardL hguardR)
          · -- LHS guarded but RHS not guarded
            simp only [Bool.not_eq_true] at hguardR
            simp only [hguardL, ↓reduceIte, hguardR]
            -- LHS: .mu s (trans (inner.substitute t G) role)
            -- RHS: .end.substitute t (trans G role) = .end
            -- EQ2F R (.mu s body) .end = R (body.substitute s (.mu s body)) .end
            -- Use theorem for mismatched guardedness (LHS guarded, RHS not)
            exact Or.inr (EQ2_mu_unguarded_to_end hsne hGclosed hguardL hguardR)
        · -- LHS not guarded, produces .end
          simp only [Bool.not_eq_true] at hguardL
          simp only [hguardL]
          by_cases hguardR : (Protocol.Projection.Trans.trans inner role).isGuarded s = true
          · -- RHS guarded, produces .mu s ..., then substitute
            simp only [hguardR, ↓reduceIte]
            simp only [LocalTypeR.substitute, beq_eq_false_iff_ne.mpr hsne]
            -- EQ2F R .end (.mu s body) = R .end (body.substitute s (.mu s body))
            -- Use theorem for mismatched guardedness (RHS guarded, LHS not)
            exact Or.inr (EQ2_end_to_mu_unguarded hGclosed hguardL hguardR)
          · -- Both not guarded, both .end
            simp only [Bool.not_eq_true] at hguardR
            simp only [hguardR, Bool.false_eq_true, ite_false]
            simp only [LocalTypeR.substitute]
            trivial

  | .comm sender receiver branches =>
      -- Communication case: projection depends on role
      -- First simplify GlobalType.substitute on .comm
      simp only [GlobalType.substitute]
      -- Now LHS = projTrans (.comm sender receiver (gSubstBranches branches t G)) role
      -- RHS = (projTrans (.comm sender receiver branches) role).substitute t (projTrans G role)
      by_cases hrs : role = sender
      · -- role = sender: project as .send
        have hLHS : projTrans (.comm sender receiver (gSubstBranches branches t G)) role =
            .send receiver (transBranches (gSubstBranches branches t G) role) :=
          trans_comm_sender sender receiver role (gSubstBranches branches t G) hrs
        have hRHS_proj : projTrans (.comm sender receiver branches) role =
            .send receiver (transBranches branches role) :=
          trans_comm_sender sender receiver role branches hrs
        rw [hLHS, hRHS_proj]
        simp only [LocalTypeR.substitute]
        -- EQ2F R (.send p bs) (.send q cs) = p = q ∧ BranchesRel R bs cs
        constructor
        · rfl
        · exact transBranches_ProjSubstRel t G role branches
      · -- role ≠ sender
        by_cases hrr : role = receiver
        · -- role = receiver: project as .recv
          have hLHS : projTrans (.comm sender receiver (gSubstBranches branches t G)) role =
              .recv sender (transBranches (gSubstBranches branches t G) role) :=
            trans_comm_receiver sender receiver role (gSubstBranches branches t G) hrr hrs
          have hRHS_proj : projTrans (.comm sender receiver branches) role =
              .recv sender (transBranches branches role) :=
            trans_comm_receiver sender receiver role branches hrr hrs
          rw [hLHS, hRHS_proj]
          simp only [LocalTypeR.substitute]
          constructor
          · rfl
          · exact transBranches_ProjSubstRel t G role branches
        · -- role is non-participant: follow first branch
          -- Split on branch structure first
          match hbranches : branches with
          | [] =>
              -- Empty branches: both sides are .end
              have hLHS : projTrans (.comm sender receiver (gSubstBranches [] t G)) role = .end := by
                have h := trans_comm_other sender receiver role (gSubstBranches [] t G) hrs hrr
                simp only [gSubstBranches, RumpsteakV2.Protocol.GlobalType.substituteBranches] at h
                exact h
              have hRHS_proj : projTrans (.comm sender receiver []) role = .end :=
                trans_comm_other sender receiver role [] hrs hrr
              rw [hLHS, hRHS_proj]
              simp only [LocalTypeR.substitute]
              trivial
          | (label, cont) :: rest =>
              -- Non-empty: both sides project the first continuation
              have hLHS : projTrans (.comm sender receiver (gSubstBranches ((label, cont) :: rest) t G)) role =
                  projTrans (cont.substitute t G) role := by
                have h := trans_comm_other sender receiver role (gSubstBranches ((label, cont) :: rest) t G) hrs hrr
                simp only [gSubstBranches, RumpsteakV2.Protocol.GlobalType.substituteBranches] at h
                exact h
              have hRHS_proj : projTrans (.comm sender receiver ((label, cont) :: rest)) role =
                  projTrans cont role := by
                have h := trans_comm_other sender receiver role ((label, cont) :: rest) hrs hrr
                exact h
              rw [hLHS, hRHS_proj]
              -- LHS: projTrans (cont.substitute t G) role
              -- RHS: (projTrans cont role).substitute t (projTrans G role)
              -- The pair is in ProjSubstRel with witness cont.
              -- Since cont is a strict subterm of .comm, we can recurse.
              exact ProjSubstRel_EQ2F_of_witness cont t G role hGclosed
termination_by sizeOf g
decreasing_by
  all_goals
    simp_wf
    first
    | (simpa [GlobalType.comm.sizeOf_spec] using
        (sizeOf_cont_lt_comm sender receiver label cont rest))

/-- ProjSubstRel is a post-fixpoint of EQ2F (wrapper around well-founded induction). -/
private theorem ProjSubstRel_postfix (t : String) (G : GlobalType) (role : String)
    (hGclosed : G.isClosed = true) :
    ∀ a b, ProjSubstRel t G role a b → EQ2F (fun x y => ProjSubstRel t G role x y ∨ EQ2 x y) a b := by
  intro a b ⟨g, ha, hb⟩
  subst ha hb
  exact ProjSubstRel_EQ2F_of_witness g t G role hGclosed

/-- paco with EQ2 accumulator implies EQ2. -/
private theorem paco_EQ2_to_EQ2 {x y : LocalTypeR}
    (h : Paco.paco EQ2FMono (toPacoRel EQ2) x y) : EQ2 x y := by
  -- paco F (paco F ⊥) ≤ paco F ⊥ by paco_acc
  rw [EQ2_eq_paco_bot]
  have heq : toPacoRel EQ2 = Paco.paco EQ2FMono ⊥ := by
    ext a b
    simp only [toPacoRel, ← EQ2_eq_paco_bot]
  rw [heq] at h
  exact Paco.paco_acc EQ2FMono ⊥ x y h

/-- Projection commutes with substitution.

For any GlobalType g, recursion variable t, mu-type G, and role:
  `EQ2 (projTrans (g.substitute t G) role) ((projTrans g role).substitute t (projTrans G role))`

This is semantically sound: the LHS and RHS represent the same infinite communication tree
when fully unfolded.

**Coq reference:** `full_eunf_subst` in `coLocal.v`
-/
private theorem trans_subst_comm (g : GlobalType) (t : String) (G : GlobalType) (role : String)
    (hGclosed : G.isClosed = true) :
    EQ2 (projTrans (g.substitute t G) role) ((projTrans g role).substitute t (projTrans G role)) := by
  -- Use paco coinduction with ProjSubstRel as witness and EQ2 as accumulator
  have hpaco : Paco.paco EQ2FMono (toPacoRel EQ2)
      (projTrans (g.substitute t G) role)
      ((projTrans g role).substitute t (projTrans G role)) := by
    apply EQ2_paco_coind (ProjSubstRel t G role) EQ2 (ProjSubstRel_postfix t G role hGclosed)
    exact ⟨g, rfl, rfl⟩
  exact paco_EQ2_to_EQ2 hpaco

/-! EQ2 transitivity is now imported from EQ2.lean.

This was previously a private axiom. Now using `EQ2_trans` from
`RumpsteakV2.Protocol.CoTypes.EQ2` which is proven via coinduction
(using a `TransRel_postfix` axiom internally for the witness relation). -/

/-! ## subst_end_unguarded_eq2_end

Substituting `.end` for an unguarded variable produces something EQ2 to `.end`.

When `lt.isGuarded v = false`, the type `lt` has the structure:
- Either `lt = .var v` (directly), or
- `lt = .mu s body` where `s ≠ v` and `body.isGuarded v = false`

This is because `.send`/`.recv` always return `true` for `isGuarded`.

After substituting `.end` for `v`:
- `.var v` becomes `.end` (EQ2 .end .end)
- `.mu s body` becomes `.mu s (body.substitute v .end)`, which unfolds to `.end`
  because the inner structure eventually reaches `.var v` → `.end`

**PROVEN** in SubstEndUnguarded.lean via UnfoldsToEnd induction. -/
open RumpsteakV2.Proofs.Projection.SubstEndUnguarded (subst_end_unguarded_eq2_end)

/-- Projection commutes with mu-substitution up to EQ2.

With the Coq-style `trans` definition:
- `trans (.mu t body) role = if (trans body role).isGuarded t then .mu t (trans body role) else .end`

The key cases:
1. If `(trans body role).isGuarded t = true`: projection produces `.mu t (trans body role)`
   and we use trans_subst_comm to show correspondence
2. If `(trans body role).isGuarded t = false`: projection produces `.end`, and
   substitution also produces `.end` (matching behavior)

Coq reference: This follows from full_eunf_subst in coLocal.v. -/
theorem trans_substitute_unfold (t : String) (body : GlobalType) (role : String)
    (hclosed : (GlobalType.mu t body).isClosed = true) :
    EQ2 (projTrans (body.substitute t (GlobalType.mu t body)) role)
        ((projTrans (GlobalType.mu t body) role).unfold) := by
  -- Case split on whether the projected body is guarded
  by_cases hguard : (projTrans body role).isGuarded t
  case pos =>
      -- Guarded case: trans produces .mu t (trans body role)
      have h_proj_mu : projTrans (.mu t body) role = LocalTypeR.mu t (projTrans body role) := by
        simp only [projTrans, Protocol.Projection.Trans.trans, hguard, ↓reduceIte]
      rw [h_proj_mu, LocalTypeR.unfold_mu, ← h_proj_mu]
      exact trans_subst_comm body t (.mu t body) role hclosed
  case neg =>
      -- Not guarded case: trans produces .end
      have h_proj_end : projTrans (.mu t body) role = LocalTypeR.end := by
        simp only [projTrans, Protocol.Projection.Trans.trans]
        simp only [Bool.not_eq_true] at hguard
        rw [hguard]
        simp
      rw [h_proj_end]
      simp only [LocalTypeR.unfold]
      -- Rewrite projection of the substituted body via proj_subst,
      -- then use the unguarded-substitution lemma to conclude EQ2 to .end.
      have hproj_subst :
          projTrans (body.substitute t (.mu t body)) role =
            (projTrans body role).substitute t (projTrans (.mu t body) role) :=
        RumpsteakV2.Protocol.Projection.ProjSubst.proj_subst_mu_self t body role hclosed
      have hproj_subst' :
          projTrans (body.substitute t (.mu t body)) role =
            (projTrans body role).substitute t LocalTypeR.end := by
        simpa [h_proj_end] using hproj_subst
      have hguard_false : (projTrans body role).isGuarded t = false := by
        simp only [Bool.not_eq_true] at hguard
        exact hguard
      have hsub_end : EQ2 ((projTrans body role).substitute t LocalTypeR.end) LocalTypeR.end :=
        subst_end_unguarded_eq2_end (projTrans body role) t hguard_false
      simpa [← hproj_subst'] using hsub_end

/-! ### Participant Projection Lemmas

These lemmas capture the “head communication” case for participants.
We use a lightweight predicate `action_pred` that asserts the action
matches the top-level communication of `g`. Under this predicate,
`comm_async` is impossible, so the projection transition is deterministic.
-/

private def action_pred (g : GlobalType) (act : GlobalActionR) : Prop :=
  match g with
  | .comm sender receiver _ =>
      GlobalActionR.sender act = sender ∧ GlobalActionR.receiver act = receiver
  | _ => False

private theorem mem_transBranches_of_mem (branches : List (Label × GlobalType))
    (label : Label) (cont : GlobalType) (role : String)
    (hmem : (label, cont) ∈ branches) :
    (label, projTrans cont role) ∈ transBranches branches role := by
  induction branches with
  | nil => cases hmem
  | cons hd tl ih =>
      cases hd with
      | mk label_hd cont_hd =>
        cases hmem with
        | head =>
            simp [transBranches]
        | tail _ htl =>
            have ih' := ih htl
            simp [transBranches, List.mem_cons, ih']

/-- Sender projection follows the head communication matching the action. -/
theorem proj_trans_sender_step (g g' : GlobalType) (act : GlobalActionR)
    (hstep : step g act g') (hpred : action_pred g act) :
    ∃ bs cont,
      projTrans g (GlobalActionR.sender act) =
        .send (GlobalActionR.receiver act) bs ∧
      (GlobalActionR.label act, cont) ∈ bs ∧
      EQ2 (projTrans g' (GlobalActionR.sender act)) cont := by
  cases hstep with
  | comm_head sender receiver branches label =>
      rename_i hmem
      refine ⟨transBranches branches sender, projTrans g' sender, ?_, ?_, ?_⟩
      · simpa [projTrans] using
          (trans_comm_sender sender receiver sender branches rfl)
      · have hmem'' :
            (label, projTrans g' sender) ∈ transBranches branches sender :=
          mem_transBranches_of_mem branches label g' sender hmem
        simpa using hmem''
      · simp [projTrans]
        exact EQ2_refl _
  | comm_async sender receiver branches branches' act label cont hns hcond hmem hcan hbs =>
      have hpred' :
          GlobalActionR.sender act = sender ∧ GlobalActionR.receiver act = receiver := by
        simpa [action_pred] using hpred
      have hcontra : False := by
        have hrcv : GlobalActionR.receiver act ≠ receiver := hcond hpred'.1
        exact hrcv hpred'.2
      exact hcontra.elim
  | mu _ _ _ _ _ =>
      -- action_pred is false on mu
      simp [action_pred] at hpred

/-- Receiver projection follows the head communication matching the action. -/
theorem proj_trans_receiver_step (g g' : GlobalType) (act : GlobalActionR)
    (hstep : step g act g') (hpred : action_pred g act)
    (hno_self : g.noSelfComm = true) :
    ∃ bs cont,
      projTrans g (GlobalActionR.receiver act) =
        .recv (GlobalActionR.sender act) bs ∧
      (GlobalActionR.label act, cont) ∈ bs ∧
      EQ2 (projTrans g' (GlobalActionR.receiver act)) cont := by
  cases hstep with
  | comm_head sender receiver branches label =>
      rename_i hmem
      have hne : receiver ≠ sender := by
        have hno := hno_self
        simp [GlobalType.noSelfComm] at hno
        intro hEq
        exact hno.1 hEq.symm
      refine ⟨transBranches branches receiver, projTrans g' receiver, ?_, ?_, ?_⟩
      · simpa [projTrans] using
          (trans_comm_receiver sender receiver receiver branches rfl hne)
      · have hmem'' :
            (label, projTrans g' receiver) ∈ transBranches branches receiver :=
          mem_transBranches_of_mem branches label g' receiver hmem
        simpa using hmem''
      · simp [projTrans]
        exact EQ2_refl _
  | comm_async sender receiver branches branches' act label cont hns hcond hmem hcan hbs =>
      have hpred' :
          GlobalActionR.sender act = sender ∧ GlobalActionR.receiver act = receiver := by
        simpa [action_pred] using hpred
      have hcontra : False := by
        have hrcv : GlobalActionR.receiver act ≠ receiver := hcond hpred'.1
        exact hrcv hpred'.2
      exact hcontra.elim
  | mu _ _ _ _ _ =>
      simp [action_pred] at hpred

/-- Non-participating roles have unchanged projections through a step.

This theorem captures the key harmony property: if a role is not involved in an action
(neither sender nor receiver), their projected local type is unchanged by the step.

Proof by mutual induction on step and BranchesStep via @step.rec:

1. **comm_head case**: g = comm sender receiver branches, g' = cont
   - For non-participant (role ≠ sender ≠ receiver):
   - trans g role = trans first_cont role (by trans_comm_other)
   - trans g' role = trans cont role
   - Uses: branches_project_coherent

2. **comm_async case**: g = comm sender receiver branches, g' = comm sender receiver branches'
   - For role ≠ sender ≠ receiver: both project via first branch's continuation
   - The IH from BranchesStep gives: EQ2 (trans first' role) (trans first role)
   - Combine with trans_comm_other rewrites

3. **mu case**: g = mu t body, step (body.substitute t (mu t body)) act g'
   - IH: EQ2 (trans g' role) (trans (body.substitute t (mu t body)) role)
   - Uses: trans_substitute_unfold + EQ2_unfold_right to connect to trans (mu t body) role

**Note:** Requires g to be projectable (in addition to closed/wellFormed). -/
theorem proj_trans_other_step (g g' : GlobalType) (act : GlobalActionR) (role : String)
    (hstep : step g act g')
    (hclosed : g.isClosed = true)
    (hwf : g.wellFormed = true)
    (hns : role ≠ act.sender) (hnr : role ≠ act.receiver)
    (hproj : ProjectableClosedWellFormed) :
    EQ2 (projTrans g' role) (projTrans g role) := by
  exact
  @step.rec
    -- motive_1: for step g act g', non-participant role has EQ2 (projTrans g' role) (projTrans g role)
    (motive_1 := fun g act g' _ =>
      g.isClosed = true → g.wellFormed = true →
      ∀ role, role ≠ act.sender → role ≠ act.receiver →
        EQ2 (projTrans g' role) (projTrans g role))
    -- motive_2: for BranchesStep bs act bs', non-participant has BranchesRel on transBranches
    (motive_2 := fun bs act bs' _ =>
      (∀ p ∈ bs, p.2.isClosed = true) →
      (∀ p ∈ bs, p.2.wellFormed = true) →
      ∀ role, role ≠ act.sender → role ≠ act.receiver →
        BranchesRel EQ2 (transBranches bs' role) (transBranches bs role))
    -- Case 1: comm_head
    (fun sender receiver branches label cont hmem hclosed hwf role hns hnr => by
      -- g = comm sender receiver branches, g' = cont
      -- For comm_head: act = { sender, receiver, label }
      -- So hns : role ≠ sender, hnr : role ≠ receiver
      -- projTrans g role = projTrans first_cont role (by trans_comm_other since role ≠ sender ≠ receiver)
      -- projTrans g' role = projTrans cont role
      -- Need: EQ2 (projTrans cont role) (projTrans first_cont role)
      match hbranches : branches with
      | [] =>
          -- hmem : (label, cont) ∈ [], contradiction
          simp at hmem
      | (fl, fc) :: rest =>
          -- projTrans g role = projTrans fc role (first continuation)
          have htrans_g : projTrans (GlobalType.comm sender receiver ((fl, fc) :: rest)) role =
              projTrans fc role := trans_comm_other sender receiver role ((fl, fc) :: rest) hns hnr
          have hproj_comm :
              ∃ lt,
                CProject (GlobalType.comm sender receiver ((fl, fc) :: rest)) role lt := by
            have hproj_comm' :
                Projectable (GlobalType.comm sender receiver ((fl, fc) :: rest)) := by
              simpa [ProjectableClosedWellFormed] using
                (hproj (GlobalType.comm sender receiver ((fl, fc) :: rest))
                  (by simpa [hbranches] using hclosed)
                  (by simpa [hbranches] using hwf))
            exact hproj_comm' role
          -- Extract closedness for all branches from comm closedness
          have hclosed_branches : ∀ b ∈ ((fl, fc) :: rest), b.2.isClosed = true := by
            intro b hb
            have := GlobalType.isClosed_comm_branches sender receiver ((fl, fc) :: rest) hclosed
            exact this b hb
          -- Extract wellFormedness for all branches from comm wellFormedness
          have hallwf_branches : ∀ b ∈ ((fl, fc) :: rest), b.2.wellFormed = true :=
            GlobalType.wellFormed_comm_branches sender receiver ((fl, fc) :: rest) hwf
          -- All branches project coherently for non-participants
          have hcoherent := branches_project_coherent sender receiver fl fc rest label cont role hmem
            hns hnr hclosed_branches hallwf_branches hproj_comm
          rw [htrans_g]
          exact hcoherent)
    -- Case 2: comm_async
    (fun sender receiver branches branches' act label cont hns_cond _hcond _hmem _hcan _hbstep
        ih_bstep hclosed hwf role hns hnr => by
      -- g = comm sender receiver branches
      -- g' = comm sender receiver branches'
      -- hns : role ≠ act.sender, hnr : role ≠ act.receiver
      -- ih_bstep : closedness → wellFormed → ... →
      --            BranchesRel EQ2 (transBranches branches' role) (transBranches branches role)
      -- hclosed : (comm sender receiver branches).isClosed = true
      --
      -- Derive branch closedness from comm closedness
      have hbranches_closed : ∀ p ∈ branches, p.2.isClosed = true :=
        GlobalType.isClosed_comm_branches sender receiver branches hclosed
      -- Derive branch wellFormedness
      have hbranches_wf : ∀ p ∈ branches, p.2.wellFormed = true :=
        GlobalType.wellFormed_comm_branches sender receiver branches hwf
      -- Case split on role's relationship to outer comm's sender/receiver
      by_cases hrs : role = sender
      · -- role = sender: project as send
        have hbranch_rel := ih_bstep hbranches_closed hbranches_wf role hns hnr
        simp only [projTrans, trans_comm_sender sender receiver role branches hrs,
                   trans_comm_sender sender receiver role branches' hrs]
        -- Goal: EQ2 (send receiver (transBranches branches' role)) (send receiver (transBranches branches role))
        -- EQ2F EQ2 (send p bs) (send p cs) = p = p ∧ BranchesRel EQ2 bs cs
        exact EQ2.construct ⟨rfl, hbranch_rel⟩
      · by_cases hrr : role = receiver
        · -- role = receiver: project as recv
          have hbranch_rel := ih_bstep hbranches_closed hbranches_wf role hns hnr
          simp only [projTrans, trans_comm_receiver sender receiver role branches hrr hrs,
                     trans_comm_receiver sender receiver role branches' hrr hrs]
          -- Goal: EQ2 (recv sender (transBranches branches' role)) (recv sender (transBranches branches role))
          -- EQ2F EQ2 (recv p bs) (recv p cs) = p = p ∧ BranchesRel EQ2 bs cs
          exact EQ2.construct ⟨rfl, hbranch_rel⟩
        · -- role ≠ sender ∧ role ≠ receiver: project via first branch
          have hbranch_rel := ih_bstep hbranches_closed hbranches_wf role hns hnr
          -- Case split on branch structure
          match hbranches : branches, hbranches' : branches' with
          | [], [] =>
              -- Both empty: trans_comm_other gives .end for both
              simp only [trans_comm_other sender receiver role [] hrs hrr]
              exact EQ2_refl _
          | [], _ :: _ =>
              -- BranchesStep from [] is only BranchesStep.nil to [], contradiction
              cases _hbstep
          | _ :: _, [] =>
              -- BranchesStep to [] requires branches = [], contradiction
              cases _hbstep
          | (fl, fc) :: rest, (fl', fc') :: rest' =>
              -- trans_comm_other gives: trans (comm s r ((l,c)::_)) role = trans c role
              simp only [trans_comm_other sender receiver role ((fl, fc) :: rest) hrs hrr,
                         trans_comm_other sender receiver role ((fl', fc') :: rest') hrs hrr]
              -- Now goal is: EQ2 (trans fc' role) (trans fc role)
              -- hbranch_rel is in expanded form
              simp only [transBranches] at hbranch_rel
              -- BranchesRel = Forall₂, cons case gives (pair_proof, tail_proof)
              -- pair_proof : a.1 = b.1 ∧ EQ2 a.2 b.2
              cases hbranch_rel with
              | cons hpair htail =>
                  -- hpair : (fl', trans fc' role).1 = (fl, trans fc role).1 ∧ EQ2 (fl', trans fc' role).2 (fl, trans fc role).2
                  -- hpair.2 : EQ2 (trans fc' role) (trans fc role)
                  exact hpair.2)
    -- Case 3: mu
    (fun t body act g' _hstep_sub ih_step hclosed hwf role hns hnr => by
      -- g = mu t body
      -- hstep_sub : step (body.substitute t (mu t body)) act g'
      -- ih_step : (body.substitute...).isClosed → (body.substitute...).wellFormed → ∀ role, ... → EQ2
      -- hclosed : (mu t body).isClosed = true
      --
      -- Need to chain: g' ~EQ2~ subst ~EQ2~ unfold ~EQ2~ mu
      -- With Coq-style trans, we don't need to case split on lcontractive.
      -- The trans_substitute_unfold theorem handles both cases.
      --
      -- First, derive closedness of the substituted type
      have hsubst_closed : (body.substitute t (.mu t body)).isClosed = true :=
        GlobalType.isClosed_substitute_mu t body hclosed
      have hsubst_wf : (body.substitute t (.mu t body)).wellFormed = true :=
        wellFormed_mu_unfold t body hwf
      -- Step 1: EQ2 (projTrans g' role) (projTrans (body.substitute...) role) [from ih_step]
      have h1 : EQ2 (projTrans g' role) (projTrans (body.substitute t (.mu t body)) role) :=
        ih_step hsubst_closed hsubst_wf role hns hnr
      -- Step 2: EQ2 (projTrans (body.substitute...) role) ((projTrans (mu...) role).unfold)
      have h2 : EQ2 (projTrans (body.substitute t (.mu t body)) role)
          ((projTrans (.mu t body) role).unfold) :=
        trans_substitute_unfold t body role hclosed
      -- Step 3: EQ2 ((projTrans (mu...) role).unfold) (projTrans (mu...) role)
      have h3 : EQ2 ((projTrans (.mu t body) role).unfold) (projTrans (.mu t body) role) :=
        EQ2_symm (EQ2_unfold_right (EQ2_refl _))
      -- Chain via transitivity
      exact EQ2_trans (EQ2_trans h1 h2) h3)
    -- Case 4: BranchesStep.nil
    (fun _act _hclosed _hwf role _hns _hnr => by
      simp only [transBranches]
      exact List.Forall₂.nil)
    -- Case 5: BranchesStep.cons
    (fun label g g' rest rest' act _hstep_g _hbstep_rest ih_step ih_bstep hclosed hwf role hns hnr => by
      simp only [transBranches]
      apply List.Forall₂.cons
      · -- Head: (label, trans g' role) and (label, trans g role)
        constructor
        · rfl  -- labels match
        · -- Need: EQ2 (trans g' role) (trans g role)
          -- ih_step gives exactly this, g is closed since it's in ((label, g) :: rest)
          have hg_closed : g.isClosed = true := hclosed (label, g) List.mem_cons_self
          have hg_wf : g.wellFormed = true := hwf (label, g) List.mem_cons_self
          exact ih_step hg_closed hg_wf role hns hnr
      · -- Tail: IH gives BranchesRel for rest
        have hrest_closed : ∀ p ∈ rest, p.2.isClosed = true := fun x hx =>
          hclosed x (List.mem_cons_of_mem (label, g) hx)
        have hrest_wf : ∀ p ∈ rest, p.2.wellFormed = true := fun x hx =>
          hwf x (List.mem_cons_of_mem (label, g) hx)
        exact ih_bstep hrest_closed hrest_wf role hns hnr)
    g act g' hstep hclosed hwf role hns hnr

/-- BranchesStep preserves transBranches up to branch-wise EQ2 for non-participants.

When branches step to branches' via BranchesStep, the transBranches are related
by BranchesRel EQ2 for any role not involved in the action.

This captures the semantic property that stepping inside branches doesn't affect
non-participant projections: each branch steps, and projection commutes with stepping.

Proven by induction on BranchesStep, using proj_trans_other_step for each branch.

**Note:** Requires all branch continuations to be closed, wellFormed, and projectable. -/
theorem branches_step_preserves_trans (branches branches' : List (Label × GlobalType))
    (act : GlobalActionR) (role : String)
    (hstep : BranchesStep step branches act branches')
    (hclosed : ∀ p ∈ branches, p.2.isClosed = true)
    (hwf : ∀ p ∈ branches, p.2.wellFormed = true)
    (hproj : ProjectableClosedWellFormed)
    (hns : role ≠ act.sender) (hnr : role ≠ act.receiver) :
    BranchesRel EQ2 (transBranches branches' role) (transBranches branches role) := by
  induction hstep with
  | nil =>
      simp only [transBranches]
      exact List.Forall₂.nil
  | cons label g g' rest rest' act hstep_g _hbstep_rest ih =>
      simp only [transBranches]
      apply List.Forall₂.cons
      · constructor
        · rfl
        · have hg_closed : g.isClosed = true := hclosed (label, g) List.mem_cons_self
          have hg_wf : g.wellFormed = true := hwf (label, g) List.mem_cons_self
          exact proj_trans_other_step g g' act role hstep_g hg_closed hg_wf hns hnr hproj
      · have hrest_closed : ∀ p ∈ rest, p.2.isClosed = true := fun x hx =>
          hclosed x (List.mem_cons_of_mem (label, g) hx)
        have hrest_wf : ∀ p ∈ rest, p.2.wellFormed = true := fun x hx =>
          hwf x (List.mem_cons_of_mem (label, g) hx)
        exact ih hrest_closed hrest_wf hns hnr

/-! ## Claims Bundle -/

/-- Domain containment for EnvStep: post-step domain is subset of pre-step domain.

Note: EnvStep does NOT preserve domain equality because global steps can shrink
the role set (step_roles_subset). Instead, we have containment.

For domain equality, use EnvStepOnto which projects onto a fixed role set. -/
theorem envstep_dom_subset {env env' : ProjectedEnv} {act : GlobalActionR}
    (h : EnvStep env act env') :
    ∀ p, p ∈ env'.map Prod.fst → p ∈ env.map Prod.fst := by
  cases h with
  | of_global g g' _ hstep =>
      intro p hp
      simp only [projEnv_dom] at hp ⊢
      exact step_roles_subset g g' _ hstep p hp

/-- Claims bundle for harmony lemmas. -/
structure Claims where
  /-- Global step induces environment step. -/
  harmony : ∀ g g' act, step g act g' → EnvStep (projEnv g) act (projEnv g')
  /-- Domain containment through steps (post ⊆ pre). -/
  dom_subset : ∀ env env' act, EnvStep env act env' →
    ∀ p, p ∈ env'.map Prod.fst → p ∈ env.map Prod.fst

/-- Build the claims bundle from proven theorems. -/
def claims : Claims where
  harmony := step_harmony
  dom_subset := fun _ _ _ h => envstep_dom_subset h

end RumpsteakV2.Proofs.Projection.Harmony
