import RumpsteakV2.Semantics.EnvStep
import RumpsteakV2.Protocol.Projection.Projectb
import RumpsteakV2.Protocol.Projection.Project
import RumpsteakV2.Protocol.Participation
import RumpsteakV2.Protocol.CoTypes.EQ2
import RumpsteakV2.Protocol.CoTypes.EQ2Props
import RumpsteakV2.Protocol.CoTypes.EQ2Paco
import RumpsteakV2.Protocol.Projection.ProjSubst
import RumpsteakV2.Proofs.Safety.Determinism
import RumpsteakV2.Proofs.Projection.MuUnfoldLemmas
import RumpsteakV2.Proofs.Projection.SubstEndUnguarded

/-
The Problem. Relate global protocol steps to environment steps in the operational
semantics, showing that projection commutes with execution. The key difficulty is
that projection distinguishes participants from non-participants, so step alignment
must preserve non-participant projections while respecting communication structure
for participants.

Solution Structure. Prove step harmony for direct communication steps, then show
non-participant projections are stable across unrelated steps. Combine these into
a Claims bundle that exposes the main harmony properties for downstream safety
proofs.
-/

/-! # RumpsteakV2.Proofs.Projection.Harmony

Harmony between global steps and environment steps.

## Expose

The following definitions form the semantic interface for proofs:

- `Claims`: bundle of harmony properties
- `step_harmony`: global step induces matching env step
- `proj_trans_other_step`: non-participant projection unchanged after step

## Technical Debt Summary (legacy placeholders removed; assumption-free in this file)

**MAJOR PROGRESS**: `trans_branches_coherent` ELIMINATED!
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
- `EQ2_trans_wf`: **PROVEN** via Bisim (EQ2Props.lean); used with explicit well-formedness witnesses

**Remaining Assumptions:** None (sender/receiver lemmas proven via head-action predicate)

**COHERENCE PROOF COMPLETE (modulo helper lemmas):**
- `trans_branches_coherent_EQ2`: **PROVEN** using participation structure
  - Case 1 (non-participant): Uses `EQ_end` - all branches project to .end
  - Case 2 (participant): Uses `part_of_all2` - uniform participation (legacy extraction placeholders)
- `trans_produces_CProject`: Bridges trans to CProject (uses coherence)
- `branches_project_coherent`: Extracts EQ2 equivalence from AllBranchesProj (legacy placeholders)

**Inherited from MuUnfoldLemmas.lean (via ProjSubst.lean):**
4. `proj_subst`: Projection-substitution commutation (Coq indProj.v:173)

**Key changes from Coq alignment:**
- `trans` now checks `(trans body role).isGuarded t` instead of `lcontractive body`
- This matches Coq's `eguarded` check on the projected type, not the global type
- Non-contractive projections are replaced with `.end` by construction
- The old `step_noncontr_impossible` assumption was removed (it was false for nested mu)
- All theorems require closedness of global types (standard for protocol verification)

**Next steps:** propagate the head-action predicate (`action_pred`) through callers
if they need sender/receiver projections beyond the head-communication case.
-/

/-! ## Notes

### Projection Coherence

These lemmas establish that projection is coherent with stepping:
after a global step, the projected environment correctly reflects
the new local types for each role.

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
This approach uses only the structure of trans without requiring CProject proofs.

### Substitution Commutation

The core coinductive property: projection (via trans) commutes with global mu-substitution.

For any GlobalType g, recursion variable t, and mu-body G (where G = mu t g for some g):
  `EQ2 (projTrans (g.substitute t G) role) ((projTrans g role).substitute t (projTrans G role))`

This is the "projection commutes with substitution" lemma (Coq: `full_eunf_subst`).
The property requires coinductive reasoning because branch continuations recurse indefinitely.

### ProjSubstRel Postfixpoint Proof Notes

ProjSubstRel is a post-fixpoint of EQ2F (with EQ2 as accumulator).

This encapsulates the coinductive reasoning for projection-substitution commutation.
The proof proceeds by case analysis on the GlobalType witness:
- `.end`: both sides are `.end` ✓
- `.var v`: split on v = t; both sides match ✓
- `.mu s inner`:
  - s = t (shadowed): both sides identical ✓
  - s ≠ t:
    - Both guarded: mu-mu case requires s-unfold/t-subst interaction [legacy placeholders]
    - Mismatched guardedness: requires showing unfold relates to .end [legacy placeholders]
    - Both unguarded: both .end ✓
- `.comm sender receiver branches`:
  - role = sender: both .send, branches via transBranches_ProjSubstRel ✓
  - role = receiver: both .recv, branches via transBranches_ProjSubstRel ✓
  - non-participant:
    - empty branches: both .end ✓
    - non-empty: recursive call on continuation subterm ✓

### trans_subst_comm intent

Projection commutes with substitution.

For any GlobalType g, recursion variable t, mu-type G, and role:
  `EQ2 (projTrans (g.substitute t G) role) ((projTrans g role).substitute t (projTrans G role))`

This is semantically sound: the LHS and RHS represent the same infinite communication tree
when fully unfolded.

**Coq reference:** `full_eunf_subst` in `coLocal.v`

### EQ2 transitivity + subst_end_unguarded_eq2_end

EQ2 transitivity now uses `EQ2_trans_wf` from EQ2Props (Bisim detour).
This replaces the prior `EQ2_trans` path and requires explicit
well-formedness witnesses for intermediate types.

Substituting `.end` for an unguarded variable produces something EQ2 to `.end`.

When `lt.isGuarded v = false`, the type `lt` has the structure:
- Either `lt = .var v` (directly), or
- `lt = .mu s body` where `s ≠ v` and `body.isGuarded v = false`

This is because `.send`/`.recv` always return `true` for `isGuarded`.

After substituting `.end` for `v`:
- `.var v` becomes `.end` (EQ2 .end .end)
- `.mu s body` becomes `.mu s (body.substitute v .end)`, which unfolds to `.end`
  because the inner structure eventually reaches `.var v` → `.end`

**PROVEN** in SubstEndUnguarded.lean via UnfoldsToEnd induction.
-/

namespace RumpsteakV2.Proofs.Projection.Harmony

open RumpsteakV2.Protocol.GlobalType
open RumpsteakV2.Protocol.LocalTypeR
open RumpsteakV2.Protocol.Projection.Projectb
open RumpsteakV2.Protocol.Projection.Project
  (EQ_end part_of2_or_end CProject_implies_EQ2_trans Projectable ProjectableClosedWellFormed)
open RumpsteakV2.Protocol.Participation (part_of2 part_of_all2 part_of_all2_comm_inv not_part_of2_comm)
open RumpsteakV2.Protocol.CoTypes.EQ2
open RumpsteakV2.Protocol.CoTypes.EQ2Props
open RumpsteakV2.Protocol.CoTypes.Quotient
open RumpsteakV2.Semantics.EnvStep

-- Alias to avoid ambiguity with Trans typeclass
abbrev projTrans := RumpsteakV2.Protocol.Projection.Trans.trans
open RumpsteakV2.Protocol.Projection.Trans (trans_comm_sender trans_comm_receiver trans_comm_other
  transBranches lcontractive trans_wellFormed_of_wellFormed)

/-! ## Claims Bundle -/

/-- Claims bundle for harmony lemmas. -/
structure Claims where
  /-- Global step induces environment step. -/
  harmony : ∀ g g' act, step g act g' → EnvStep (projEnv g) act (projEnv g')
  /-- Domain containment through steps (post ⊆ pre). -/
  dom_subset : ∀ env env' act, EnvStep env act env' →
    ∀ p, p ∈ env'.map Prod.fst → p ∈ env.map Prod.fst

/-! ## Step Harmony

The harmony property states that global steps are faithfully reflected in
the projected environment. This is the key lemma connecting global semantics
to local session type semantics. -/

/-- Global step induces environment step through projection. -/
theorem step_harmony (g g' : GlobalType) (act : GlobalActionR)
    (hstep : step g act g') :
    EnvStep (projEnv g) act (projEnv g') :=
  -- Directly lift the global step to an environment step.
  step_to_envstep g g' act hstep

/-! ## Projection Coherence -/

/-! ### Key Theorem: trans Produces Valid Projections

The trans function produces valid CProject proofs for well-formed types.
This is the bridge between computational projection (trans) and relational projection (CProject). -/

/-- Helper: wellFormed implies allCommsNonEmpty. -/
private theorem allCommsNonEmpty_of_wf (g : GlobalType) (hwf : g.wellFormed = true) :
    g.allCommsNonEmpty = true := by
  -- Unpack the wellFormed conjunction to reach allCommsNonEmpty.
  simp only [GlobalType.wellFormed, Bool.and_eq_true] at hwf
  rcases hwf with ⟨⟨⟨_havb, hne⟩, _hnsc⟩, _hprod⟩
  exact hne

/-- Helper: CProject + wellFormed gives the exact trans candidate. -/
private theorem trans_eq_of_CProject_wf (g : GlobalType) (role : String) (lt : LocalTypeR)
    (hproj : CProject g role lt) (hwf : g.wellFormed = true) :
    projTrans g role = lt := by
  -- Use trans_eq_of_CProject after extracting allCommsNonEmpty.
  have hne := allCommsNonEmpty_of_wf g hwf
  simpa [projTrans] using (trans_eq_of_CProject g role lt hproj hne)

/-- Helper: non-participant comms yield AllBranchesProj from CProject. -/
private theorem allBranchesProj_of_comm_nonpart
    (sender receiver : String) (branches : List (Label × GlobalType)) (role : String) (lt : LocalTypeR)
    (hns : role ≠ sender) (hnr : role ≠ receiver)
    (hproj : CProject (GlobalType.comm sender receiver branches) role lt) :
    AllBranchesProj CProject branches role lt := by
  -- Destructure the comm case in CProjectF and drop sender/receiver branches.
  have hF := CProject_destruct hproj
  simpa [CProjectF, hns, hnr] using hF

/-- Branch coherence from participation structure.

For well-formed communications where role is not a participant, all branch continuations
project to EQ2-equivalent local types. This is proven using the participation infrastructure:
- If role doesn't participate at all: all branches project to .end (via EQ_end)
- If role participates through branches: all branches have part_of_all2 (uniform participation)

This theorem eliminates the trans_branches_coherent assumption by proving coherence from
first principles, following Coq's proof strategy. -/
private theorem trans_branches_coherent_EQ2_participant
    (sender receiver : String) (branches : List (Label × GlobalType)) (role : String)
    (hnp : role ≠ sender ∧ role ≠ receiver)
    (hne : branches ≠ [])
    (hwf : (GlobalType.comm sender receiver branches).wellFormed = true)
    (lt : LocalTypeR) (hproj_comm : CProject (.comm sender receiver branches) role lt) :
    ∀ b ∈ branches, EQ2 (projTrans b.2 role) (projTrans branches.head!.2 role) := by
  -- Use AllBranchesProj to identify a common candidate across branches.
  cases hbranches : branches with
  | nil => cases (hne hbranches)
  | cons hd tl =>
      intro b hmem
      have hwf' : (GlobalType.comm sender receiver (hd :: tl)).wellFormed = true := by
        simpa [hbranches] using hwf
      have hproj_comm' : CProject (GlobalType.comm sender receiver (hd :: tl)) role lt := by
        simpa [hbranches] using hproj_comm
      have hall : AllBranchesProj CProject (hd :: tl) role lt :=
        allBranchesProj_of_comm_nonpart sender receiver (hd :: tl) role lt hnp.1 hnp.2 hproj_comm'
      have hproj_hd : CProject hd.2 role lt := hall hd (List.Mem.head tl)
      have hproj_b : CProject b.2 role lt := hall b hmem
      have hwf_hd : hd.2.wellFormed = true :=
        GlobalType.wellFormed_comm_branches sender receiver (hd :: tl) hwf' hd (List.Mem.head tl)
      have hwf_b : b.2.wellFormed = true :=
        GlobalType.wellFormed_comm_branches sender receiver (hd :: tl) hwf' b hmem
      have htrans_hd : projTrans hd.2 role = lt := trans_eq_of_CProject_wf hd.2 role lt hproj_hd hwf_hd
      have htrans_b : projTrans b.2 role = lt := trans_eq_of_CProject_wf b.2 role lt hproj_b hwf_b
      have hEq : projTrans b.2 role = projTrans hd.2 role := by simp [htrans_b, htrans_hd]
      simpa [hbranches, List.head!, hEq] using (EQ2_refl (projTrans hd.2 role))

private theorem trans_branches_coherent_EQ2_nonpart
    (sender receiver : String) (branches : List (Label × GlobalType)) (role : String)
    (hne : branches ≠ [])
    (hwf : (GlobalType.comm sender receiver branches).wellFormed = true)
    (hnot : ¬ part_of2 role (.comm sender receiver branches)) :
    ∀ b ∈ branches, EQ2 (projTrans b.2 role) (projTrans branches.head!.2 role) := by
  -- Non-participants project each branch to .end.
  intro b hmem
  rcases not_part_of2_comm hnot with ⟨_, hnotbranch⟩
  cases hbranches : branches with
  | nil => cases (hne hbranches)
  | cons hd tl =>
      have hmem_hd : hd ∈ branches := by simp [hbranches]
      have hnopart_hd : ¬ part_of2 role hd.2 := hnotbranch hd hmem_hd
      have hnopart_b : ¬ part_of2 role b.2 := hnotbranch b hmem
      have hwf_hd : hd.2.wellFormed = true :=
        GlobalType.wellFormed_comm_branches sender receiver branches hwf hd hmem_hd
      have hwf_b : b.2.wellFormed = true :=
        GlobalType.wellFormed_comm_branches sender receiver branches hwf b hmem
      have hhd_end : EQ2 (projTrans hd.2 role) .end := EQ2_symm (EQ_end role hd.2 hnopart_hd hwf_hd)
      have hb_end : EQ2 (projTrans b.2 role) .end := EQ2_symm (EQ_end role b.2 hnopart_b hwf_b)
      simpa [hbranches, List.head!] using (EQ2_trans_via_end hb_end (EQ2_symm hhd_end))

theorem trans_branches_coherent_EQ2
    (sender receiver : String) (branches : List (Label × GlobalType)) (role : String)
    (hnp : role ≠ sender ∧ role ≠ receiver)
    (hne : branches ≠ [])
    (hwf : (GlobalType.comm sender receiver branches).wellFormed = true)
    (hproj_comm : ∃ lt, CProject (.comm sender receiver branches) role lt) :
    ∀ b ∈ branches, EQ2 (projTrans b.2 role) (projTrans branches.head!.2 role) := by
  -- Split on whether the role participates in the comm.
  intro b hmem
  by_cases hpart : part_of2 role (.comm sender receiver branches)
  · rcases hproj_comm with ⟨lt, hproj⟩
    exact trans_branches_coherent_EQ2_participant sender receiver branches role hnp hne hwf lt hproj b hmem
  · exact trans_branches_coherent_EQ2_nonpart sender receiver branches role hne hwf hpart b hmem

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
  -- Reduce to the original candidate via trans_eq_of_CProject.
  have htrans_eq : projTrans g role = lt := trans_eq_of_CProject_wf g role lt hproj hwf
  simpa [htrans_eq] using hproj

/-- Helper: derive equality of branch projections via a common CProject candidate. -/
private theorem branches_project_coherent_eq (sender receiver : String)
    (first_label : Label) (first_cont : GlobalType) (rest : List (Label × GlobalType))
    (label : Label) (cont : GlobalType) (role : String)
    (hmem : (label, cont) ∈ ((first_label, first_cont) :: rest))
    (hns : role ≠ sender) (hnr : role ≠ receiver)
    (hallwf_branches : ∀ b ∈ ((first_label, first_cont) :: rest), b.2.wellFormed = true)
    (hproj_comm :
      ∃ lt, CProject (GlobalType.comm sender receiver ((first_label, first_cont) :: rest)) role lt) :
    projTrans cont role = projTrans first_cont role := by
  -- Use CProject to get a common candidate and rewrite both branches to it.
  rcases hproj_comm with ⟨lt, hproj_comm⟩
  have hall : AllBranchesProj CProject ((first_label, first_cont) :: rest) role lt :=
    allBranchesProj_of_comm_nonpart sender receiver ((first_label, first_cont) :: rest)
      role lt hns hnr hproj_comm
  have hproj_first : CProject first_cont role lt :=
    hall (first_label, first_cont) (List.Mem.head rest)
  have hproj_cont : CProject cont role lt := hall (label, cont) hmem
  have hwf_first : first_cont.wellFormed = true :=
    hallwf_branches (first_label, first_cont) (List.Mem.head rest)
  have hwf_cont : cont.wellFormed = true := hallwf_branches (label, cont) hmem
  have htrans_first : projTrans first_cont role = lt :=
    trans_eq_of_CProject_wf first_cont role lt hproj_first hwf_first
  have htrans_cont : projTrans cont role = lt :=
    trans_eq_of_CProject_wf cont role lt hproj_cont hwf_cont
  simp [htrans_cont, htrans_first]

/-- Branch coherence for non-participants: all branches project to EQ2-equivalent types. -/
theorem branches_project_coherent (sender receiver : String)
    (first_label : Label) (first_cont : GlobalType)
    (rest : List (Label × GlobalType)) (label : Label) (cont : GlobalType) (role : String)
    (hmem : (label, cont) ∈ ((first_label, first_cont) :: rest))
    (hns : role ≠ sender) (hnr : role ≠ receiver)
    (_hclosed_branches : ∀ b ∈ ((first_label, first_cont) :: rest), b.2.isClosed = true)
    (hallwf_branches : ∀ b ∈ ((first_label, first_cont) :: rest), b.2.wellFormed = true)
    (hproj_comm :
      ∃ lt, CProject (GlobalType.comm sender receiver ((first_label, first_cont) :: rest)) role lt) :
    EQ2 (projTrans cont role) (projTrans first_cont role) := by
  -- Reduce to equality of projections, then use EQ2 reflexivity.
  have hEq :=
    branches_project_coherent_eq sender receiver first_label first_cont rest label cont role
      hmem hns hnr hallwf_branches hproj_comm
  simpa [hEq] using (EQ2_refl (projTrans cont role))

end RumpsteakV2.Proofs.Projection.Harmony
