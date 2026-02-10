import Choreography.Projection.Project.ImplConstructors

/-! # Choreography.Projection.Project.ImplTransRelComp.Core

CProjectTransRel, CProjectTransRelComp definitions and postfix property.
-/

/-
The Problem. State the projection/harmony lemma objective and the exact invariant boundary it preserves.
Solution Structure. Introduce local helper lemmas first, then discharge the main theorem by case analysis over the operational/projection relation.
-/

set_option linter.unnecessarySimpa false

/-! ## Core Development -/

namespace Choreography.Projection.Project

open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
open Choreography.Projection.Trans
open Choreography.Projection.Projectb
open SessionCoTypes.EQ2
open SessionCoTypes.EQ2Props
open SessionCoTypes.EQ2Paco
open Paco
open SessionTypes.Participation

/-- Local copy of BranchesRel_mono (since the original is private in EQ2.lean). -/
theorem BranchesRel_mono {R S : Rel}
    (h : ∀ a b, R a b → S a b) :
    ∀ {bs cs}, BranchesRel R bs cs → BranchesRel S bs cs := by
  intro bs cs hrel
  exact List.Forall₂.imp (fun a b hab => ⟨hab.1, h _ _ hab.2⟩) hrel

/-- Monotonicity of EQ2F over relations. -/
theorem EQ2F_mono {R S : Rel}
    (h : ∀ a b, R a b → S a b) :
    ∀ {a b}, EQ2F R a b → EQ2F S a b := by
  intro a b hrel
  cases a <;> cases b <;> simp [EQ2F] at hrel ⊢
  all_goals
    first
    | exact hrel
    | exact h _ _ hrel
    | cases hrel with
      | intro h1 h2 =>
        first
        | exact ⟨h _ _ h1, h _ _ h2⟩
        | exact ⟨h1, BranchesRel_mono h h2⟩

/-! NOTE: EQ2 transitivity is used with explicit LocalTypeR.WellFormed witnesses. -/

theorem wf_tail_of_cons
    {lb : BranchR} {bs : List BranchR}
    (hwf : ∀ lb' ∈ lb :: bs, LocalTypeR.WellFormed lb'.2.2) :
    ∀ lb' ∈ bs, LocalTypeR.WellFormed lb'.2.2 := by
  -- Derive tail well-formedness from a cons list witness.
  intro lb' hmem
  exact hwf lb' (by simp [hmem])

private theorem BranchesRel_trans_chain_head {R : Rel}
    (hextend : ∀ a b c, R a b → EQ2 b c →
      LocalTypeR.WellFormed a → LocalTypeR.WellFormed b → LocalTypeR.WellFormed c → R a c)
    {lb_bs lb_cs lb_ds : BranchR}
    (h1 : lb_bs.1 = lb_cs.1 ∧ (EQ2_closure R) lb_bs.2.2 lb_cs.2.2)
    (h2 : lb_cs.1 = lb_ds.1 ∧ EQ2 lb_cs.2.2 lb_ds.2.2)
    (hWFa : LocalTypeR.WellFormed lb_bs.2.2)
    (hWFb : LocalTypeR.WellFormed lb_cs.2.2)
    (hWFc : LocalTypeR.WellFormed lb_ds.2.2) :
    lb_bs.1 = lb_ds.1 ∧ (EQ2_closure R) lb_bs.2.2 lb_ds.2.2 := by
  -- Combine labels and chain the continuation relation through hextend or EQ2_trans_wf.
  constructor
  · exact h1.1.trans h2.1
  · cases h1.2 with
    | inl hr => exact Or.inl (hextend _ _ _ hr h2.2 hWFa hWFb hWFc)
    | inr heq => exact Or.inr (EQ2_trans_wf heq h2.2 hWFa hWFb hWFc)

theorem BranchesRel_trans_chain_rev_head {R : Rel}
    (hextend : ∀ a b c, EQ2 a b → R b c →
      LocalTypeR.WellFormed a → LocalTypeR.WellFormed b → LocalTypeR.WellFormed c → R a c)
    {lb_bs lb_cs lb_ds : BranchR}
    (h1 : lb_bs.1 = lb_cs.1 ∧ EQ2 lb_bs.2.2 lb_cs.2.2)
    (h2 : lb_cs.1 = lb_ds.1 ∧ (EQ2_closure R) lb_cs.2.2 lb_ds.2.2)
    (hWFa : LocalTypeR.WellFormed lb_bs.2.2)
    (hWFb : LocalTypeR.WellFormed lb_cs.2.2)
    (hWFc : LocalTypeR.WellFormed lb_ds.2.2) :
    lb_bs.1 = lb_ds.1 ∧ (EQ2_closure R) lb_bs.2.2 lb_ds.2.2 := by
  -- Combine labels and chain the continuation relation through hextend or EQ2_trans_wf.
  constructor
  · exact h1.1.trans h2.1
  · cases h2.2 with
    | inl hr => exact Or.inl (hextend _ _ _ h1.2 hr hWFa hWFb hWFc)
    | inr heq => exact Or.inr (EQ2_trans_wf h1.2 heq hWFa hWFb hWFc)

/-- Chain BranchesRel through an intermediate into the EQ2_closure.
    Given BranchesRel (EQ2_closure R) bs cs and BranchesRel EQ2 cs ds,
    produce BranchesRel (EQ2_closure R) bs ds.

    Requires an extension hypothesis: R can be extended with EQ2 at the right
    to produce another R. This is satisfied by CProjectTransRelComp. -/
theorem BranchesRel_trans_chain {R : Rel}
    (hextend : ∀ a b c, R a b → EQ2 b c →
      LocalTypeR.WellFormed a → LocalTypeR.WellFormed b → LocalTypeR.WellFormed c → R a c)
    {bs cs ds : List BranchR}
    (hbc : BranchesRel (EQ2_closure R) bs cs)
    (hcd : BranchesRel EQ2 cs ds)
    (hwf_bs : ∀ lb ∈ bs, LocalTypeR.WellFormed lb.2.2)
    (hwf_cs : ∀ lb ∈ cs, LocalTypeR.WellFormed lb.2.2)
    (hwf_ds : ∀ lb ∈ ds, LocalTypeR.WellFormed lb.2.2) :
    BranchesRel (EQ2_closure R) bs ds := by
  induction hbc generalizing ds with -- Head/tail split of Forall₂.
  | nil => cases hcd; exact List.Forall₂.nil
  | cons h1 hbc_tail ih =>
      rename_i lb_bs lb_cs bs_tail cs_tail; cases ds with
      | nil => cases hcd
      | cons lb_ds ds_tail =>
          cases hcd with
          | cons h2 hcd_tail =>
              constructor
              · exact BranchesRel_trans_chain_head hextend h1 h2
                  (hwf_bs lb_bs (by simp)) (hwf_cs lb_cs (by simp)) (hwf_ds lb_ds (by simp))
              · exact ih hcd_tail (wf_tail_of_cons hwf_bs)
                  (wf_tail_of_cons hwf_cs) (wf_tail_of_cons hwf_ds)

/-- Witness relation for CProject_implies_EQ2_trans coinduction.
    Pairs local type lt with trans output when lt is a valid CProject output.
    Uses GlobalType.wellFormed (Coq gInvPred analogue) to derive allCommsNonEmpty. -/
def CProjectTransRel : Rel := fun lt t =>
  ∃ g role, CProject g role lt ∧ t = Trans.trans g role ∧ g.wellFormed = true

/-- CProject preserves well-formedness under well-formed globals. -/
theorem CProject_wellFormed_of_wellFormed {g : GlobalType} {role : String} {lt : LocalTypeR}
    (hproj : CProject g role lt) (hwf : g.wellFormed = true) :
    LocalTypeR.WellFormed lt := by
  have hne : g.allCommsNonEmpty = true := by
    simp only [GlobalType.wellFormed, Bool.and_eq_true] at hwf
    exact hwf.1.1.2
  have htrans : Trans.trans g role = lt := trans_eq_of_CProject g role lt hproj hne
  have hWFtrans : LocalTypeR.WellFormed (Trans.trans g role) :=
    Choreography.Projection.Trans.trans_wellFormed_of_wellFormed g role hwf
  simpa [htrans] using hWFtrans

/-- Left endpoint of CProjectTransRel is well-formed. -/
theorem CProjectTransRel_wf_left {a b : LocalTypeR} (h : CProjectTransRel a b) :
    LocalTypeR.WellFormed a := by
  rcases h with ⟨g, role, hproj, _htrans, hwf⟩
  exact CProject_wellFormed_of_wellFormed (g := g) (role := role) (lt := a) hproj hwf

/-- Right endpoint of CProjectTransRel is well-formed. -/
theorem CProjectTransRel_wf_right {a b : LocalTypeR} (h : CProjectTransRel a b) :
    LocalTypeR.WellFormed b := by
  rcases h with ⟨g, role, _hproj, htrans, hwf⟩
  have hWF := trans_wellFormed_of_wellFormed g role hwf
  simpa [htrans] using hWF

/-- Composition witness: extends CProjectTransRel with EQ2 transitivity.

    This is needed for the mu case where we have:
    - EQ2 (lbody.unfold) (.mu v lbody) from EQ2_refl
    - CProjectTransRel (.mu v lbody) (.mu v (trans gbody role))
    - EQ2 (.mu v (trans gbody role)) ((trans gbody role).unfold) from EQ2_refl

    The composition allows chaining these through intermediates:
    - 2-hop: EQ2 → CProjectTransRel or CProjectTransRel → EQ2
    - 3-hop: EQ2 → CProjectTransRel → EQ2 (for unfolded-to-unfolded chains) -/
def CProjectTransRelComp : Rel := fun a c =>
  CProjectTransRel a c ∨
  (∃ b, EQ2 a b ∧ CProjectTransRel b c) ∨
  (∃ b, CProjectTransRel a b ∧ EQ2 b c) ∨
  (∃ b b', EQ2 a b ∧ CProjectTransRel b b' ∧ EQ2 b' c)

/-- Well-formed variant of CProjectTransRelComp (tracks LocalTypeR.WellFormed endpoints). -/
def CProjectTransRelCompWF : Rel := fun a c =>
  CProjectTransRelComp a c ∧ LocalTypeR.WellFormed a ∧ LocalTypeR.WellFormed c

/-- Lift a base CProjectTransRel witness into the well-formed composition wrapper. -/
theorem CProjectTransRelCompWF_of_CProjectTransRel {a c : LocalTypeR}
    (h : CProjectTransRel a c) : CProjectTransRelCompWF a c := by
  -- Lift a base CProjectTransRel witness into the well-formed composition wrapper.
  have hWFa : LocalTypeR.WellFormed a := CProjectTransRel_wf_left h
  have hWFc : LocalTypeR.WellFormed c := CProjectTransRel_wf_right h
  exact ⟨Or.inl h, hWFa, hWFc⟩

private theorem allCommsNonEmpty_of_mem_branch
    (gbs : List (Label × GlobalType)) (label : Label) (cont : GlobalType)
    (hmem : (label, cont) ∈ gbs)
    (hwf : allCommsNonEmptyBranches gbs = true) :
    cont.allCommsNonEmpty = true := by
  induction gbs with
  | nil => cases hmem
  | cons head tail ih =>
      simp only [allCommsNonEmptyBranches, Bool.and_eq_true] at hwf
      cases hmem with
      | head => exact hwf.1
      | tail _ htail => exact ih htail hwf.2

/- Helper: BranchesProjRel implies transBranches produces branch-wise related pairs.
    Requires wellFormedness of branch continuations to build CProjectTransRel witnesses. -/
theorem branchesProjRel_to_branchesRel_CProjectTransRel
    (gbs : List (Label × GlobalType)) (role : String)
    (lbs : List BranchR)
    (h : BranchesProjRel CProject gbs role lbs) (hwf : ∀ gb, gb ∈ gbs → gb.2.wellFormed = true) :
    BranchesRel CProjectTransRel lbs (transBranches gbs role) := by
  induction h with
  | nil => simp [BranchesRel, transBranches]
  | cons hpair _hrest ih =>
      rename_i gb lb gbs_tail lbs_tail
      cases gb with
      | mk gLabel gCont =>
          obtain ⟨lLabel, lVt, lCont⟩ := lb
          simp only [transBranches, BranchesRel]
          constructor
          · -- Pair relation: labels match and continuations are in CProjectTransRel
            constructor
            · -- Labels match
              exact hpair.1.symm
            · -- CProjectTransRel lCont (trans gCont role)
              have hwf_cont : gCont.wellFormed = true := by
                exact hwf (gLabel, gCont) (by simp)
              exact ⟨gCont, role, hpair.2.2, rfl, hwf_cont⟩
          · -- Tail relation
            have hwf_tail : ∀ gb', gb' ∈ gbs_tail → gb'.2.wellFormed = true := by
              intro gb' hmem
              exact hwf gb' (List.mem_cons_of_mem _ hmem)
            exact ih hwf_tail


theorem CProjectTransRel_postfix_mu_closure
    {v : String} {lbody t' : LocalTypeR}
    (hmu_rel : CProjectTransRel (LocalTypeR.mu v lbody) (LocalTypeR.mu v t')) :
    EQ2F (EQ2_closure CProjectTransRelComp) (LocalTypeR.mu v lbody) (LocalTypeR.mu v t') := by
  -- Build EQ2_closure witnesses using EQ2_refl on both mu sides.
  simp [EQ2F, EQ2_closure]
  have heq_unfold_left : EQ2 ((LocalTypeR.mu v lbody).unfold) (LocalTypeR.mu v lbody) := by
    have hrefl := EQ2_refl (LocalTypeR.mu v lbody)
    exact (EQ2.destruct hrefl).1
  have heq_unfold_right : EQ2 (LocalTypeR.mu v t') ((LocalTypeR.mu v t').unfold) := by
    have hrefl := EQ2_refl (LocalTypeR.mu v t')
    exact (EQ2.destruct hrefl).2
  constructor
  · left; right; left
    exact ⟨LocalTypeR.mu v lbody, heq_unfold_left, hmu_rel⟩
  · left; right; right; left
    exact ⟨LocalTypeR.mu v t', hmu_rel, heq_unfold_right⟩

theorem CProjectTransRel_postfix_end
    {role : String} {t : LocalTypeR}
    (htrans : t = Trans.trans GlobalType.end role) :
    EQ2F (EQ2_closure CProjectTransRelComp) LocalTypeR.end t := by
  -- Reduce by rewriting the trans target.
  subst htrans
  simp [Trans.trans, EQ2F]

theorem CProjectTransRel_postfix_var
    {vt vlt : String} {role : String} {t : LocalTypeR}
    (hf : CProjectF CProject (GlobalType.var vt) role (LocalTypeR.var vlt))
    (htrans : t = Trans.trans (GlobalType.var vt) role) :
    EQ2F (EQ2_closure CProjectTransRelComp) (LocalTypeR.var vlt) t := by
  -- Use CProjectF to identify the variable and reduce trans.
  simp [CProjectF] at hf
  subst htrans hf
  simp [Trans.trans, EQ2F]

/-- Helper: guarded mu/mu case for CProjectTransRel_postfix_mu_mu. -/
private theorem CProjectTransRel_postfix_mu_mu_guarded
    {muvar : String} {gbody : GlobalType} {lbody t : LocalTypeR} {role : String}
    (hbody_proj : CProject gbody role lbody)
    (hguard : lbody.isGuarded muvar = true)
    (htrans : t = Trans.trans (GlobalType.mu muvar gbody) role)
    (hwf : (GlobalType.mu muvar gbody).wellFormed = true)
    (hne : (GlobalType.mu muvar gbody).allCommsNonEmpty = true) :
    EQ2F (EQ2_closure CProjectTransRelComp) (LocalTypeR.mu muvar lbody) t := by
  -- Compute trans for mu and wrap via the mu closure helper.
  have hwf_body : gbody.allCommsNonEmpty = true := by
    simpa [GlobalType.allCommsNonEmpty] using hne
  have htrans_guard : (Trans.trans gbody role).isGuarded muvar = true :=
    CProject_isGuarded_trans hbody_proj hwf_body hguard
  have htrans_mu :
      Trans.trans (GlobalType.mu muvar gbody) role =
        LocalTypeR.mu muvar (Trans.trans gbody role) := by
    simp [Trans.trans, htrans_guard]
  have hmu_rel :
      CProjectTransRel (LocalTypeR.mu muvar lbody)
        (LocalTypeR.mu muvar (Trans.trans gbody role)) := by
    -- Package CProject with the concrete trans equality.
    have hmu_proj :
        CProject (GlobalType.mu muvar gbody) role (LocalTypeR.mu muvar lbody) :=
      CProject_mu muvar gbody lbody role hguard hbody_proj
    exact ⟨GlobalType.mu muvar gbody, role, hmu_proj, htrans_mu.symm, hwf⟩
  subst htrans
  simpa [htrans_mu] using CProjectTransRel_postfix_mu_closure hmu_rel

theorem CProjectTransRel_postfix_mu_mu
    {muvar ltvar : String} {gbody : GlobalType} {lbody t : LocalTypeR} {role : String}
    (hproj : CProject (GlobalType.mu muvar gbody) role (LocalTypeR.mu ltvar lbody))
    (htrans : t = Trans.trans (GlobalType.mu muvar gbody) role)
    (hwf : (GlobalType.mu muvar gbody).wellFormed = true)
    (hne : (GlobalType.mu muvar gbody).allCommsNonEmpty = true)
    (hf : CProjectF CProject (GlobalType.mu muvar gbody) role (LocalTypeR.mu ltvar lbody)) :
    EQ2F (EQ2_closure CProjectTransRelComp) (LocalTypeR.mu ltvar lbody) t := by
  -- Use the guarded mu branch and lift to EQ2_closure via mu refls.
  simp only [CProjectF] at hf
  rcases hf with ⟨candBody, hbody_proj, hcase⟩
  rcases hcase with ⟨hguard, hmu_eq⟩ | ⟨_hguard, hend_eq⟩
  · -- Guarded case: rewrite lbody and defer to the helper.
    cases hmu_eq
    exact CProjectTransRel_postfix_mu_mu_guarded hbody_proj hguard htrans hwf hne
  · -- Unguarded case contradicts the mu candidate.
    have : False := by simpa using hend_eq
    exact this.elim

theorem CProjectTransRel_postfix_mu_end
    {muvar : String} {gbody : GlobalType} {t : LocalTypeR} {role : String}
    (_hproj : CProject (GlobalType.mu muvar gbody) role LocalTypeR.end)
    (htrans : t = Trans.trans (GlobalType.mu muvar gbody) role)
    (hne : (GlobalType.mu muvar gbody).allCommsNonEmpty = true)
    (hf : CProjectF CProject (GlobalType.mu muvar gbody) role LocalTypeR.end) :
    EQ2F (EQ2_closure CProjectTransRelComp) LocalTypeR.end t := by
  -- Use the unguarded mu branch to reduce trans to .end.
  simp only [CProjectF] at hf
  rcases hf with ⟨candBody, hbody_proj, hcase⟩
  rcases hcase with ⟨_hguard, hmu_eq⟩ | ⟨hguard, hend_eq⟩
  ·
    have : False := by simpa using hmu_eq
    exact this.elim
  ·
    cases hend_eq
    have htrans_guard : (Trans.trans gbody role).isGuarded muvar = false :=
      CProject_unguarded_trans hbody_proj
        (by simpa [GlobalType.allCommsNonEmpty] using hne) hguard
    have htrans_end : Trans.trans (GlobalType.mu muvar gbody) role = LocalTypeR.end := by
      simp [Trans.trans, htrans_guard]
    subst htrans
    simpa [htrans_end, EQ2F]

end Choreography.Projection.Project
