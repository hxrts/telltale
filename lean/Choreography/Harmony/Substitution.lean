import Choreography.Harmony.StepHarmony

/-! # Choreography.Harmony.Substitution

Substitution commutation: projection commutes with substitution via paco coinduction.
-/

/-
The Problem. State the projection/harmony lemma objective and the exact invariant boundary it preserves.
Solution Structure. Introduce local helper lemmas first, then discharge the main theorem by case analysis over the operational/projection relation.
-/

namespace Choreography.Harmony
/-! ## Substitution Commutation -/

open SessionCoTypes.EQ2Paco
open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
open SessionCoTypes.EQ2
open Choreography.Projection.Trans (trans_comm_sender trans_comm_receiver trans_comm_other)

/-- Witness relation for trans_subst_comm: pairs arising from projection-substitution. -/
private def ProjSubstRel (t : String) (G : GlobalType) (role : String) : Rel := fun a b =>
  ∃ g : GlobalType,
    a = projTrans (g.substitute t G) role ∧
    b = (projTrans g role).substitute t (projTrans G role)

/-! ## Remaining Lemmas for Legacy Gaps

The following lemmas capture the semantic properties needed for the remaining cases.
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
    (hL : (Choreography.Projection.Trans.trans (inner.substitute t G) role).isGuarded s = true)
    (hR_pre : (Choreography.Projection.Trans.trans inner role).isGuarded s = true) :
    EQ2 ((Choreography.Projection.Trans.trans (inner.substitute t G) role).substitute s
           (.mu s (Choreography.Projection.Trans.trans (inner.substitute t G) role)))
        (.mu s ((Choreography.Projection.Trans.trans inner role).substitute t
                 (Choreography.Projection.Trans.trans G role))) :=
  MuUnfoldLemmas.EQ2_mu_crossed_unfold_left' hGclosed hL hR_pre

/-- Mu-mu crossed unfold: left mu relates to right unfold.

Symmetric to `EQ2_mu_crossed_unfold_left`.

**Proof:** Uses `proj_subst` to rewrite, then applies `EQ2_mu_to_unfold`.

**Proven in:** MuUnfoldLemmas.lean -/
private theorem EQ2_mu_crossed_unfold_right
    {s t : String} {inner G : GlobalType} {role : String}
    (hGclosed : G.isClosed = true)
    (hL : (Choreography.Projection.Trans.trans (inner.substitute t G) role).isGuarded s = true)
    (hR_pre : (Choreography.Projection.Trans.trans inner role).isGuarded s = true) :
    EQ2 (.mu s (Choreography.Projection.Trans.trans (inner.substitute t G) role))
        (((Choreography.Projection.Trans.trans inner role).substitute t
           (Choreography.Projection.Trans.trans G role)).substitute s
          (.mu s ((Choreography.Projection.Trans.trans inner role).substitute t
                   (Choreography.Projection.Trans.trans G role)))) :=
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
    (hL : (Choreography.Projection.Trans.trans (inner.substitute t G) role).isGuarded s = true)
    (hR_pre : (Choreography.Projection.Trans.trans inner role).isGuarded s = false) :
    EQ2 ((Choreography.Projection.Trans.trans (inner.substitute t G) role).substitute s
           (.mu s (Choreography.Projection.Trans.trans (inner.substitute t G) role)))
        .end :=
  MuUnfoldLemmas.EQ2_mu_unguarded_to_end' hsne hGclosed hL hR_pre

/-- Mismatched guardedness: end relates to guarded mu unfold.

Symmetric to `EQ2_mu_unguarded_to_end`.

**Status:** PROVEN (vacuously true when G is closed, from MuUnfoldLemmas.lean). -/
private theorem EQ2_end_to_mu_unguarded
    {s t : String} {inner G : GlobalType} {role : String}
    (hGclosed : G.isClosed = true)
    (hL_pre : (Choreography.Projection.Trans.trans (inner.substitute t G) role).isGuarded s = false)
    (hR : (Choreography.Projection.Trans.trans inner role).isGuarded s = true) :
    EQ2 .end
        (((Choreography.Projection.Trans.trans inner role).substitute t
          (Choreography.Projection.Trans.trans G role)).substitute s
         (.mu s ((Choreography.Projection.Trans.trans inner role).substitute t
                  (Choreography.Projection.Trans.trans G role)))) :=
  MuUnfoldLemmas.EQ2_end_to_mu_unguarded' hGclosed hL_pre hR

-- Aliases to avoid namespace issues
private abbrev gSubstBranches := SessionTypes.GlobalType.substituteBranches -- global branch subst
private abbrev lSubstBranches := SessionTypes.LocalTypeR.substituteBranches -- local branch subst
private abbrev projTransBranches := Choreography.Projection.Trans.transBranches

private theorem sizeOf_head_snd_lt_cons (pair : Label × GlobalType)
    (rest : List (Label × GlobalType)) :
    sizeOf pair.2 < sizeOf (pair :: rest) := by
  -- Compare sizeOf via the pair and then the cons.
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
  -- comm adds a constructor on top of the branch list size.
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
      (projTransBranches (gSubstBranches branches t G) role)
      (lSubstBranches (projTransBranches branches role) t (projTrans G role)) := by
  induction branches with
  | nil =>
      simp [BranchesRel, gSubstBranches, lSubstBranches, projTransBranches,
        Choreography.Projection.Trans.transBranches,
        SessionTypes.GlobalType.substituteBranches,
        SessionTypes.LocalTypeR.substituteBranches,
        -SessionTypes.LocalTypeR.substituteBranches_eq_map]
  | cons hd tl ih =>
      obtain ⟨label, cont⟩ := hd
      simp [BranchesRel, gSubstBranches, lSubstBranches, projTransBranches,
        Choreography.Projection.Trans.transBranches,
        SessionTypes.GlobalType.substituteBranches,
        SessionTypes.LocalTypeR.substituteBranches,
        -SessionTypes.LocalTypeR.substituteBranches_eq_map]
      constructor
      · -- head relation
        exact Or.inl ⟨cont, rfl, rfl⟩
      ·
        simpa [BranchesRel, gSubstBranches, lSubstBranches, projTransBranches,
          Choreography.Projection.Trans.transBranches,
          SessionTypes.GlobalType.substituteBranches,
          SessionTypes.LocalTypeR.substituteBranches,
          -SessionTypes.LocalTypeR.substituteBranches_eq_map] using ih

/-- Helper: EQ2F for projection-substitution on `.end`. -/
private theorem ProjSubstRel_EQ2F_end (t : String) (G : GlobalType) (role : String) :
    EQ2F (fun x y => ProjSubstRel t G role x y ∨ EQ2 x y)
      (projTrans (GlobalType.end.substitute t G) role)
      ((projTrans GlobalType.end role).substitute t (projTrans G role)) := by
  -- Both sides reduce to `.end`.
  simp [GlobalType.substitute, projTrans, Choreography.Projection.Trans.trans, EQ2F]

/-- Helper: EQ2F for projection-substitution on `.var`. -/
private theorem ProjSubstRel_EQ2F_var (v t : String) (G : GlobalType) (role : String) :
    EQ2F (fun x y => ProjSubstRel t G role x y ∨ EQ2 x y)
      (projTrans ((GlobalType.var v).substitute t G) role)
      ((projTrans (GlobalType.var v) role).substitute t (projTrans G role)) := by
  -- Split on whether the variable is the substitution target.
  by_cases hvt : v = t
  · subst hvt
    simp [GlobalType.substitute, projTrans, Choreography.Projection.Trans.trans]
    exact EQ2F.mono (fun _ _ h => Or.inr h) _ _ (EQ2.destruct (EQ2_refl _))
  · have hvt' : (v == t) = false := beq_eq_false_iff_ne.mpr hvt
    simp [GlobalType.substitute, projTrans, Choreography.Projection.Trans.trans, hvt']
    rfl

/-- Helper: mu case with shadowed substitution (s = t). -/
private theorem ProjSubstRel_EQ2F_mu_shadow
    (s t : String) (inner G : GlobalType) (role : String) (hst : s = t) :
    EQ2F (fun x y => ProjSubstRel t G role x y ∨ EQ2 x y)
      (projTrans ((GlobalType.mu s inner).substitute t G) role)
      ((projTrans (GlobalType.mu s inner) role).substitute t (projTrans G role)) := by
  -- Substitution is shadowed; both sides project the same mu.
  have hst' : (s == t) = true := by
    simpa [beq_iff_eq] using hst
  simp [GlobalType.substitute, hst', projTrans, Choreography.Projection.Trans.trans]
  by_cases hguard : (Choreography.Projection.Trans.trans inner role).isGuarded s = true
  ·
    have hguard_t : (Choreography.Projection.Trans.trans inner role).isGuarded t = true := by
      simpa [hst] using hguard
    have hF : EQ2F EQ2
        (LocalTypeR.mu s (Choreography.Projection.Trans.trans inner role))
        (LocalTypeR.mu s (Choreography.Projection.Trans.trans inner role)) :=
      EQ2.destruct (EQ2_refl _)
    have hF' : EQ2F (fun x y => ProjSubstRel t G role x y ∨ EQ2 x y)
        (LocalTypeR.mu s (Choreography.Projection.Trans.trans inner role))
        (LocalTypeR.mu s (Choreography.Projection.Trans.trans inner role)) :=
      EQ2F.mono (fun _ _ h => Or.inr h) _ _ hF
    simpa [hguard_t, LocalTypeR.substitute, hst] using hF'
  · simp [hguard, EQ2F]

/-- Helper: mu case, s ≠ t, both projections guarded. -/
private theorem ProjSubstRel_EQ2F_mu_noshadow_guarded
    (s t : String) (inner G : GlobalType) (role : String)
    (hsne : s ≠ t) (hGclosed : G.isClosed = true)
    (hguardL : (Choreography.Projection.Trans.trans (inner.substitute t G) role).isGuarded s = true)
    (hguardR : (Choreography.Projection.Trans.trans inner role).isGuarded s = true) :
    EQ2F (fun x y => ProjSubstRel t G role x y ∨ EQ2 x y)
      (projTrans (GlobalType.mu s (inner.substitute t G)) role)
      ((projTrans (GlobalType.mu s inner) role).substitute t (projTrans G role)) := by
  -- Both sides are guarded mu; relate via crossed unfold lemmas.
  simp [projTrans, Choreography.Projection.Trans.trans, hguardL, hguardR]
  simp [LocalTypeR.substitute, beq_eq_false_iff_ne.mpr hsne]
  constructor
  · exact Or.inr (EQ2_mu_crossed_unfold_left hGclosed hguardL hguardR)
  · exact Or.inr (EQ2_mu_crossed_unfold_right hGclosed hguardL hguardR)

/-- Helper: mu case, s ≠ t, LHS guarded and RHS unguarded. -/
private theorem ProjSubstRel_EQ2F_mu_noshadow_guarded_end
    (s t : String) (inner G : GlobalType) (role : String)
    (hsne : s ≠ t) (hGclosed : G.isClosed = true)
    (hguardL : (Choreography.Projection.Trans.trans (inner.substitute t G) role).isGuarded s = true)
    (hguardR : (Choreography.Projection.Trans.trans inner role).isGuarded s = false) :
    EQ2F (fun x y => ProjSubstRel t G role x y ∨ EQ2 x y)
      (projTrans (GlobalType.mu s (inner.substitute t G)) role)
      ((projTrans (GlobalType.mu s inner) role).substitute t (projTrans G role)) := by
  -- Guarded mu relates to end via the mismatched guardedness lemma.
  simp [projTrans, Choreography.Projection.Trans.trans, hguardL, hguardR]
  exact Or.inr (EQ2_mu_unguarded_to_end hsne hGclosed hguardL hguardR)

/-- Helper: mu case, s ≠ t, LHS unguarded and RHS guarded. -/
private theorem ProjSubstRel_EQ2F_mu_noshadow_end_guarded
    (s t : String) (inner G : GlobalType) (role : String)
    (hsne : s ≠ t) (hGclosed : G.isClosed = true)
    (hguardL : (Choreography.Projection.Trans.trans (inner.substitute t G) role).isGuarded s = false)
    (hguardR : (Choreography.Projection.Trans.trans inner role).isGuarded s = true) :
    EQ2F (fun x y => ProjSubstRel t G role x y ∨ EQ2 x y)
      (projTrans (GlobalType.mu s (inner.substitute t G)) role)
      ((projTrans (GlobalType.mu s inner) role).substitute t (projTrans G role)) := by
  -- End relates to guarded mu via the mismatched guardedness lemma.
  simp [projTrans, Choreography.Projection.Trans.trans, hguardL, hguardR]
  simp [LocalTypeR.substitute, beq_eq_false_iff_ne.mpr hsne]
  exact Or.inr (EQ2_end_to_mu_unguarded hGclosed hguardL hguardR)

/-- Helper: mu case, s ≠ t, both unguarded. -/
private theorem ProjSubstRel_EQ2F_mu_noshadow_end_end
    (s t : String) (inner G : GlobalType) (role : String)
    (_hsne : s ≠ t)
    (hguardL : (Choreography.Projection.Trans.trans (inner.substitute t G) role).isGuarded s = false)
    (hguardR : (Choreography.Projection.Trans.trans inner role).isGuarded s = false) :
    EQ2F (fun x y => ProjSubstRel t G role x y ∨ EQ2 x y)
      (projTrans (GlobalType.mu s (inner.substitute t G)) role)
      ((projTrans (GlobalType.mu s inner) role).substitute t (projTrans G role)) := by
  -- Both sides collapse to end.
  simp [projTrans, Choreography.Projection.Trans.trans, hguardL, hguardR, EQ2F]

/-- Helper: mu case, s ≠ t, dispatch on guardedness. -/
private theorem ProjSubstRel_EQ2F_mu_noshadow
    (s t : String) (inner G : GlobalType) (role : String)
    (hGclosed : G.isClosed = true) (hsne : s ≠ t) :
    EQ2F (fun x y => ProjSubstRel t G role x y ∨ EQ2 x y)
      (projTrans ((GlobalType.mu s inner).substitute t G) role)
      ((projTrans (GlobalType.mu s inner) role).substitute t (projTrans G role)) := by
  -- Split on guardedness of both projections.
  have hst : (s == t) = false := by
    simpa [beq_eq_false_iff_ne] using hsne
  simp [GlobalType.substitute, hst]
  cases hguardL : (Choreography.Projection.Trans.trans (inner.substitute t G) role).isGuarded s with
  | true =>
      cases hguardR : (Choreography.Projection.Trans.trans inner role).isGuarded s with
      | true =>
          exact ProjSubstRel_EQ2F_mu_noshadow_guarded s t inner G role hsne hGclosed hguardL hguardR
      | false =>
          exact ProjSubstRel_EQ2F_mu_noshadow_guarded_end s t inner G role hsne hGclosed hguardL hguardR
  | false =>
      cases hguardR : (Choreography.Projection.Trans.trans inner role).isGuarded s with
      | true =>
          exact ProjSubstRel_EQ2F_mu_noshadow_end_guarded s t inner G role hsne hGclosed hguardL hguardR
      | false =>
          exact ProjSubstRel_EQ2F_mu_noshadow_end_end s t inner G role hsne hguardL hguardR

/-- Helper: comm case when role is sender. -/
private theorem ProjSubstRel_EQ2F_comm_sender
    (sender receiver : String) (branches : List (Label × GlobalType))
    (t : String) (G : GlobalType) (role : String) (hrs : role = sender) :
    EQ2F (fun x y => ProjSubstRel t G role x y ∨ EQ2 x y)
      (projTrans (GlobalType.comm sender receiver (gSubstBranches branches t G)) role)
      ((projTrans (GlobalType.comm sender receiver branches) role).substitute t (projTrans G role)) := by
  -- Sender projection stays send; relate branches via transBranches_ProjSubstRel.
  have hLHS :
      projTrans (GlobalType.comm sender receiver (gSubstBranches branches t G)) role =
        LocalTypeR.send receiver (projTransBranches (gSubstBranches branches t G) role) :=
    trans_comm_sender sender receiver role (gSubstBranches branches t G) hrs
  have hRHS_proj :
      projTrans (GlobalType.comm sender receiver branches) role =
        LocalTypeR.send receiver (projTransBranches branches role) :=
    trans_comm_sender sender receiver role branches hrs
  rw [hLHS, hRHS_proj]
  simp [LocalTypeR.substitute, EQ2F]
  simpa [lSubstBranches, SessionTypes.LocalTypeR.substituteBranches_eq_map] using
    (transBranches_ProjSubstRel t G role branches)

/-- Helper: comm case when role is receiver. -/
private theorem ProjSubstRel_EQ2F_comm_receiver
    (sender receiver : String) (branches : List (Label × GlobalType))
    (t : String) (G : GlobalType) (role : String) (hrr : role = receiver) (hrs : role ≠ sender) :
    EQ2F (fun x y => ProjSubstRel t G role x y ∨ EQ2 x y)
      (projTrans (GlobalType.comm sender receiver (gSubstBranches branches t G)) role)
      ((projTrans (GlobalType.comm sender receiver branches) role).substitute t (projTrans G role)) := by
  -- Receiver projection stays recv; relate branches via transBranches_ProjSubstRel.
  have hLHS :
      projTrans (GlobalType.comm sender receiver (gSubstBranches branches t G)) role =
        LocalTypeR.recv sender (projTransBranches (gSubstBranches branches t G) role) :=
    trans_comm_receiver sender receiver role (gSubstBranches branches t G) hrr hrs
  have hRHS_proj :
      projTrans (GlobalType.comm sender receiver branches) role =
        LocalTypeR.recv sender (projTransBranches branches role) :=
    trans_comm_receiver sender receiver role branches hrr hrs
  rw [hLHS, hRHS_proj]
  simp [LocalTypeR.substitute, EQ2F]
  simpa [lSubstBranches, SessionTypes.LocalTypeR.substituteBranches_eq_map] using
    (transBranches_ProjSubstRel t G role branches)

/-- Helper: comm case, non-participant and empty branches. -/
private theorem ProjSubstRel_EQ2F_comm_other_nil
    (sender receiver : String) (t : String) (G : GlobalType) (role : String)
    (hrs : role ≠ sender) (hrr : role ≠ receiver) :
    EQ2F (fun x y => ProjSubstRel t G role x y ∨ EQ2 x y)
      (projTrans (GlobalType.comm sender receiver (gSubstBranches [] t G)) role)
      ((projTrans (GlobalType.comm sender receiver []) role).substitute t (projTrans G role)) := by
  -- Empty branches: both sides are end.
  have hLHS : projTrans (GlobalType.comm sender receiver (gSubstBranches [] t G)) role = LocalTypeR.end := by
    have h := trans_comm_other sender receiver role (gSubstBranches [] t G) hrs hrr
    simp [gSubstBranches, SessionTypes.GlobalType.substituteBranches] at h
    exact h
  have hRHS_proj : projTrans (GlobalType.comm sender receiver []) role = LocalTypeR.end :=
    trans_comm_other sender receiver role [] hrs hrr
  rw [hLHS, hRHS_proj]
  simp [LocalTypeR.substitute, EQ2F]

/-- Helper: comm case, non-participant and non-empty branches. -/
private theorem ProjSubstRel_EQ2F_comm_other_cons
    (sender receiver : String) (label : Label) (cont : GlobalType) (rest : List (Label × GlobalType))
    (t : String) (G : GlobalType) (role : String) (hrs : role ≠ sender) (hrr : role ≠ receiver)
    (ih :
      EQ2F (fun x y => ProjSubstRel t G role x y ∨ EQ2 x y)
        (projTrans (cont.substitute t G) role)
        ((projTrans cont role).substitute t (projTrans G role))) :
    EQ2F (fun x y => ProjSubstRel t G role x y ∨ EQ2 x y)
      (projTrans (GlobalType.comm sender receiver (gSubstBranches ((label, cont) :: rest) t G)) role)
      ((projTrans (GlobalType.comm sender receiver ((label, cont) :: rest)) role).substitute t (projTrans G role)) := by
  -- Non-participant: follow the first branch and reuse the IH.
  have hLHS :
      projTrans (GlobalType.comm sender receiver (gSubstBranches ((label, cont) :: rest) t G)) role =
        projTrans (cont.substitute t G) role := by
    have h := trans_comm_other sender receiver role (gSubstBranches ((label, cont) :: rest) t G) hrs hrr
    simp [gSubstBranches, SessionTypes.GlobalType.substituteBranches] at h
    exact h
  have hRHS_proj :
      projTrans (GlobalType.comm sender receiver ((label, cont) :: rest)) role =
        projTrans cont role := by
    exact trans_comm_other sender receiver role ((label, cont) :: rest) hrs hrr
  rw [hLHS, hRHS_proj]
  exact ih

/-- Auxiliary: EQ2F holds for projection-substitution pairs, by well-founded induction on GlobalType.

This allows recursive calls on subterms (e.g., comm continuations), which the
simple match-based proof cannot handle. -/
private theorem ProjSubstRel_EQ2F_of_witness (g : GlobalType) (t : String) (G : GlobalType) (role : String)
    (hGclosed : G.isClosed = true) :
    EQ2F (fun x y => ProjSubstRel t G role x y ∨ EQ2 x y) (projTrans (g.substitute t G) role)
      ((projTrans g role).substitute t (projTrans G role)) := by
  match g with
  | .end => exact ProjSubstRel_EQ2F_end t G role
  | .var v => exact ProjSubstRel_EQ2F_var v t G role
  | .mu s inner =>
      by_cases hst : s = t
      · exact ProjSubstRel_EQ2F_mu_shadow s t inner G role hst
      · exact ProjSubstRel_EQ2F_mu_noshadow s t inner G role hGclosed hst
  | .comm sender receiver branches =>
      by_cases hrs : role = sender
      · exact ProjSubstRel_EQ2F_comm_sender sender receiver branches t G role hrs
      · by_cases hrr : role = receiver
        · exact ProjSubstRel_EQ2F_comm_receiver sender receiver branches t G role hrr hrs
        · cases branches with
          | nil => exact ProjSubstRel_EQ2F_comm_other_nil sender receiver t G role hrs hrr
          | cons head rest =>
              cases head with
              | mk label cont =>
                  have ih := ProjSubstRel_EQ2F_of_witness cont t G role hGclosed
                  exact ProjSubstRel_EQ2F_comm_other_cons
                    sender receiver label cont rest t G role hrs hrr ih
termination_by sizeOf g
decreasing_by
  all_goals
    simp_wf; first | simpa [GlobalType.comm.sizeOf_spec] using (sizeOf_cont_lt_comm sender receiver label cont rest)

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

/-- Coinduction witness for `trans_subst_comm`. -/
private theorem trans_subst_comm_paco (g : GlobalType) (t : String) (G : GlobalType) (role : String)
    (hGclosed : G.isClosed = true) :
    Paco.paco EQ2FMono (toPacoRel EQ2)
      (projTrans (g.substitute t G) role)
      ((projTrans g role).substitute t (projTrans G role)) := by
  -- Use paco coinduction with ProjSubstRel as witness and EQ2 as accumulator.
  apply EQ2_paco_coind (ProjSubstRel t G role) EQ2 (ProjSubstRel_postfix t G role hGclosed)
  exact ⟨g, rfl, rfl⟩

/-- Projection commutes with substitution up to EQ2. -/
private theorem trans_subst_comm (g : GlobalType) (t : String) (G : GlobalType) (role : String)
    (hGclosed : G.isClosed = true) :
    EQ2 (projTrans (g.substitute t G) role) ((projTrans g role).substitute t (projTrans G role)) := by
  -- Reduce to the paco witness, then convert to EQ2.
  exact paco_EQ2_to_EQ2 (trans_subst_comm_paco g t G role hGclosed)

/-! ## subst_end_unguarded_eq2_end -/
open Choreography.Harmony.SubstEndUnguarded (subst_end_unguarded_eq2_end)

/-- Projection commutes with mu-substitution up to EQ2.

With the Coq-style `trans` definition:
- `trans (.mu t body) role = if (trans body role).isGuarded t then .mu t (trans body role) else .end`

The key cases:
1. If `(trans body role).isGuarded t = true`: projection produces `.mu t (trans body role)`
   and we use trans_subst_comm to show correspondence
2. If `(trans body role).isGuarded t = false`: projection produces `.end`, and
   substitution also produces `.end` (matching behavior)

Coq reference: This follows from full_eunf_subst in coLocal.v. -/
private theorem trans_substitute_unfold_guarded
    (t : String) (body : GlobalType) (role : String) (hclosed : (GlobalType.mu t body).isClosed = true)
    (hguard : (projTrans body role).isGuarded t = true) :
    EQ2 (projTrans (body.substitute t (GlobalType.mu t body)) role)
        ((projTrans (GlobalType.mu t body) role).unfold) := by
  -- Guarded case: both sides are the unfolded mu, use trans_subst_comm.
  have h_proj_mu : projTrans (.mu t body) role = LocalTypeR.mu t (projTrans body role) := by
    simp [projTrans, Choreography.Projection.Trans.trans, hguard]
  rw [h_proj_mu, LocalTypeR.unfold_mu, ← h_proj_mu]
  exact trans_subst_comm body t (.mu t body) role hclosed

private theorem trans_substitute_unfold_unguarded
    (t : String) (body : GlobalType) (role : String) (hclosed : (GlobalType.mu t body).isClosed = true)
    (hguard : (projTrans body role).isGuarded t = false) :
    EQ2 (projTrans (body.substitute t (GlobalType.mu t body)) role)
        ((projTrans (GlobalType.mu t body) role).unfold) := by
  -- Unguarded case: projection collapses to end, use subst_end_unguarded_eq2_end.
  have h_proj_end : projTrans (.mu t body) role = LocalTypeR.end := by
    simp [projTrans, Choreography.Projection.Trans.trans, hguard]
  rw [h_proj_end]
  simp [LocalTypeR.unfold]
  have hproj_subst :
      projTrans (body.substitute t (.mu t body)) role =
        (projTrans body role).substitute t (projTrans (.mu t body) role) :=
    Choreography.Projection.ProjSubst.proj_subst_mu_self t body role hclosed
  have hproj_subst' :
      projTrans (body.substitute t (.mu t body)) role =
        (projTrans body role).substitute t LocalTypeR.end := by
    simpa [h_proj_end] using hproj_subst
  have hsub_end : EQ2 ((projTrans body role).substitute t LocalTypeR.end) LocalTypeR.end :=
    subst_end_unguarded_eq2_end (projTrans body role) t hguard
  simpa [← hproj_subst'] using hsub_end

/-- Projection commutes with a single mu-unfold (up to EQ2) for closed globals. -/
theorem trans_substitute_unfold (t : String) (body : GlobalType) (role : String)
    (hclosed : (GlobalType.mu t body).isClosed = true) :
    EQ2 (projTrans (body.substitute t (GlobalType.mu t body)) role)
        ((projTrans (GlobalType.mu t body) role).unfold) := by
  -- Case split on whether the projected body is guarded.
  by_cases hguard : (projTrans body role).isGuarded t = true
  · exact trans_substitute_unfold_guarded t body role hclosed hguard
  · have hguard' : (projTrans body role).isGuarded t = false := by
      cases h : (projTrans body role).isGuarded t with
      | true => exact (False.elim (hguard h))
      | false => rfl
    exact trans_substitute_unfold_unguarded t body role hclosed hguard'

end Choreography.Harmony
