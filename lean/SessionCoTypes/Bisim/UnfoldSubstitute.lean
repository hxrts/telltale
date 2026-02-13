import SessionCoTypes.Bisim.Substitution

/-! # SessionCoTypes.Bisim.UnfoldSubstitute

Proves unfold_substitute_EQ2_via_Bisim: unfolding and substituting commute up to EQ2.
-/

/-
The Problem. Unfolding and substituting don't commute exactly, but we need them
to commute up to EQ2: (t.substitute var repl).unfold ≈ (t.unfold).substitute var repl.
This is essential for reasoning about recursive type unfolding.

Solution Structure. Defines `SubstUnfoldRel` as a witness relation pairing
corresponding terms. For non-mu types, unfold is identity so the relation reduces
to Bisim. For mu types, uses the mu unfolding equation. `SubstUnfoldClosure`
extends the relation with Bisim for reflexive cases. Proves both sides satisfy
BisimF, yielding the commutation lemma.
-/

set_option linter.dupNamespace false
set_option linter.unnecessarySimpa false

-- Core Development

namespace SessionCoTypes.Bisim
open SessionTypes.LocalTypeR
open SessionTypes.GlobalType
open SessionCoTypes.Observable
open SessionCoTypes.EQ2
open SessionCoTypes.CoinductiveRel
/-! ## Phase 5: Unfold/Substitute Commutation

The goal is to prove `unfold_substitute_EQ2`:
  EQ2 ((t.substitute var repl).unfold) ((t.unfold).substitute var repl)

This eliminates the `unfold_substitute_EQ2` dependency. -/

/-- Witness relation for unfold/substitute commutation.
    Related pairs are: (a.substitute var repl).unfold and (a.unfold).substitute var repl -/
def SubstUnfoldRel (var : String) (repl : LocalTypeR) :
    LocalTypeR → LocalTypeR → Prop :=
  fun u v => ∃ t : LocalTypeR, LocalTypeR.WellFormed t ∧
    u = (t.substitute var repl).unfold ∧ v = (t.unfold).substitute var repl

/-- For non-mu types, unfold is the identity. -/
theorem unfold_non_mu {t : LocalTypeR} (h : ∀ x body, t ≠ .mu x body) :
    t.unfold = t := by
  cases t with
  | «end» => rfl
  | send _ _ => rfl
  | recv _ _ => rfl
  | mu x body => exact absurd rfl (h x body)
  | var _ => rfl

/-- For mu types, unfold performs substitution. -/
theorem unfold_mu (x : String) (body : LocalTypeR) :
    (LocalTypeR.mu x body).unfold = body.substitute x (.mu x body) := rfl

/-- Closure of SubstUnfoldRel including Bisim for reflexive cases.
    This is needed because SubstUnfoldRel is not reflexive, but for send/recv cases
    both sides are identical (unfold is identity on send/recv). -/
def SubstUnfoldClosure (var : String) (repl : LocalTypeR) : Rel :=
  fun u v => SubstUnfoldRel var repl u v ∨ Bisim u v

/-- BranchesRelBisim reflexivity for SubstUnfoldClosure when all branches are well-formed. -/
private theorem BranchesRelBisim_SubstUnfoldClosure_refl (var : String) (repl : LocalTypeR)
    (hWFrepl : LocalTypeR.WellFormed repl)
    (bs : List BranchR) (hWFbs : ∀ lb ∈ bs, LocalTypeR.WellFormed lb.2.2) :
    BranchesRelBisim (SubstUnfoldClosure var repl)
      (substituteBranches bs var repl)
      (substituteBranches bs var repl) := by
  induction bs with
  | nil => exact List.Forall₂.nil
  | cons b rest ih =>
      constructor
      · exact ⟨rfl, Or.inr (Bisim_refl (b.2.2.substitute var repl)
          (WellFormed_substitute var (hWFbs b (List.Mem.head _)) hWFrepl))⟩
      · exact ih (fun lb hm => hWFbs lb (List.Mem.tail _ hm))

-- Postfix Construction for `SubstUnfoldClosure`

/-- SubstUnfoldClosure is a post-fixpoint of BisimF.
    This is the key lemma for proving unfold_substitute_EQ2. -/
theorem SubstUnfoldClosure_postfix (var : String) (repl : LocalTypeR)
    (hWFrepl : LocalTypeR.WellFormed repl) :
    ∀ u v, SubstUnfoldClosure var repl u v →
      BisimF (SubstUnfoldClosure var repl) u v := by
  intro u v huv
  cases huv with
  -- Postfix: `SubstUnfoldRel` Branch
  | inl hSubst =>
    -- Case: SubstUnfoldRel var repl u v
    obtain ⟨t, hWFt, hu, hv⟩ := hSubst
    cases t with
    | «end» =>
      simp only [LocalTypeR.substitute, LocalTypeR.unfold] at hu hv
      subst hu hv
      exact BisimF.eq_end UnfoldsToEnd.base UnfoldsToEnd.base
    | var x =>
      simp only [LocalTypeR.substitute, LocalTypeR.unfold] at hu hv
      by_cases heq : x = var
      · -- x = var: LHS = repl.unfold, RHS = repl
        -- Use heq to rewrite x to var without destroying var
        have hbeq : (x == var) = true := by simp [heq]
        simp only [hbeq, ↓reduceIte] at hu hv
        -- hu : u = LocalTypeR.unfold repl, hv : v = repl
        rw [hu, hv]
        -- Goal: BisimF (SubstUnfoldClosure var repl) (LocalTypeR.unfold repl) repl
        -- LocalTypeR.unfold repl and repl are Bisim via EQ2_unfold_left
        have hWFrepl_unfold : LocalTypeR.WellFormed repl.unfold :=
/- ## Structured Block 1 -/
          LocalTypeR.WellFormed.unfold (t := repl) hWFrepl
        have hBisim : Bisim (LocalTypeR.unfold repl) repl :=
          EQ2.toBisim (EQ2_unfold_left (EQ2_refl repl)) hWFrepl_unfold hWFrepl
        obtain ⟨R', hR'post, hxy⟩ := hBisim
        have hf : BisimF R' (LocalTypeR.unfold repl) repl :=
          hR'post (LocalTypeR.unfold repl) repl hxy
        -- Lift R' ⊆ SubstUnfoldClosure via Or.inr (Bisim)
        have hR'_to_closure : ∀ a b, R' a b → SubstUnfoldClosure var repl a b :=
          fun a b h => Or.inr ⟨R', hR'post, h⟩
        exact BisimF.mono hR'_to_closure (LocalTypeR.unfold repl) repl hf
      · -- x ≠ var: both sides are .var x
        have hne : (x == var) = false := by simp [heq]
        simp only [hne] at hu hv
        subst hu hv
        exact BisimF.eq_var UnfoldsToVar.base UnfoldsToVar.base
    | send p bs =>
      -- t = .send p bs: both sides are .send p (substituteBranches bs var repl)
      simp only [LocalTypeR.substitute, LocalTypeR.unfold] at hu hv
      subst hu hv
      apply BisimF.eq_send CanSend.base CanSend.base
      exact BranchesRelBisim_SubstUnfoldClosure_refl var repl hWFrepl bs
        (LocalTypeR.WellFormed.branches_of_send (p := p) (bs := bs) hWFt)
    | recv p bs =>
      -- t = .recv p bs: both sides are .recv p (substituteBranches bs var repl)
      simp only [LocalTypeR.substitute, LocalTypeR.unfold] at hu hv
      subst hu hv
      apply BisimF.eq_recv CanRecv.base CanRecv.base
      exact BranchesRelBisim_SubstUnfoldClosure_refl var repl hWFrepl bs
        (LocalTypeR.WellFormed.branches_of_recv (p := p) (bs := bs) hWFt)
    -- Postfix: `SubstUnfoldRel` Mu Case
    | mu x body =>
      -- t = .mu x body: the complex case
      -- LHS: ((.mu x body).substitute var repl).unfold
      -- RHS: ((.mu x body).unfold).substitute var repl
      simp only [LocalTypeR.unfold] at hu hv
      by_cases hshadow : x = var
      -- Postfix: Mu Case with Shadowing (`x = var`)
      · -- x = var: substitution is shadowed
        -- Use hshadow : x = var to rewrite x occurrences
        have hsame : (x == var) = true := by simp [hshadow]
        simp only [LocalTypeR.substitute, hsame, ↓reduceIte] at hu
        -- LHS = (.mu x body).unfold = body.substitute x (.mu x body)
        -- RHS = (body.substitute x (.mu x body)).substitute var repl
        subst hu hv
        -- Key insight: x is not free in body.substitute x (.mu x body) (isFreeIn_mu_unfold_false)
        have hnotfree : SessionCoTypes.SubstCommBarendregt.isFreeIn x
            (body.substitute x (.mu x body)) = false :=
          isFreeIn_mu_unfold_false body x
        -- Since x = var, we have: (body.substitute x (.mu x body)).substitute var repl
        -- = (body.substitute x (.mu x body)).substitute x repl (using hshadow)
        -- = body.substitute x (.mu x body) (by substitute_not_free)
        have hv_eq_u : (body.substitute x (.mu x body)).substitute var repl =
                       body.substitute x (.mu x body) := by
          rw [← hshadow]  -- Rewrite var to x
          exact SessionCoTypes.SubstCommBarendregt.substitute_not_free _ x repl hnotfree
        rw [hv_eq_u]
        -- Now we need BisimF (SubstUnfoldClosure var repl) u u where u = body.substitute x (.mu x body)
        -- Both sides are equal, use Bisim.refl via EQ2_refl
        have hWF_unfold : LocalTypeR.WellFormed (body.substitute x (.mu x body)) :=
          LocalTypeR.WellFormed.unfold (t := .mu x body) (by simpa using hWFt)
        have hBisim : Bisim (body.substitute x (.mu x body)) (body.substitute x (.mu x body)) :=
          EQ2.toBisim (EQ2_refl _) hWF_unfold hWF_unfold
        obtain ⟨R', hR'post, hxy⟩ := hBisim
        have hf := hR'post _ _ hxy
        have hlift : ∀ a b, R' a b → SubstUnfoldClosure var repl a b :=
          fun a b h => Or.inr ⟨R', hR'post, h⟩
        exact BisimF.mono hlift _ _ hf
      -- Postfix: Mu Case without Shadowing (`x ≠ var`)
/- ## Structured Block 2 -/
      · -- x ≠ var: substitution goes through
        have hdiff : (x == var) = false := by simp [hshadow]
        simp only [LocalTypeR.substitute, hdiff] at hu
        -- LHS = (.mu x (body.substitute var repl)).unfold
        --     = (body.substitute var repl).substitute x (.mu x (body.substitute var repl))
        -- RHS = (body.substitute x (.mu x body)).substitute var repl
        subst hu hv
        -- x ≠ var from hdiff
        have hxne : x ≠ var := by simp only [beq_eq_false_iff_ne] at hdiff; exact hdiff
        -- EQ2_subst_mu_comm gives: EQ2 LHS RHS
        have heq := EQ2_subst_mu_comm body var x repl hxne hWFt
        -- EQ2 implies Bisim (well-formedness from unfold + substitution)
        have hWFmu' : LocalTypeR.WellFormed (.mu x (body.substitute var repl)) :=
          WellFormed_mu_substitute (x := x) (var := var) hWFt hWFrepl
        have hWFx : LocalTypeR.WellFormed
            ((body.substitute var repl).substitute x (.mu x (body.substitute var repl))) :=
          LocalTypeR.WellFormed.unfold (t := .mu x (body.substitute var repl)) hWFmu'
        have hWFy : LocalTypeR.WellFormed ((body.substitute x (.mu x body)).substitute var repl) :=
          WellFormed_substitute (var := var)
            (LocalTypeR.WellFormed.unfold (t := .mu x body) (by simpa using hWFt)) hWFrepl
        have hBisim := EQ2.toBisim heq hWFx hWFy
        -- Extract witness relation from Bisim
        obtain ⟨R', hR'post, hxy⟩ := hBisim
        have hf : BisimF R' _ _ := hR'post _ _ hxy
        -- Lift R' to SubstUnfoldClosure via Bisim inclusion
        have hlift : ∀ a b, R' a b → SubstUnfoldClosure var repl a b :=
          fun a b h => Or.inr ⟨R', hR'post, h⟩
        exact BisimF.mono hlift _ _ hf
  -- Postfix: Existing `Bisim` Branch
  | inr hBisim =>
    -- Case: Bisim u v - use the existing Bisim post-fixpoint property
    obtain ⟨R, hRpost, huv⟩ := hBisim
    have hf : BisimF R u v := hRpost u v huv
    -- Lift R to SubstUnfoldClosure via Bisim inclusion
    have hlift : ∀ a b, R a b → SubstUnfoldClosure var repl a b :=
      fun a b hab => Or.inr ⟨R, hRpost, hab⟩
    exact BisimF.mono hlift u v hf

-- Consequences of the Postfix Construction

/-- SubstUnfoldRel implies Bisim via the closure.

    Once SubstUnfoldClosure_postfix is proven, this follows directly. -/
theorem SubstUnfoldRel_implies_Bisim (var : String) (repl : LocalTypeR)
    (t : LocalTypeR) (hWFt : LocalTypeR.WellFormed t) (hWFrepl : LocalTypeR.WellFormed repl) :
    Bisim ((t.substitute var repl).unfold) ((t.unfold).substitute var repl) := by
  use SubstUnfoldClosure var repl
  constructor
  · exact SubstUnfoldClosure_postfix var repl hWFrepl
  · exact Or.inl ⟨t, hWFt, rfl, rfl⟩

/-- EQ2 ((t.substitute var repl).unfold) ((t.unfold).substitute var repl).

    This eliminates the unfold_substitute_EQ2 dependency.

    Proof: SubstUnfoldRel is in SubstUnfoldClosure which is a bisimulation,
    so the pair is in Bisim, and Bisim.toEQ2 gives us EQ2. -/
theorem unfold_substitute_EQ2_via_Bisim (t : LocalTypeR) (var : String) (repl : LocalTypeR)
    (hWFt : LocalTypeR.WellFormed t) (hWFrepl : LocalTypeR.WellFormed repl) :
    EQ2 ((t.substitute var repl).unfold) ((t.unfold).substitute var repl) := by
  have hBisim := SubstUnfoldRel_implies_Bisim var repl t hWFt hWFrepl
  exact Bisim.toEQ2 hBisim

end SessionCoTypes.Bisim
