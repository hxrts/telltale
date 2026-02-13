import Mathlib
import Paco
import SessionCoTypes.Coinductive.Observable
import SessionCoTypes.Coinductive.EQ2C
import SessionCoTypes.Coinductive.EQ2CProps
import SessionCoTypes.Coinductive.EQ2CPaco
import SessionCoTypes.Coinductive.BisimDecidable

set_option linter.dupNamespace false

/-! # EQ2CMu

Mu-aware paco equality step and bounded unfolding helpers.
-/

/-
The Problem. Standard EQ2C requires observable steps on both sides simultaneously.
When one side has a mu-wrapping, we need to unfold it first. The mu-aware variant
allows unfolding on either side before requiring an observable match.

Solution Structure. Defines `EQ2C_mu_step` generator that either takes an observable
step or unfolds mu on either side. `EQ2C_mu_paco` is the greatest fixed point.
Proves `EQ2C_paco_le_mu` showing observable-step EQ2C is contained in mu-aware EQ2C.
The converse `EQ2C_mu_paco_eq_paco` shows they coincide for observable types.
-/

namespace SessionCoTypes.Coinductive

/-- One-step mu-aware generator: either take an observable step, or unfold μ on either side. -/
inductive EQ2C_mu_step (R : LocalTypeC → LocalTypeC → Prop) (a b : LocalTypeC) : Prop
  | obs (h : ObservableRelC R a b) : EQ2C_mu_step R a b
  | mu_left  {a'} (hstep : UnfoldsC a a') (hrel : R a' b) : EQ2C_mu_step R a b
  | mu_right {b'} (hstep : UnfoldsC b b') (hrel : R a b') : EQ2C_mu_step R a b

lemma EQ2C_mu_step_mono : Paco.Monotone2 EQ2C_mu_step := by
  intro R S h a b hstep
  cases hstep with
  | obs hobs => exact EQ2C_mu_step.obs (ObservableRelC_mono (fun _ _ hr => h _ _ hr) hobs)
  | mu_left hstep hrel => exact EQ2C_mu_step.mu_left hstep (h _ _ hrel)
  | mu_right hstep hrel => exact EQ2C_mu_step.mu_right hstep (h _ _ hrel)

/-- Mu-aware paco transformer. -/
def EQ2CMuMono : Paco.MonoRel LocalTypeC where
  F := EQ2C_mu_step
  mono := EQ2C_mu_step_mono

/-- Mu-aware paco equality. -/
def EQ2C_mu_paco : LocalTypeC → LocalTypeC → Prop :=
  Paco.paco EQ2CMuMono ⊥

/-- Observable-step generator is included in mu-step generator. -/
lemma EQ2C_step_paco_le_mu (R : LocalTypeC → LocalTypeC → Prop) :
    EQ2C_step_paco R ≤ EQ2C_mu_step R := by
  intro a b h
  rcases h with ⟨obs_a, obs_b, hrel⟩
  exact EQ2C_mu_step.obs hrel

/-- EQ2C_paco is contained in EQ2C_mu_paco (easy direction). -/
lemma EQ2C_paco_le_mu : EQ2C_paco ≤ EQ2C_mu_paco := by
  -- paco is monotone in the generator
  have hF : ∀ R, EQ2CMono.F R ≤ EQ2CMuMono.F R := by
    intro R a b hstep
    exact EQ2C_step_paco_le_mu R a b hstep
  exact Paco.paco_mon_F EQ2CMono EQ2CMuMono ⊥ hF

-- From mu-step paco to observable steps (bounded unfolding)

private lemma fullUnfoldN_succ_of_unfoldsC {a a' : LocalTypeC} (hstep : UnfoldsC a a') :
    ∀ n, fullUnfoldN (n + 1) a = fullUnfoldN n a' := by
  intro n
  rcases hstep with ⟨x, f, hdest, rfl⟩
  simp [fullUnfoldN, hdest]

private lemma hasNonMuHead_fullUnfoldN_succ_of_unfoldsC {a a' : LocalTypeC}
    (hstep : UnfoldsC a a') {n : Nat}
    (h : hasNonMuHead (fullUnfoldN (n + 1) a) = true) :
    hasNonMuHead (fullUnfoldN n a') = true := by
  simpa [fullUnfoldN_succ_of_unfoldsC hstep] using h


/-- If both sides reach a non-μ head within bounds, mu-step paco yields an observable relation. -/
lemma EQ2C_mu_paco_to_obs_of_bounds {a b : LocalTypeC} {na nb : Nat}
    (ha : hasNonMuHead (fullUnfoldN na a) = true)
    (hb : hasNonMuHead (fullUnfoldN nb b) = true)
    (h : EQ2C_mu_paco a b) :
    ObservableRelC EQ2C_mu_paco a b := by
  classical
  -- Bounded-to-Observable Reduction
  -- Induct on the combined unfolding budget.
  have aux :
      ∀ n {a b : LocalTypeC} {na nb : Nat},
        na + nb = n →
        hasNonMuHead (fullUnfoldN na a) = true →
        hasNonMuHead (fullUnfoldN nb b) = true →
        EQ2C_mu_paco a b →
        ObservableRelC EQ2C_mu_paco a b := by
    intro n
    induction n with
    -- Bounds Induction: Base Case
    | zero =>
        intro a b na nb hsum ha hb hmu
        -- na = 0 and nb = 0
        rcases Nat.add_eq_zero_iff.mp hsum with ⟨hna, hnb⟩
        subst hna
        subst hnb
        have hstep := Paco.paco_unfold EQ2CMuMono ⊥ a b hmu
        have hstep' : EQ2C_mu_step EQ2C_mu_paco a b := by
          simpa only [Paco.upaco_bot] using hstep
        cases hstep' with
        | obs hobs => exact hobs
        | mu_left hstep _ =>
            rcases hstep with ⟨x, f, hdest, rfl⟩
            have hnonmu : hasNonMuHead a = true := by
              simpa [fullUnfoldN] using ha
            have : False := by simp [hasNonMuHead, head, hdest] at hnonmu
            cases this
        | mu_right hstep _ =>
            rcases hstep with ⟨x, f, hdest, rfl⟩
            have hnonmu : hasNonMuHead b = true := by
              simpa [fullUnfoldN] using hb
            have : False := by simp [hasNonMuHead, head, hdest] at hnonmu
            cases this
    -- Bounds Induction: Successor Case
    | succ n ih =>
        intro a b na nb hsum ha hb hmu
        have hstep := Paco.paco_unfold EQ2CMuMono ⊥ a b hmu
        have hstep' : EQ2C_mu_step EQ2C_mu_paco a b := by
          simpa only [Paco.upaco_bot] using hstep
        cases hstep' with
        | obs hobs => exact hobs
        | mu_left hstep hrel =>
            cases na with
            | zero =>
                rcases hstep with ⟨x, f, hdest, rfl⟩
                have hnonmu : hasNonMuHead a = true := by
                  simpa [fullUnfoldN] using ha
                have : False := by simp [hasNonMuHead, head, hdest] at hnonmu
                cases this
            | succ na' =>
                rcases hstep with ⟨x, f, hdest, rfl⟩
                have hstep' : UnfoldsC a (f ()) := ⟨x, f, hdest, rfl⟩
                have hsum' : na' + nb = n := by
                  have hsum'' : (na' + nb) + 1 = n + 1 := by
                    calc
                      (na' + nb) + 1 = na' + (nb + 1) := by
                        simp [Nat.add_assoc]
                      _ = na' + (1 + nb) := by
                        simp [Nat.add_comm]
                      _ = na' + 1 + nb := by
                        simp [Nat.add_assoc]
                      _ = n + 1 := hsum
                  exact Nat.add_right_cancel hsum''
                have ha' : hasNonMuHead (fullUnfoldN na' (f ())) = true := by
                  simpa using
                    (hasNonMuHead_fullUnfoldN_succ_of_unfoldsC (a := a) (a' := f ())
                      hstep' (n := na') (h := ha))
                have hobs' :=
                  ih (a := f ()) (b := b) (na := na') (nb := nb) hsum' ha' hb hrel
                exact ObservableRelC_unfoldsC_left hstep' hobs'
        -- Bounds Induction: Right-Unfold Case
        | mu_right hstep hrel =>
            cases nb with
            | zero =>
                rcases hstep with ⟨x, f, hdest, rfl⟩
                have hnonmu : hasNonMuHead b = true := by
                  simpa [fullUnfoldN] using hb
                have : False := by simp [hasNonMuHead, head, hdest] at hnonmu
                cases this
            | succ nb' =>
                rcases hstep with ⟨x, f, hdest, rfl⟩
                have hstep' : UnfoldsC b (f ()) := ⟨x, f, hdest, rfl⟩
                have hsum' : na + nb' = n := by
                  have hsum'' : (na + nb') + 1 = n + 1 := by
                    calc
                      (na + nb') + 1 = na + (nb' + 1) := by
                        simp [Nat.add_assoc]
                      _ = n + 1 := by
                        simpa [Nat.add_assoc] using hsum
                  exact Nat.add_right_cancel hsum''
                have hb' : hasNonMuHead (fullUnfoldN nb' (f ())) = true := by
                  simpa using
                    (hasNonMuHead_fullUnfoldN_succ_of_unfoldsC (a := b) (a' := f ())
                      hstep' (n := nb') (h := hb))
                have hobs' :=
                  ih (a := a) (b := f ()) (na := na) (nb := nb') hsum' ha hb' hrel
                exact ObservableRelC_unfoldsC_right hstep' hobs'
  exact aux (na + nb) rfl ha hb h

-- Observable Inputs Corollary

/-- For observable types, mu-step paco yields an observable relation. -/
lemma EQ2C_mu_paco_to_obs {a b : LocalTypeC}
    (ha : ObservableC a) (hb : ObservableC b) (h : EQ2C_mu_paco a b) :
    ObservableRelC EQ2C_mu_paco a b := by
  classical
  obtain ⟨na, ha'⟩ := hasNonMuHead_fullUnfoldN_of_observable (t := a) ha
  obtain ⟨nb, hb'⟩ := hasNonMuHead_fullUnfoldN_of_observable (t := b) hb
  exact EQ2C_mu_paco_to_obs_of_bounds (a := a) (b := b) ha' hb' h

end SessionCoTypes.Coinductive
