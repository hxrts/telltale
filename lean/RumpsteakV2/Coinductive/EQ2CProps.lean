import Mathlib
import RumpsteakV2.Coinductive.EQ2C
import RumpsteakV2.Coinductive.WellFormed

set_option linter.dupNamespace false

/-!
# EQ2C helper lemmas

Auxiliary lemmas for reasoning about EQ2C, including left/right μ-unfolding.
-/

namespace RumpsteakV2.Coinductive

/-- Base EQ2C proof for `end`. -/
lemma EQ2C_end : EQ2C mkEnd mkEnd := by
  let R : LocalTypeC → LocalTypeC → Prop := fun a b => a = mkEnd ∧ b = mkEnd
  have hR : IsBisimulationC R := by
    intro a b hrel
    rcases hrel with ⟨ha, hb⟩
    subst ha; subst hb
    have obs : ObservableC mkEnd := observable_mkEnd
    exact ⟨obs, obs, ObservableRelC.is_end (by
      cases obs with
      | is_end ha => exact ha
      | _ => cases obs) (by
      cases obs with
      | is_end hb => exact hb
      | _ => cases obs)⟩
  exact ⟨R, hR, ⟨rfl, rfl⟩⟩

/-- Base EQ2C proof for variables. -/
lemma EQ2C_var (v : String) : EQ2C (mkVar v) (mkVar v) := by
  let R : LocalTypeC → LocalTypeC → Prop := fun a b => a = mkVar v ∧ b = mkVar v
  have hR : IsBisimulationC R := by
    intro a b hrel
    rcases hrel with ⟨ha, hb⟩
    subst ha; subst hb
    have obs : ObservableC (mkVar v) := observable_mkVar v
    exact ⟨obs, obs, ObservableRelC.is_var v (by
      cases obs with
      | is_var _ ha => exact ha
      | _ => cases obs) (by
      cases obs with
      | is_var _ hb => exact hb
      | _ => cases obs)⟩
  exact ⟨R, hR, ⟨rfl, rfl⟩⟩

/-- EQ2C is closed under send, given branch-wise EQ2C. -/
lemma EQ2C_send {p : String} {bs cs : List (Label × LocalTypeC)}
    (hbr : BranchesRelC EQ2C bs cs) : EQ2C (mkSend p bs) (mkSend p cs) := by
  let R' : LocalTypeC → LocalTypeC → Prop :=
    fun a b => (a = mkSend p bs ∧ b = mkSend p cs) ∨ EQ2C a b
  have hR' : IsBisimulationC R' := by
    intro a b hrel
    cases hrel with
    | inr hEQ =>
        rcases hEQ with ⟨R, hR, hrel⟩
        obtain ⟨obs_a, obs_b, hobs⟩ := hR a b hrel
        have hobs' : ObservableRelC R' obs_a obs_b :=
          ObservableRelC_mono (fun _ _ hr => Or.inr ⟨R, hR, hr⟩) hobs
        exact ⟨obs_a, obs_b, hobs'⟩
    | inl hpair =>
        rcases hpair with ⟨ha, hb⟩
        subst ha; subst hb
        have obs_a : ObservableC (mkSend p bs) := observable_mkSend p bs
        have obs_b : ObservableC (mkSend p cs) := observable_mkSend p cs
        have hbr' : BranchesRelC R' bs cs :=
          BranchesRelC_mono (fun _ _ hr => Or.inr hr) hbr
        exact ⟨obs_a, obs_b, ObservableRelC.is_send p bs cs (by
          -- Use the observable produced by `observable_mkSend`.
          cases obs_a with
          | is_send _ _ ha => exact ha
          | _ => cases obs_a) (by
          cases obs_b with
          | is_send _ _ hb => exact hb
          | _ => cases obs_b) hbr'⟩
  refine ⟨R', hR', ?_⟩
  exact Or.inl ⟨rfl, rfl⟩

/-- EQ2C is closed under recv, given branch-wise EQ2C. -/
lemma EQ2C_recv {p : String} {bs cs : List (Label × LocalTypeC)}
    (hbr : BranchesRelC EQ2C bs cs) : EQ2C (mkRecv p bs) (mkRecv p cs) := by
  let R' : LocalTypeC → LocalTypeC → Prop :=
    fun a b => (a = mkRecv p bs ∧ b = mkRecv p cs) ∨ EQ2C a b
  have hR' : IsBisimulationC R' := by
    intro a b hrel
    cases hrel with
    | inr hEQ =>
        rcases hEQ with ⟨R, hR, hrel⟩
        obtain ⟨obs_a, obs_b, hobs⟩ := hR a b hrel
        have hobs' : ObservableRelC R' obs_a obs_b :=
          ObservableRelC_mono (fun _ _ hr => Or.inr ⟨R, hR, hr⟩) hobs
        exact ⟨obs_a, obs_b, hobs'⟩
    | inl hpair =>
        rcases hpair with ⟨ha, hb⟩
        subst ha; subst hb
        have obs_a : ObservableC (mkRecv p bs) := observable_mkRecv p bs
        have obs_b : ObservableC (mkRecv p cs) := observable_mkRecv p cs
        have hbr' : BranchesRelC R' bs cs :=
          BranchesRelC_mono (fun _ _ hr => Or.inr hr) hbr
        exact ⟨obs_a, obs_b, ObservableRelC.is_recv p bs cs (by
          cases obs_a with
          | is_recv _ _ ha => exact ha
          | _ => cases obs_a) (by
          cases obs_b with
          | is_recv _ _ hb => exact hb
          | _ => cases obs_b) hbr'⟩
  refine ⟨R', hR', ?_⟩
  exact Or.inl ⟨rfl, rfl⟩

/-- Wrap a bisimulation on the left with a μ constructor. -/
lemma EQ2C_unfold_left {t u : LocalTypeC} (h : EQ2C t u) (x : String) :
    EQ2C (mkMu x t) u := by
  rcases h with ⟨R, hR, htu⟩
  let R' : LocalTypeC → LocalTypeC → Prop :=
    fun a b => (a = mkMu x t ∧ b = u) ∨ R a b
  have hR' : IsBisimulationC R' := by
    intro a b hrel
    cases hrel with
    | inr hRrel =>
        obtain ⟨obs_a, obs_b, hobs⟩ := hR a b hRrel
        have hobs' : ObservableRelC R' obs_a obs_b :=
          ObservableRelC_mono (fun _ _ hr => Or.inr hr) hobs
        exact ⟨obs_a, obs_b, hobs'⟩
    | inl hpair =>
        rcases hpair with ⟨ha, hb⟩
        subst ha; subst hb
        obtain ⟨obs_t, obs_u, hobs⟩ := hR t u htu
        -- Lift the observable on `t` to `mkMu x t`.
        have obs_mu : ObservableC (mkMu x t) := observable_mkMu obs_t
        -- Build the corresponding observable relation.
        have hrel' : ObservableRelC R' obs_mu obs_u := by
          cases hobs with
          | is_end ha hb =>
              have obs_mu' := observable_mkMu (ObservableC.is_end ha)
              cases obs_mu' with
              | is_end ha_mu => exact ObservableRelC.is_end ha_mu hb
          | is_var v ha hb =>
              have obs_mu' := observable_mkMu (ObservableC.is_var v ha)
              cases obs_mu' with
              | is_var _ ha_mu => exact ObservableRelC.is_var v ha_mu hb
          | is_send p bs cs ha hb hbr =>
              have obs_mu' := observable_mkMu (ObservableC.is_send p bs ha)
              cases obs_mu' with
              | is_send _ _ ha_mu =>
                  exact ObservableRelC.is_send p bs cs ha_mu hb
                    (BranchesRelC_mono (fun _ _ hr => Or.inr hr) hbr)
          | is_recv p bs cs ha hb hbr =>
              have obs_mu' := observable_mkMu (ObservableC.is_recv p bs ha)
              cases obs_mu' with
              | is_recv _ _ ha_mu =>
                  exact ObservableRelC.is_recv p bs cs ha_mu hb
                    (BranchesRelC_mono (fun _ _ hr => Or.inr hr) hbr)
        exact ⟨obs_mu, obs_u, hrel'⟩
  refine ⟨R', hR', ?_⟩
  exact Or.inl ⟨rfl, rfl⟩

/-- Wrap a bisimulation on the right with a μ constructor. -/
lemma EQ2C_unfold_right {t u : LocalTypeC} (h : EQ2C t u) (x : String) :
    EQ2C t (mkMu x u) := by
  have h' : EQ2C u t := EQ2C_symm h
  have h'' : EQ2C (mkMu x u) t := EQ2C_unfold_left h' x
  exact EQ2C_symm h''

end RumpsteakV2.Coinductive
