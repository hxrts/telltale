import Mathlib
import RumpsteakV2.Coinductive.Bridge
import RumpsteakV2.Coinductive.LocalTypeC
import RumpsteakV2.Coinductive.Observable
import RumpsteakV2.Coinductive.EQ2C
import RumpsteakV2.Coinductive.EQ2CEnv
import RumpsteakV2.Coinductive.Regularity
import RumpsteakV2.Coinductive.ToInductive
import RumpsteakV2.Coinductive.ToCoindInjectivity
import RumpsteakV2.Coinductive.ToCoindRegular
import RumpsteakV2.Coinductive.RoundtripHelpers
import RumpsteakV2.Coinductive.EQ2CPaco
import RumpsteakV2.Coinductive.EQ2CProps
import RumpsteakV2.Coinductive.EQ2CMu
import RumpsteakV2.Coinductive.BisimHelpers
import RumpsteakV2.Coinductive.BisimDecidable
import RumpsteakV2.Coinductive.WellFormed
import RumpsteakV2.Protocol.LocalTypeR

set_option linter.dupNamespace false

/-
The Problem. The key correctness property for the inductive-coinductive bridge
is that round-tripping preserves equivalence: toCoind(toInductive(t)) ≅ t.
This ensures we can convert freely between representations without losing
semantic meaning.

The difficulty is that toInductive introduces fresh mu-binders and variable
names that don't exist in the original coinductive type. We need to prove
that these are equivalent under EQ2C (equi-recursive type equality).

Module Organization.
- ToCoindInjectivity.lean: injectivity of toCoind (complete)
- RoundtripHelpers.lean: structural helper lemmas (complete)
- BisimHelpers.lean: bisimulation construction lemmas (complete)
- EQ2CEnv/EQ2CMu.lean: environment resolution + mu-aware paco machinery

This file now contains the round-trip erasure proofs and the public API.
Remaining placeholders (nameOf/envOf + round-trip statements) are tracked here
until the full round-trip proof is completed.
-/

namespace RumpsteakV2.Coinductive

open Classical
open RumpsteakV2.Protocol.GlobalType
open RumpsteakV2.Protocol.LocalTypeR

/-! ## Re-exports from ToCoindInjectivity -/

-- toCoind_injective is available from ToCoindInjectivity
-- toCoindBranches_injective is available from ToCoindInjectivity
-- toCoindBranches_length, toCoindBranches_get are available from ToCoindInjectivity

/-! ## Re-exports from RoundtripHelpers -/

-- childRel_toCoind, childRel_toCoind_size are available from RoundtripHelpers
-- VisitedLt, visitedLt_not_mem, visitedLt_insert are available from RoundtripHelpers
-- childRel_toCoind_mu, childRel_toCoind_send, childRel_toCoind_recv are available

/-! ## Re-exports from BisimHelpers -/

-- EQ2C_end_head, EQ2C_var_head, EQ2C_send_head, EQ2C_recv_head are available from BisimHelpers
-- EQ2CE_step_to_EQ2C is available from BisimHelpers

/-! ## EQ2CE → EQ2C erasure (coinductive) -/

def EQ2CE_rel (a b : LocalTypeC) : Prop :=
  ∃ ρ, EnvResolvesL ρ ∧ EnvVarR ρ ∧ EQ2CE ρ a b

/-- Relation for coinductive proof: env-aware EQ2CE with resolution constraints. -/
def EQ2CE_resolved : Rel :=
  fun ρ a b => EnvResolvesL ρ ∧ EnvVarR ρ ∧ EQ2CE ρ a b

/-- Environment-aware bisimulation with resolution: relation for coinductive proof. -/
def EQ2CE_resolved' (a b : LocalTypeC) : Prop :=
  ∃ ρ, EnvResolvesL ρ ∧ EnvVarR ρ ∧ EQ2CE ρ a b

/-! ## μ-closure for gpaco_clo -/

/-- Explicit μ-closure: allow wrapping a relation on either side with `mkMu`. -/
def mu_clo (R : LocalTypeC → LocalTypeC → Prop) : LocalTypeC → LocalTypeC → Prop :=
  fun a b =>
    R a b ∨
      (∃ x t, a = mkMu x t ∧ R t b) ∨
      (∃ x t, b = mkMu x t ∧ R a t)

lemma mu_clo_mono : Paco.CloMono mu_clo := by
  intro R S h a b hab
  rcases hab with hR | hL | hR'
  · exact Or.inl (h _ _ hR)
  · rcases hL with ⟨x, t, ha, hRt⟩
    exact Or.inr (Or.inl ⟨x, t, ha, h _ _ hRt⟩)
  · rcases hR' with ⟨x, t, hb, hRt⟩
    exact Or.inr (Or.inr ⟨x, t, hb, h _ _ hRt⟩)

lemma mu_clo_compat : Paco.Compatible EQ2CMono mu_clo := by
  intro R a b h
  rcases h with hR | hL | hR'
  · rcases hR with ⟨obs_a, obs_b, hrel⟩
    refine ⟨obs_a, obs_b, ?_⟩
    exact ObservableRelC_mono (fun _ _ hr => Or.inl hr) hrel
  · rcases hL with ⟨x, t, ha, hstep⟩
    rcases hstep with ⟨obs_t, obs_b, hrel⟩
    have obs_mu : ObservableC (mkMu x t) := observable_mkMu obs_t
    have obs_a : ObservableC a := by
      simpa [ha] using obs_mu
    refine ⟨obs_a, obs_b, ?_⟩
    have hrel' : ObservableRelC (mu_clo R) t b :=
      ObservableRelC_mono (fun _ _ hr => Or.inl hr) hrel
    simpa [ha] using (ObservableRelC_mu_left (x := x) hrel')
  · rcases hR' with ⟨x, t, hb, hstep⟩
    rcases hstep with ⟨obs_a, obs_t, hrel⟩
    have obs_mu : ObservableC (mkMu x t) := observable_mkMu obs_t
    have obs_b : ObservableC b := by
      simpa [hb] using obs_mu
    refine ⟨obs_a, obs_b, ?_⟩
    have hrel' : ObservableRelC (mu_clo R) a t :=
      ObservableRelC_mono (fun _ _ hr => Or.inl hr) hrel
    simpa [hb] using (ObservableRelC_mu_right (x := x) hrel')

/-! ## gpaco_clo helpers -/

lemma BranchesRelC_gupaco_clo {rr : LocalTypeC → LocalTypeC → Prop}
    {bs cs : List (Label × LocalTypeC)}
    (hbr : BranchesRelC rr bs cs) :
    BranchesRelC (Paco.gupaco_clo EQ2CMono mu_clo rr) bs cs := by
  refine BranchesRelC_mono ?_ hbr
  intro a b h
  have h' := Paco.r_le_gpaco_clo EQ2CMono mu_clo rr rr a b h
  simpa [Paco.gupaco_clo_def] using h'

lemma gupaco_clo_obs_of_rr {rr : LocalTypeC → LocalTypeC → Prop}
    (hrr : ∀ a b, rr a b → ObservableRelC (Paco.gupaco_clo EQ2CMono mu_clo rr) a b)
    {a b : LocalTypeC} (h : Paco.gupaco_clo EQ2CMono mu_clo rr a b) :
    ObservableRelC (Paco.gupaco_clo EQ2CMono mu_clo rr) a b := by
  -- Unfold gupaco_clo to expose the underlying rclo proof.
  simp [Paco.gupaco_clo_def, Paco.gpaco_clo_def] at h
  -- Now: h : rclo mu_clo (paco (composeRclo EQ2CMono mu_clo) rr ⊔ rr) a b
  revert a b
  intro a b h
  induction h with
  | base hbase =>
      cases hbase with
      | inl hpaco =>
          have hstep :=
            Paco.paco_unfold (Paco.composeRclo EQ2CMono mu_clo) rr _ _ hpaco
          rcases hstep with ⟨obs_a, obs_b, hrel⟩
          -- composeRclo = EQ2CMono.F ∘ rclo mu_clo; upaco = paco ⊔ rr
          -- So this is exactly ObservableRelC with gupaco_clo as the relation.
          simpa [Paco.composeRclo_def, Paco.gupaco_clo_def, Paco.gpaco_clo_def] using hrel
      | inr hrr' =>
          exact hrr _ _ hrr'
  | clo R' _ hclo ih =>
      cases hclo with
      | inl hR'ab =>
          exact ih _ _ hR'ab
      | inr hrest =>
          cases hrest with
          | inl hleft =>
              rcases hleft with ⟨x, t, ha, hRt⟩
              have hobs := ih _ _ hRt
              have hobs' := ObservableRelC_mu_left (x := x) hobs
              simpa [ha] using hobs'
          | inr hright =>
              rcases hright with ⟨x, t, hb, hRt⟩
              have hobs := ih _ _ hRt
              have hobs' := ObservableRelC_mu_right (x := x) hobs
              simpa [hb] using hobs'

/-! ## EQ2CE_resolved' → EQ2C_mu_paco -/

/-- EQ2CE_resolved' embeds into the μ-aware paco relation.

We keep the global guard empty and fold EQ2C into the witness relation.
μ-steps are handled directly by the generator `EQ2C_mu_step`.
-/
theorem EQ2CE_resolved'_to_mu_paco {a b : LocalTypeC} (h : EQ2CE_resolved' a b) :
    EQ2C_mu_paco a b := by
  refine
    (Paco.paco_coind EQ2CMuMono (EQ2CE_resolved' ⊔ EQ2C) ⊥ ?_ (Or.inl h))
  intro a b hR
  cases hR with
  | inr hEQ =>
      obtain ⟨_, _, hrel⟩ := EQ2C_observableRel hEQ
      have hrel' : ObservableRelC ((EQ2CE_resolved' ⊔ EQ2C) ⊔ ⊥) a b :=
        ObservableRelC_mono (fun _ _ hr => Or.inl (Or.inr hr)) hrel
      exact EQ2C_mu_step.obs hrel'
  | inl hR =>
      rcases hR with ⟨ρ, hResL, hVarR, hce⟩
      have hstep := EQ2CE_unfold hce
      cases hstep with
      | «end» ha hb =>
          have hend_a : UnfoldsToEndC a := UnfoldsToEndC_of_head ha
          have hend_b : UnfoldsToEndC b := UnfoldsToEndC_of_head hb
          exact EQ2C_mu_step.obs (ObservableRelC.is_end hend_a hend_b)
      | var ha hb =>
          rename_i x
          have hvar_a : UnfoldsToVarC a x := UnfoldsToVarC_of_head ha
          have hvar_b : UnfoldsToVarC b x := UnfoldsToVarC_of_head hb
          exact EQ2C_mu_step.obs (ObservableRelC.is_var x hvar_a hvar_b)
      | send ha hb hbr =>
          rename_i p labels labels'
          have hbr0 : BranchesRelC (EQ2CE_resolved' ⊔ EQ2C) (branchesOf a) (branchesOf b) := by
            refine List.Forall₂.imp ?_ hbr
            intro c d hcd
            exact ⟨hcd.1, Or.inl ⟨ρ, hResL, hVarR, hcd.2⟩⟩
          have hsend_a : CanSendC a p (branchesOf a) := CanSendC_of_head ha
          have hsend_b : CanSendC b p (branchesOf b) := CanSendC_of_head hb
          have hbr1 :
              BranchesRelC ((EQ2CE_resolved' ⊔ EQ2C) ⊔ ⊥) (branchesOf a) (branchesOf b) :=
            BranchesRelC_mono (fun _ _ hr => Or.inl hr) hbr0
          exact EQ2C_mu_step.obs (ObservableRelC.is_send p _ _ hsend_a hsend_b hbr1)
      | recv ha hb hbr =>
          rename_i p labels labels'
          have hbr0 : BranchesRelC (EQ2CE_resolved' ⊔ EQ2C) (branchesOf a) (branchesOf b) := by
            refine List.Forall₂.imp ?_ hbr
            intro c d hcd
            exact ⟨hcd.1, Or.inl ⟨ρ, hResL, hVarR, hcd.2⟩⟩
          have hrecv_a : CanRecvC a p (branchesOf a) := CanRecvC_of_head ha
          have hrecv_b : CanRecvC b p (branchesOf b) := CanRecvC_of_head hb
          have hbr1 :
              BranchesRelC ((EQ2CE_resolved' ⊔ EQ2C) ⊔ ⊥) (branchesOf a) (branchesOf b) :=
            BranchesRelC_mono (fun _ _ hr => Or.inl hr) hbr0
          exact EQ2C_mu_step.obs (ObservableRelC.is_recv p _ _ hrecv_a hrecv_b hbr1)
      | var_left ha hmem =>
          rename_i x
          have hvar_b : UnfoldsToVarC b x :=
            EQ2C_mkVar_left_unfolds (hResL x b hmem)
          have hvar_a : UnfoldsToVarC a x := UnfoldsToVarC_of_head ha
          exact EQ2C_mu_step.obs (ObservableRelC.is_var x hvar_a hvar_b)
      | var_right hb hmem =>
          rename_i x
          have hEq : a = mkVar x := hVarR x a hmem
          have ha : head a = .var x := by simp [hEq]
          have hvar_a : UnfoldsToVarC a x := UnfoldsToVarC_of_head ha
          have hvar_b : UnfoldsToVarC b x := UnfoldsToVarC_of_head hb
          exact EQ2C_mu_step.obs (ObservableRelC.is_var x hvar_a hvar_b)
      | mu_left ha hmem hrel =>
          rename_i x f
          have hEnvL' : EnvResolvesL (envInsertL ρ x b) := EnvResolvesL_insertL_mem hResL hmem
          have hVarR' : EnvVarR (envInsertL ρ x b) := by
            intro y c hc; simp only [envInsertL, envR] at hc; exact hVarR y c hc
          have hR' : EQ2CE_resolved' (f ()) b := ⟨envInsertL ρ x b, hEnvL', hVarR', hrel⟩
          have hstep' : UnfoldsC a (f ()) := ⟨x, f, ha, rfl⟩
          exact EQ2C_mu_step.mu_left hstep' (Or.inl (Or.inl hR'))
      | mu_right hb hrel =>
          rename_i x f
          have hEnvL' : EnvResolvesL (envInsertR ρ x (mkVar x)) := by
            intro y c hc; simp only [envInsertR, envL] at hc; exact hResL y c hc
          have hVarR' : EnvVarR (envInsertR ρ x (mkVar x)) :=
            EnvVarR_insertR_var hVarR
          have hR' : EQ2CE_resolved' a (f ()) := ⟨envInsertR ρ x (mkVar x), hEnvL', hVarR', hrel⟩
          have hstep' : UnfoldsC b (f ()) := ⟨x, f, hb, rfl⟩
          exact EQ2C_mu_step.mu_right hstep' (Or.inl (Or.inl hR'))

/-- EQ2CE_resolved' is a bisimulation: each step produces either EQ2C or stays in EQ2CE_resolved'.
    This uses EQ2CE_step_to_EQ2C_varR from BisimHelpers. -/
theorem EQ2CE_resolved'_step_to_EQ2C {a b : LocalTypeC}
    (h : EQ2CE_resolved' a b)
    (hIH : ∀ a' b', EQ2CE_resolved' a' b' → EQ2C a' b') :
    EQ2C a b := by
  rcases h with ⟨ρ, hResL, hVarR, hce⟩
  have hstep := EQ2CE_unfold hce
  -- Define R as EQ2CE with resolving env
  let R : Rel := fun ρ' a' b' => EnvResolvesL ρ' ∧ EnvVarR ρ' ∧ EQ2CE ρ' a' b'
  have hR : ∀ ρ' a' b', R ρ' a' b' → EQ2C a' b' := by
    intro ρ' a' b' ⟨hResL', hVarR', hce'⟩
    exact hIH a' b' ⟨ρ', hResL', hVarR', hce'⟩
  -- Key: show the step relation holds for R
  have hstep' : EQ2CE_step R ρ a b := by
    cases hstep with
    | «end» ha hb => exact EQ2CE_step.«end» ha hb
    | var ha hb => exact EQ2CE_step.var ha hb
    | send ha hb hbr =>
        refine EQ2CE_step.send ha hb ?_
        refine List.Forall₂.imp ?_ hbr
        intro c d hcd
        exact ⟨hcd.1, hResL, hVarR, hcd.2⟩
    | recv ha hb hbr =>
        refine EQ2CE_step.recv ha hb ?_
        refine List.Forall₂.imp ?_ hbr
        intro c d hcd
        exact ⟨hcd.1, hResL, hVarR, hcd.2⟩
    | var_left ha hmem => exact EQ2CE_step.var_left ha hmem
    | var_right hb hmem => exact EQ2CE_step.var_right hb hmem
    | mu_left ha hmem hrel =>
        rename_i v f
        have hEnvL' : EnvResolvesL (envInsertL ρ v b) := EnvResolvesL_insertL_mem hResL hmem
        have hVarR' : EnvVarR (envInsertL ρ v b) := by
          intro x c hc; simp only [envInsertL, envR] at hc; exact hVarR x c hc
        exact EQ2CE_step.mu_left ha hmem ⟨hEnvL', hVarR', hrel⟩
    | mu_right hb hrel =>
        rename_i vname f
        have hEnvL' : EnvResolvesL (envInsertR ρ vname (mkVar vname)) := by
          intro x c hc; simp only [envInsertR, envL] at hc; exact hResL x c hc
        have hVarR' : EnvVarR (envInsertR ρ vname (mkVar vname)) :=
          EnvVarR_insertR_var hVarR
        exact EQ2CE_step.mu_right hb ⟨hEnvL', hVarR', hrel⟩
  exact EQ2CE_step_to_EQ2C_varR hR hResL hVarR hstep'

end RumpsteakV2.Coinductive.Roundtrip
