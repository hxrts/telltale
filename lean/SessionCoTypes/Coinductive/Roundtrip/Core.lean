
import Mathlib
import SessionCoTypes.Coinductive.Bridge
import SessionCoTypes.Coinductive.LocalTypeC
import SessionCoTypes.Coinductive.Observable
import SessionCoTypes.Coinductive.EQ2C
import SessionCoTypes.Coinductive.EQ2CEnv
import SessionCoTypes.Coinductive.Regularity
import SessionCoTypes.Coinductive.ToInductive
import SessionCoTypes.Coinductive.ToCoindInjectivity
import SessionCoTypes.Coinductive.ToCoindRegular
import SessionCoTypes.Coinductive.RoundtripHelpers
import SessionCoTypes.Coinductive.EQ2CPaco
import SessionCoTypes.Coinductive.EQ2CProps
import SessionCoTypes.Coinductive.EQ2CMu
import SessionCoTypes.Coinductive.BisimHelpers
import SessionCoTypes.Coinductive.BisimDecidable
import SessionCoTypes.Coinductive.WellFormed
import SessionTypes.LocalTypeR

/- ## Structured Block 1 -/
set_option linter.dupNamespace false

/-! # Round-Trip Correctness

Proof that toCoind(toInductive(t)) ≅ t for inductive-coinductive bridge. -/

/-
The Problem. Round-tripping through inductive-coinductive conversions must preserve
equivalence: toCoind(toInductive(t)) ≅ t. The difficulty is that toInductive
introduces fresh mu-binders and variable names not in the original type.

Solution Structure. Module organization: ToCoindInjectivity.lean proves injectivity
of toCoind, RoundtripHelpers.lean provides structural helpers, BisimHelpers.lean
has bisimulation construction lemmas, EQ2CEnv/EQ2CMu.lean provides environment
resolution and mu-aware paco machinery. This file contains round-trip erasure
proofs and the public API.
-/

namespace SessionCoTypes.Coinductive

open Classical
open SessionTypes.GlobalType
open SessionTypes.LocalTypeR

-- Re-exports from ToCoindInjectivity

-- to_coind_injective is available from ToCoindInjectivity
-- to_coind_branches_injective is available from ToCoindInjectivity
-- to_coind_branches_length, to_coind_branches_get are available from ToCoindInjectivity

-- Re-exports from RoundtripHelpers

-- child_rel_to_coind, child_rel_to_coind_size are available from RoundtripHelpers
-- VisitedLt, visited_lt_not_mem, visited_lt_insert are available from RoundtripHelpers
-- child_rel_to_coind_mu, child_rel_to_coind_send, child_rel_to_coind_recv are available

-- Re-exports from BisimHelpers

-- eq2_c_end_head, eq2_c_var_head, eq2_c_send_head, eq2_c_recv_head are available from BisimHelpers
-- eq2_ce_step_to_eq2_c is available from BisimHelpers

-- EQ2CE → EQ2C erasure (coinductive)

def EQ2CE_rel (a b : LocalTypeC) : Prop :=
  ∃ ρ, EnvResolvesL ρ ∧ EnvVarR ρ ∧ EQ2CE ρ a b

/-- Relation for coinductive proof: env-aware EQ2CE with resolution constraints. -/
def EQ2CE_resolved : Rel :=
  fun ρ a b => EnvResolvesL ρ ∧ EnvVarR ρ ∧ EQ2CE ρ a b

/-- Environment-aware bisimulation with resolution: relation for coinductive proof. -/
def EQ2CE_resolved' (a b : LocalTypeC) : Prop :=
  ∃ ρ, EnvResolvesL ρ ∧ EnvVarR ρ ∧ EQ2CE ρ a b

-- μ-closure for gpaco_clo

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
    exact observable_rel_c_mono (fun _ _ hr => Or.inl hr) hrel
  · rcases hL with ⟨x, t, ha, hstep⟩
    rcases hstep with ⟨obs_t, obs_b, hrel⟩
    have obs_mu : ObservableC (mkMu x t) := observable_mk_mu obs_t
    have obs_a : ObservableC a := by
      simpa [ha] using obs_mu
    refine ⟨obs_a, obs_b, ?_⟩
    have hrel' : ObservableRelC (mu_clo R) t b :=
      observable_rel_c_mono (fun _ _ hr => Or.inl hr) hrel
    simpa [ha] using (observable_rel_c_mu_left (x := x) hrel')
  · rcases hR' with ⟨x, t, hb, hstep⟩
    rcases hstep with ⟨obs_a, obs_t, hrel⟩
    have obs_mu : ObservableC (mkMu x t) := observable_mk_mu obs_t
    have obs_b : ObservableC b := by
      simpa [hb] using obs_mu
    refine ⟨obs_a, obs_b, ?_⟩
    have hrel' : ObservableRelC (mu_clo R) a t :=
      observable_rel_c_mono (fun _ _ hr => Or.inl hr) hrel
    simpa [hb] using (observable_rel_c_mu_right (x := x) hrel')

-- gpaco_clo helpers

lemma branches_rel_c_gupaco_clo {rr : LocalTypeC → LocalTypeC → Prop}
    {bs cs : List (Label × LocalTypeC)}
/- ## Structured Block 2 -/
    (hbr : BranchesRelC rr bs cs) :
    BranchesRelC (Paco.gupaco_clo EQ2CMono mu_clo rr) bs cs := by
  refine branches_rel_c_mono ?_ hbr
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
              have hobs' := observable_rel_c_mu_left (x := x) hobs
              simpa [ha] using hobs'
          | inr hright =>
              rcases hright with ⟨x, t, hb, hRt⟩
              have hobs := ih _ _ hRt
              have hobs' := observable_rel_c_mu_right (x := x) hobs
              simpa [hb] using hobs'

-- EQ2CE_resolved' → EQ2C_mu_paco

/-- EQ2CE_resolved' embeds into the μ-aware paco relation.

We keep the global guard empty and fold EQ2C into the witness relation.
μ-steps are handled directly by the generator `EQ2C_mu_step`.
-/
theorem eq2_ce_resolved'_to_mu_paco {a b : LocalTypeC} (h : EQ2CE_resolved' a b) :
    EQ2C_mu_paco a b := by
  refine
    (Paco.paco_coind EQ2CMuMono (EQ2CE_resolved' ⊔ EQ2C) ⊥ ?_ (Or.inl h))
  intro a b hR
  cases hR with
  | inr hEQ =>
      obtain ⟨_, _, hrel⟩ := eq2_c_observable_rel hEQ
      have hrel' : ObservableRelC ((EQ2CE_resolved' ⊔ EQ2C) ⊔ ⊥) a b :=
        observable_rel_c_mono (fun _ _ hr => Or.inl (Or.inr hr)) hrel
      exact EQ2C_mu_step.obs hrel'
/- ## Structured Block 3 -/
  | inl hR =>
      rcases hR with ⟨ρ, hResL, hVarR, hce⟩
      have hstep := eq2_ce_unfold hce
      cases hstep with
      -- μ-paco Embed: Observable Cases
      | «end» ha hb =>
          have hend_a : UnfoldsToEndC a := unfolds_to_end_c_of_head ha
          have hend_b : UnfoldsToEndC b := unfolds_to_end_c_of_head hb
          exact EQ2C_mu_step.obs (ObservableRelC.is_end hend_a hend_b)
      | var ha hb =>
          rename_i x
          have hvar_a : UnfoldsToVarC a x := unfolds_to_var_c_of_head ha
          have hvar_b : UnfoldsToVarC b x := unfolds_to_var_c_of_head hb
          exact EQ2C_mu_step.obs (ObservableRelC.is_var x hvar_a hvar_b)
      -- μ-paco Embed: Communication Cases
      | send ha hb hbr =>
          rename_i p labels labels'
          have hbr0 : BranchesRelC (EQ2CE_resolved' ⊔ EQ2C) (branchesOf a) (branchesOf b) := by
            refine List.Forall₂.imp ?_ hbr
            intro c d hcd
            exact ⟨hcd.1, Or.inl ⟨ρ, hResL, hVarR, hcd.2⟩⟩
          have hsend_a : CanSendC a p (branchesOf a) := can_send_c_of_head ha
          have hsend_b : CanSendC b p (branchesOf b) := can_send_c_of_head hb
          have hbr1 :
              BranchesRelC ((EQ2CE_resolved' ⊔ EQ2C) ⊔ ⊥) (branchesOf a) (branchesOf b) :=
            branches_rel_c_mono (fun _ _ hr => Or.inl hr) hbr0
          exact EQ2C_mu_step.obs (ObservableRelC.is_send p _ _ hsend_a hsend_b hbr1)
      | recv ha hb hbr =>
          rename_i p labels labels'
          have hbr0 : BranchesRelC (EQ2CE_resolved' ⊔ EQ2C) (branchesOf a) (branchesOf b) := by
            refine List.Forall₂.imp ?_ hbr
            intro c d hcd
            exact ⟨hcd.1, Or.inl ⟨ρ, hResL, hVarR, hcd.2⟩⟩
          have hrecv_a : CanRecvC a p (branchesOf a) := can_recv_c_of_head ha
          have hrecv_b : CanRecvC b p (branchesOf b) := can_recv_c_of_head hb
          have hbr1 :
              BranchesRelC ((EQ2CE_resolved' ⊔ EQ2C) ⊔ ⊥) (branchesOf a) (branchesOf b) :=
            branches_rel_c_mono (fun _ _ hr => Or.inl hr) hbr0
          exact EQ2C_mu_step.obs (ObservableRelC.is_recv p _ _ hrecv_a hrecv_b hbr1)
      -- μ-paco Embed: Variable Cases
      | var_left ha hmem =>
          rename_i x
          have hvar_b : UnfoldsToVarC b x :=
            eq2_c_mk_var_left_unfolds (hResL x b hmem)
          have hvar_a : UnfoldsToVarC a x := unfolds_to_var_c_of_head ha
          exact EQ2C_mu_step.obs (ObservableRelC.is_var x hvar_a hvar_b)
      | var_right hb hmem =>
          rename_i x
          have hEq : a = mkVar x := hVarR x a hmem
          have ha : head a = .var x := by simp [hEq]
          have hvar_a : UnfoldsToVarC a x := unfolds_to_var_c_of_head ha
          have hvar_b : UnfoldsToVarC b x := unfolds_to_var_c_of_head hb
          exact EQ2C_mu_step.obs (ObservableRelC.is_var x hvar_a hvar_b)
      -- μ-paco Embed: μ-unfold Cases
/- ## Structured Block 4 -/
      | mu_left ha hmem hrel =>
          rename_i x f
          have hEnvL' : EnvResolvesL (envInsertL ρ x b) := env_resolves_l_insert_l_mem hResL hmem
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
            env_var_r_insert_r_var hVarR
          have hR' : EQ2CE_resolved' a (f ()) := ⟨envInsertR ρ x (mkVar x), hEnvL', hVarR', hrel⟩
          have hstep' : UnfoldsC b (f ()) := ⟨x, f, hb, rfl⟩
          exact EQ2C_mu_step.mu_right hstep' (Or.inl (Or.inl hR'))

-- EQ2CE_resolved' Step Erasure

/-- EQ2CE_resolved' is a bisimulation: each step produces either EQ2C or stays in EQ2CE_resolved'.
    This uses eq2_ce_step_to_eq2_c_var_r from BisimHelpers. -/
theorem eq2_ce_resolved'_step_to_eq2_c {a b : LocalTypeC}
    (h : EQ2CE_resolved' a b)
    (hIH : ∀ a' b', EQ2CE_resolved' a' b' → EQ2C a' b') :
    EQ2C a b := by
  rcases h with ⟨ρ, hResL, hVarR, hce⟩
  have hstep := eq2_ce_unfold hce
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
        have hEnvL' : EnvResolvesL (envInsertL ρ v b) := env_resolves_l_insert_l_mem hResL hmem
        have hVarR' : EnvVarR (envInsertL ρ v b) := by
          intro x c hc; simp only [envInsertL, envR] at hc; exact hVarR x c hc
        exact EQ2CE_step.mu_left ha hmem ⟨hEnvL', hVarR', hrel⟩
    | mu_right hb hrel =>
/- ## Structured Block 5 -/
        rename_i vname f
        have hEnvL' : EnvResolvesL (envInsertR ρ vname (mkVar vname)) := by
          intro x c hc; simp only [envInsertR, envL] at hc; exact hResL x c hc
        have hVarR' : EnvVarR (envInsertR ρ vname (mkVar vname)) :=
          env_var_r_insert_r_var hVarR
        exact EQ2CE_step.mu_right hb ⟨hEnvL', hVarR', hrel⟩
  exact eq2_ce_step_to_eq2_c_var_r hR hResL hVarR hstep'

end SessionCoTypes.Coinductive
