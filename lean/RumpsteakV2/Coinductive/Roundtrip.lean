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
Remaining axioms (nameOf/envOf + round-trip statements) are tracked here
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

/-! ## μ-aware paco collapse (productivity assumption) -/

lemma mem_childrenOf_of_mem_branchesOf {u : LocalTypeC} {b : Label × LocalTypeC}
    (hmem : b ∈ branchesOf u) : b.2 ∈ childrenOf u := by
  cases hdest : PFunctor.M.dest u with
  | mk hhead f =>
      cases hhead with
      | «end» =>
          have : False := by
            simp [branchesOf, hdest] at hmem
          exact this.elim
      | var v =>
          have : False := by
            simp [branchesOf, hdest] at hmem
          exact this.elim
      | mu x =>
          have : False := by
            simp [branchesOf, hdest] at hmem
          exact this.elim
      | send p labels =>
          have hhead' : head u = .send p labels := by
            simp [head, hdest]
          have hchildren : childrenOf u = (branchesOf u).map (·.2) :=
            childrenOf_send_eq_snd_branchesOf (t := u) (p := p) (labels := labels) hhead'
          have hmem' : b.2 ∈ (branchesOf u).map (·.2) := by
            exact List.mem_map.mpr ⟨b, hmem, rfl⟩
          rw [hchildren]
          exact hmem'
      | recv p labels =>
          have hhead' : head u = .recv p labels := by
            simp [head, hdest]
          have hchildren : childrenOf u = (branchesOf u).map (·.2) :=
            childrenOf_recv_eq_snd_branchesOf (t := u) (p := p) (labels := labels) hhead'
          have hmem' : b.2 ∈ (branchesOf u).map (·.2) := by
            exact List.mem_map.mpr ⟨b, hmem, rfl⟩
          rw [hchildren]
          exact hmem'

lemma reachable_of_canSendC_mem {t : LocalTypeC} {p : String} {bs : List (Label × LocalTypeC)}
    (h : CanSendC t p bs) {b : Label × LocalTypeC} (hmem : b ∈ bs) :
    b.2 ∈ Reachable t := by
  rcases h with ⟨u, labels, hunf, hhead, hbs⟩
  have hreach : u ∈ Reachable t := UnfoldsToC_reachable hunf
  have hmem' : b ∈ branchesOf u := by simpa [hbs] using hmem
  have hchild : childRel u b.2 := childRel_of_mem_childrenOf (mem_childrenOf_of_mem_branchesOf hmem')
  exact reachable_step hreach hchild

lemma reachable_of_canRecvC_mem {t : LocalTypeC} {p : String} {bs : List (Label × LocalTypeC)}
    (h : CanRecvC t p bs) {b : Label × LocalTypeC} (hmem : b ∈ bs) :
    b.2 ∈ Reachable t := by
  rcases h with ⟨u, labels, hunf, hhead, hbs⟩
  have hreach : u ∈ Reachable t := UnfoldsToC_reachable hunf
  have hmem' : b ∈ branchesOf u := by simpa [hbs] using hmem
  have hchild : childRel u b.2 := childRel_of_mem_childrenOf (mem_childrenOf_of_mem_branchesOf hmem')
  exact reachable_step hreach hchild

theorem EQ2C_mu_paco_le_paco_of_productive {a b : LocalTypeC}
    (ha : ProductiveC a) (hb : ProductiveC b) (h : EQ2C_mu_paco a b) :
    EQ2C_paco a b := by
  let R : LocalTypeC → LocalTypeC → Prop :=
    fun x y => EQ2C_mu_paco x y ∧ ProductiveC x ∧ ProductiveC y
  have hR : R a b := ⟨h, ha, hb⟩
  refine Paco.paco_coind EQ2CMono R ⊥ ?_ hR
  intro x y hxy
  rcases hxy with ⟨hmu, hx, hy⟩
  have obs_x : ObservableC x := hx x (Relation.ReflTransGen.refl)
  have obs_y : ObservableC y := hy y (Relation.ReflTransGen.refl)
  have hrel : ObservableRelC EQ2C_mu_paco x y := EQ2C_mu_paco_to_obs obs_x obs_y hmu
  refine ⟨obs_x, obs_y, ?_⟩
  cases hrel with
  | is_end ha hb =>
      exact ObservableRelC.is_end ha hb
  | is_var v ha hb =>
      exact ObservableRelC.is_var v ha hb
  | is_send p bs cs ha_send hb_send hbr =>
      -- Strengthen branch relation with productivity.
      have hbr' : BranchesRelC R bs cs := by
        -- Recurse structurally over the branch lists, tracking membership in the original lists.
        let rec go_send {bs' cs'}
            (hbr : BranchesRelC EQ2C_mu_paco bs' cs')
            (hsub_l : ∀ {b}, b ∈ bs' → b ∈ bs)
            (hsub_r : ∀ {c}, c ∈ cs' → c ∈ cs) : BranchesRelC R bs' cs' := by
          cases hbr with
          | nil => exact List.Forall₂.nil
          | cons hhd htl =>
              rename_i b0 c0 bs'' cs''
              rcases hhd with ⟨hlab, hmu'⟩
              have hreach_l : b0.2 ∈ Reachable x :=
                reachable_of_canSendC_mem ha_send (hsub_l (by simp))
              have hreach_r : c0.2 ∈ Reachable y :=
                reachable_of_canSendC_mem hb_send (hsub_r (by simp))
              have hprod_l : ProductiveC b0.2 := productive_of_reachable hx hreach_l
              have hprod_r : ProductiveC c0.2 := productive_of_reachable hy hreach_r
              have hsub_l' : ∀ {b}, b ∈ bs'' → b ∈ bs := by
                intro b hb
                exact hsub_l (by simp [hb])
              have hsub_r' : ∀ {c}, c ∈ cs'' → c ∈ cs := by
                intro c hc
                exact hsub_r (by simp [hc])
              exact List.Forall₂.cons ⟨hlab, ⟨hmu', hprod_l, hprod_r⟩⟩
                (go_send htl hsub_l' hsub_r')
        exact go_send hbr (by intro b hb; exact hb) (by intro c hc; exact hc)
      exact ObservableRelC.is_send p bs cs ha_send hb_send (BranchesRelC_mono (fun _ _ hr => Or.inl hr) hbr')
  | is_recv p bs cs ha_recv hb_recv hbr =>
      have hbr' : BranchesRelC R bs cs := by
        let rec go_recv {bs' cs'}
            (hbr : BranchesRelC EQ2C_mu_paco bs' cs')
            (hsub_l : ∀ {b}, b ∈ bs' → b ∈ bs)
            (hsub_r : ∀ {c}, c ∈ cs' → c ∈ cs) : BranchesRelC R bs' cs' := by
          cases hbr with
          | nil => exact List.Forall₂.nil
          | cons hhd htl =>
              rename_i b0 c0 bs'' cs''
              rcases hhd with ⟨hlab, hmu'⟩
              have hreach_l : b0.2 ∈ Reachable x :=
                reachable_of_canRecvC_mem ha_recv (hsub_l (by simp))
              have hreach_r : c0.2 ∈ Reachable y :=
                reachable_of_canRecvC_mem hb_recv (hsub_r (by simp))
              have hprod_l : ProductiveC b0.2 := productive_of_reachable hx hreach_l
              have hprod_r : ProductiveC c0.2 := productive_of_reachable hy hreach_r
              have hsub_l' : ∀ {b}, b ∈ bs'' → b ∈ bs := by
                intro b hb
                exact hsub_l (by simp [hb])
              have hsub_r' : ∀ {c}, c ∈ cs'' → c ∈ cs := by
                intro c hc
                exact hsub_r (by simp [hc])
              exact List.Forall₂.cons ⟨hlab, ⟨hmu', hprod_l, hprod_r⟩⟩
                (go_recv htl hsub_l' hsub_r')
        exact go_recv hbr (by intro b hb; exact hb) (by intro c hc; exact hc)
      exact ObservableRelC.is_recv p bs cs ha_recv hb_recv (BranchesRelC_mono (fun _ _ hr => Or.inl hr) hbr')

/-- EQ2CE_resolved' implies EQ2C, assuming productivity on both sides. -/
theorem EQ2CE_resolved'_implies_EQ2C (a b : LocalTypeC) (h : EQ2CE_resolved' a b)
    (ha : ProductiveC a) (hb : ProductiveC b) :
    EQ2C a b := by
  have hmu : EQ2C_mu_paco a b := EQ2CE_resolved'_to_mu_paco h
  have hpaco : EQ2C_paco a b := EQ2C_mu_paco_le_paco_of_productive ha hb hmu
  exact paco_to_EQ2C hpaco

/-- The main erasure theorem: EQ2CE with resolving env implies EQ2C.
    This uses EQ2CE_resolved'_step_to_EQ2C with the coinductive IH
    EQ2CE_resolved'_implies_EQ2C. -/
theorem EQ2CE_to_EQ2C' {ρ : EnvPair} {a b : LocalTypeC}
    (hce : EQ2CE ρ a b) (hEnvL : EnvResolvesL ρ) (hVarR : EnvVarR ρ)
    (ha : ProductiveC a) (hb : ProductiveC b) :
    EQ2C a b :=
  EQ2CE_resolved'_implies_EQ2C a b ⟨ρ, hEnvL, hVarR, hce⟩ ha hb

/-- Simplified erasure: EQ2CE with resolving env implies EQ2C.

This uses EQ2CE_to_EQ2C' which builds a bisimulation directly.
-/
theorem EQ2CE_to_EQ2C {ρ : EnvPair} {a b : LocalTypeC}
    (hce : EQ2CE ρ a b) (hEnvL : EnvResolvesL ρ) (hVarR : EnvVarR ρ)
    (ha : ProductiveC a) (hb : ProductiveC b) :
    EQ2C a b :=
  -- Delegate to EQ2CE_to_EQ2C' which handles all cases
  EQ2CE_to_EQ2C' hce hEnvL hVarR ha hb

/-- The key lemma: EQ2CE_resolved implies EQ2C by coinduction.
    This uses EQ2CE_step_to_EQ2C_varR which handles mu cases via unfolding.
    Delegates to EQ2CE_to_EQ2C'. -/
theorem EQ2CE_resolved_to_EQ2C :
    ∀ ρ a b, EQ2CE_resolved ρ a b → ProductiveC a → ProductiveC b → EQ2C a b := by
  intro ρ a b ⟨hResL, hVarR, hce⟩ ha hb
  exact EQ2CE_to_EQ2C' hce hResL hVarR ha hb

/-! ## Paco-style erasure (alternative) -/

def EQ2CE_rel_paco (a b : LocalTypeC) : Prop :=
  ∃ ρ, EnvResolvesL ρ ∧ EnvVarR ρ ∧ EQ2CE ρ a b

theorem EQ2CE_to_EQ2C_paco {a b : LocalTypeC} (hR : EQ2CE_rel_paco a b)
    (ha : ProductiveC a) (hb : ProductiveC b) :
    EQ2C_paco a b := by
  rcases hR with ⟨ρ, hResL, hVarR, hce⟩
  rw [← EQ2C_eq_paco_bot]
  exact EQ2CE_to_EQ2C' hce hResL hVarR ha hb

/-! ## Stub Definitions (Work in Progress)

These definitions and theorems are incomplete. Full proofs are being developed
in this file. The axioms below serve as placeholders for the public API.
-/

/-- Name assigned to a coinductive node in a finite system. -/
noncomputable def nameOf (c : LocalTypeC) (all : Finset LocalTypeC) : String :=
  match head c with
  | .mu x => x
  | _     => nameFor c all

/-- Environment generated from a finite system of nodes. -/
def envOf (all : Finset LocalTypeC) (_visited : Finset LocalTypeC) : EnvPair :=
  (fun x => { c | c ∈ all ∧ nameOf c all = x }, fun x => { mkVar x })

lemma envOf_varR (all visited : Finset LocalTypeC) : EnvVarR (envOf all visited) := by
  intro x c hmem
  simpa [envOf] using hmem

lemma envOf_resolvesL_of_backedge {all visited : Finset LocalTypeC}
    (hback : ∀ c ∈ all, EQ2C (mkVar (nameOf c all)) c) :
    EnvResolvesL (envOf all visited) := by
  intro x c hmem
  have hmem' : c ∈ all ∧ nameOf c all = x := by
    simpa [envOf] using hmem
  rcases hmem' with ⟨hmem_all, hname⟩
  have h := hback c hmem_all
  simpa [hname] using h

lemma envOf_resolves_of_backedge {all visited : Finset LocalTypeC}
    (hback : ∀ c ∈ all, EQ2C (mkVar (nameOf c all)) c) :
    EnvResolves (envOf all visited) :=
  EnvResolves_of_left_varR (envOf_resolvesL_of_backedge (all := all) (visited := visited) hback)
    (envOf_varR all visited)

/-! ## Round-Trip Theorems (Axioms - proofs in progress) -/

/-- Canonical round-trip: toCoind(toInductive(t)) is EQ2CE-equivalent to t. -/
axiom toCoind_toInductive_eq2ce (t : LocalTypeC) (h : Regular t) :
    EQ2CE (envOf (Set.Finite.toFinset h) (Set.Finite.toFinset h))
      (toCoind (toInductive t h)) t

/-- Erase environment awareness given back-edge resolution.
    Requires productivity of the RHS. -/
theorem toCoind_toInductive_eq2c_of_eq2ce (t : LocalTypeC) (h : Regular t)
    (hprod : ProductiveC t)
    (hback : ∀ c ∈ Set.Finite.toFinset h, EQ2C (mkVar (nameOf c (Set.Finite.toFinset h))) c)
    (hce : EQ2CE (envOf (Set.Finite.toFinset h) (Set.Finite.toFinset h))
             (toCoind (toInductive t h)) t) :
    EQ2C (toCoind (toInductive t h)) t := by
  have hEnvL :
      EnvResolvesL (envOf (Set.Finite.toFinset h) (Set.Finite.toFinset h)) :=
    envOf_resolvesL_of_backedge (all := Set.Finite.toFinset h)
      (visited := Set.Finite.toFinset h) hback
  have hEnvR : EnvVarR (envOf (Set.Finite.toFinset h) (Set.Finite.toFinset h)) :=
    envOf_varR (Set.Finite.toFinset h) (Set.Finite.toFinset h)
  have hprod_left : ProductiveC (toCoind (toInductive t h)) :=
    productive_toCoind (toInductive t h)
  exact EQ2CE_to_EQ2C' hce hEnvL hEnvR hprod_left hprod

/-- Round-trip in EQ2C assuming back-edge resolution.
    Requires productivity of the RHS. -/
theorem toCoind_toInductive_eq2c_of_backedge (t : LocalTypeC) (h : Regular t)
    (hprod : ProductiveC t)
    (hback : ∀ c ∈ Set.Finite.toFinset h, EQ2C (mkVar (nameOf c (Set.Finite.toFinset h))) c) :
    EQ2C (toCoind (toInductive t h)) t :=
  toCoind_toInductive_eq2c_of_eq2ce t h hprod hback (toCoind_toInductive_eq2ce t h)

/-- Round-trip in EQ2C assuming environment resolves back-edges.
    Requires productivity of the RHS. -/
theorem toCoind_toInductive_eq2c_of_env (t : LocalTypeC) (h : Regular t)
    (hprod : ProductiveC t)
    (hEnv : EnvResolves (envOf (Set.Finite.toFinset h) (Set.Finite.toFinset h))) :
    EQ2C (toCoind (toInductive t h)) t := by
  have hce := toCoind_toInductive_eq2ce t h
  have hprod_left : ProductiveC (toCoind (toInductive t h)) :=
    productive_toCoind (toInductive t h)
  have hEnvR : EnvVarR (envOf (Set.Finite.toFinset h) (Set.Finite.toFinset h)) :=
    envOf_varR (Set.Finite.toFinset h) (Set.Finite.toFinset h)
  exact EQ2CE_to_EQ2C' hce hEnv.1 hEnvR hprod_left hprod

/-- Round-trip in EQ2C for `toCoind` images, discharging productivity. -/
theorem toCoind_toInductive_eq2c_of_env_toCoind (t : LocalTypeR)
    (hEnv : EnvResolves
      (envOf (Set.Finite.toFinset (toCoind_regular t))
        (Set.Finite.toFinset (toCoind_regular t)))) :
    EQ2C (toCoind (toInductive (toCoind t) (toCoind_regular t))) (toCoind t) :=
  toCoind_toInductive_eq2c_of_env (t := toCoind t) (h := toCoind_regular t)
    (hprod := productive_toCoind t) hEnv

/-- Round-trip in EQ2C for `toCoind` images with explicit back-edge resolution. -/
theorem toCoind_toInductive_eq2c_of_backedge_toCoind (t : LocalTypeR)
    (hback : ∀ c ∈ Set.Finite.toFinset (toCoind_regular t),
      EQ2C (mkVar (nameOf c (Set.Finite.toFinset (toCoind_regular t)))) c) :
    EQ2C (toCoind (toInductive (toCoind t) (toCoind_regular t))) (toCoind t) :=
  toCoind_toInductive_eq2c_of_backedge (t := toCoind t) (h := toCoind_regular t)
    (hprod := productive_toCoind t) hback

/-- Canonical round-trip statement (alias). -/
theorem toCoind_toInductive (t : LocalTypeC) (h : Regular t) :
    EQ2CE (envOf (Set.Finite.toFinset h) (Set.Finite.toFinset h))
      (toCoind (toInductive t h)) t :=
  toCoind_toInductive_eq2ce t h

end RumpsteakV2.Coinductive
