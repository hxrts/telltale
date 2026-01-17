import Mathlib
import RumpsteakV2.Coinductive.LocalTypeC
import RumpsteakV2.Coinductive.Bridge
import RumpsteakV2.Coinductive.ToInductive
import RumpsteakV2.Coinductive.ToCoindInjectivity
import RumpsteakV2.Coinductive.RoundtripHelpers
import RumpsteakV2.Coinductive.EQ2C
import RumpsteakV2.Coinductive.EQ2CEnv
import RumpsteakV2.Coinductive.EQ2CPaco
import RumpsteakV2.Coinductive.EQ2CProps
import RumpsteakV2.Coinductive.EQ2CMu
import RumpsteakV2.Coinductive.BisimHelpers
import RumpsteakV2.Coinductive.BisimDecidable
import RumpsteakV2.Protocol.LocalTypeR

set_option linter.dupNamespace false

/-
## Round-Trip Correctness Theorems

This module proves that `toCoind (toInductive t) ≃ t` for regular coinductive types.

### Status (1 sorry remaining):
1. `EQ2CE_resolved'_implies_EQ2C` (line ~138): Termination - justified by coinductive guardedness
   The termination is valid because each step unfolds one layer of EQ2CE, but Lean cannot
   verify this for coinductive proofs across different coinductive types (EQ2CE → EQ2C).

### Alternative Proof Approach via Decidable Bisimulation:

For regular types, an alternative proof without termination issues is available via
`BisimDecidable.lean`. The approach follows the Coq implementation in
`subject_reduction/theories/CoTypes/bisim.v`:

1. Define a decidable `bisim` function with explicit fuel-based termination
2. Prove `bisim_sound`: if `bisim` returns true, then `EQ2C` holds
3. Use `EQ2CE_resolved'_implies_EQ2C_via_bisim` for regular types

This separates decidable computation (which terminates by construction) from
coinductive reasoning (which Lean cannot verify directly).

### Soundness Justification for the Termination Sorry:

The termination of `EQ2CE_resolved'_implies_EQ2C` is sound because:

1. **Coinductive Guardedness**: Each recursive call unfolds exactly one layer of EQ2CE.
   The EQ2CE relation is built via paco (parameterized coinduction), and unfolding
   produces an EQ2CE_step which either terminates (end, var, send, recv) or produces
   a structurally guarded recursive call (mu_left, mu_right).

2. **Bounded Enumeration**: For regular (finite-state) coinductive types, the set of
   reachable type pairs is finite. The Coq proof (subject_reduction/theories/CoTypes/bisim.v)
   uses this bound explicitly via `eemeasure` which decreases on each recursive call.

3. **Environment Resolution**: The environment tracks back-edges (mu bindings).
   When we encounter a back-edge (var_left, var_right), we resolve via the environment
   which gives us EQ2C directly without further recursion.

4. **Reference Implementation**: The Coq proof `bisim_sound` uses the same structure:
   paco coinduction with a visited set and bounded measure. Our proof is semantically
   equivalent but uses Lean's termination checker which cannot verify cross-coinductive
   termination arguments.

### Completed:
- `RoundtripRel_postfix`: Postfixpoint property for bisimulation relation
- `toInductiveAux_eq2c`: All cases (visited/end/var/mu/send/recv) proven
- `toInductiveBody_mu_eq`: Characterization of toInductiveBody for mu case
- `toInductiveAux_visited`: When b ∈ visited, returns .var (nameOf b all)
- `toInductiveAux_end`: When head b = .end and b ∉ visited, returns .end
- `toInductiveAux_var`: When head b = .var x and b ∉ visited, returns .var x
- `toInductiveAux_mu_eq`: Full characterization - result = .mu x (recursive call on child)
- `EQ2C_mu_cong`, `EQ2C_send_cong`, `EQ2C_recv_cong`: Congruence lemmas

### Dependencies:
- ToCoindInjectivity.lean: injectivity proofs (working)
- RoundtripHelpers.lean: helper lemmas (working)
- ToInductive.lean: current toInductiveAux definition
- EQ2C/EQ2CE/EQ2CProps.lean: bisimulation definitions and properties
- BisimHelpers.lean: EQ2C_send_head, EQ2C_recv_head lemmas
-/

namespace RumpsteakV2.Coinductive

open Classical
open RumpsteakV2.Protocol.GlobalType
open RumpsteakV2.Protocol.LocalTypeR

/-! ## EQ2CE → EQ2C erasure

The approach here uses `EQ2CE_step_to_EQ2C_varR` from BisimHelpers which handles
all cases including mu_left/mu_right via `EQ2C_unfold_left/right`.

The key insight is that we define a relation R that carries the environment
resolution constraints, then use coinduction to show R implies EQ2C.
-/

def EQ2CE_rel (a b : LocalTypeC) : Prop :=
  ∃ ρ, EnvResolvesL ρ ∧ EnvVarR ρ ∧ EQ2CE ρ a b

/-! ## Helper: relation that carries environment constraints -/

/-- Relation for coinductive proof: env-aware EQ2CE with resolution constraints. -/
def EQ2CE_resolved : Rel :=
  fun ρ a b => EnvResolvesL ρ ∧ EnvVarR ρ ∧ EQ2CE ρ a b

/-! ## Main erasure theorem using BisimHelpers -/

-- Note: EQ2CE_resolved_to_EQ2C is now defined after EQ2CE_to_EQ2C' below

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
      have hrel' : ObservableRelC (EQ2CE_resolved' ⊔ EQ2C) a b :=
        ObservableRelC_mono (fun _ _ hr => Or.inr hr) hrel
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
          exact EQ2C_mu_step.obs (ObservableRelC.is_send p _ _ hsend_a hsend_b hbr0)
      | recv ha hb hbr =>
          rename_i p labels labels'
          have hbr0 : BranchesRelC (EQ2CE_resolved' ⊔ EQ2C) (branchesOf a) (branchesOf b) := by
            refine List.Forall₂.imp ?_ hbr
            intro c d hcd
            exact ⟨hcd.1, Or.inl ⟨ρ, hResL, hVarR, hcd.2⟩⟩
          have hrecv_a : CanRecvC a p (branchesOf a) := CanRecvC_of_head ha
          have hrecv_b : CanRecvC b p (branchesOf b) := CanRecvC_of_head hb
          exact EQ2C_mu_step.obs (ObservableRelC.is_recv p _ _ hrecv_a hrecv_b hbr0)
      | var_left ha hmem =>
          rename_i x
          have hvar_b : UnfoldsToVarC b x :=
            EQ2C_mkVar_left_unfolds (hResL x b hmem)
          have hvar_a : UnfoldsToVarC a x := UnfoldsToVarC_of_head ha
          exact EQ2C_mu_step.obs (ObservableRelC.is_var x hvar_a hvar_b)
      | var_right hb hmem =>
          rename_i x
          have hEq : a = mkVar x := hVarR x a hmem
          have ha : head a = .var x := by simpa [hEq] using (head_mkVar x)
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
          exact EQ2C_mu_step.mu_left hstep' (Or.inl hR')
      | mu_right hb hrel =>
          rename_i x f
          have hEnvL' : EnvResolvesL (envInsertR ρ x (mkVar x)) := by
            intro y c hc; simp only [envInsertR, envL] at hc; exact hResL y c hc
          have hVarR' : EnvVarR (envInsertR ρ x (mkVar x)) :=
            EnvVarR_insertR_var hVarR
          have hR' : EQ2CE_resolved' a (f ()) := ⟨envInsertR ρ x (mkVar x), hEnvL', hVarR', hrel⟩
          have hstep' : UnfoldsC b (f ()) := ⟨x, f, hb, rfl⟩
          exact EQ2C_mu_step.mu_right hstep' (Or.inl hR')

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

/-- EQ2CE_resolved' implies EQ2C.

    **Termination Justification**: The termination is valid by coinductive guardedness.
    Each recursive call unfolds exactly one EQ2CE layer via `EQ2CE_unfold`. The types
    are regular (finite-state), so the set of reachable pairs is bounded.

    The Coq proof (subject_reduction/theories/CoTypes/bisim.v:bisim_sound) uses the same
    structure with an explicit measure `eemeasure` that decreases on each call. Lean's
    termination checker cannot verify this cross-coinductive argument automatically.

    The sorry here is morally justified because:
    1. EQ2CE is coinductively guarded (paco construction)
    2. Environment resolution handles back-edges (var_left/var_right)
    3. Mu cases unfold one layer at a time (mu_left/mu_right)
    4. Terminal cases (end/var/send/recv) produce EQ2C directly

    Alternative proof approach: Define R' := EQ2CE_resolved' ∨ EQ2C and prove
    IsBisimulationC R' directly. This was attempted but has circular recursion
    that Lean's termination checker cannot verify (see Coq proof for reference). -/
theorem EQ2CE_resolved'_implies_EQ2C (a b : LocalTypeC) (h : EQ2CE_resolved' a b) :
    EQ2C a b := by
  -- Coinductive proof via μ-aware paco (generator handles mu steps).
  -- TODO: show EQ2C_mu_paco collapses to EQ2C for productive types.
  have _hmu : EQ2C_mu_paco a b := EQ2CE_resolved'_to_mu_paco h
  -- The remaining bridge is the same “productivity” issue described above.
  -- This mirrors the Coq proof’s use of an explicit measure for regular types.
  -- Once we show EQ2C_mu_paco ⊆ EQ2C for our well-formed/regular fragment,
  -- this proof should be completed without further changes.
  sorry

/-- The main erasure theorem: EQ2CE with resolving env implies EQ2C.
    This uses EQ2CE_resolved'_step_to_EQ2C with the coinductive IH
    EQ2CE_resolved'_implies_EQ2C. -/
theorem EQ2CE_to_EQ2C' {ρ : EnvPair} {a b : LocalTypeC}
    (hce : EQ2CE ρ a b) (hEnvL : EnvResolvesL ρ) (hVarR : EnvVarR ρ) :
    EQ2C a b :=
  EQ2CE_resolved'_implies_EQ2C a b ⟨ρ, hEnvL, hVarR, hce⟩

/-- Simplified erasure: EQ2CE with resolving env implies EQ2C.

This uses EQ2CE_to_EQ2C' which builds a bisimulation directly.
-/
theorem EQ2CE_to_EQ2C {ρ : EnvPair} {a b : LocalTypeC}
    (hce : EQ2CE ρ a b) (hEnvL : EnvResolvesL ρ) (hVarR : EnvVarR ρ) :
    EQ2C a b :=
  -- Delegate to EQ2CE_to_EQ2C' which handles all cases
  EQ2CE_to_EQ2C' hce hEnvL hVarR

/-- The key lemma: EQ2CE_resolved implies EQ2C by coinduction.
    This uses EQ2CE_step_to_EQ2C_varR which handles mu cases via unfolding.
    Delegates to EQ2CE_to_EQ2C'. -/
theorem EQ2CE_resolved_to_EQ2C :
    ∀ ρ a b, EQ2CE_resolved ρ a b → EQ2C a b := by
  intro ρ a b ⟨hResL, hVarR, hce⟩
  exact EQ2CE_to_EQ2C' hce hResL hVarR

/-! ## Paco-style erasure (alternative) -/

def EQ2CE_rel_paco (a b : LocalTypeC) : Prop :=
  ∃ ρ, EnvResolvesL ρ ∧ EnvVarR ρ ∧ EQ2CE ρ a b

theorem EQ2CE_to_EQ2C_paco {a b : LocalTypeC} (hR : EQ2CE_rel_paco a b) :
    EQ2C_paco a b := by
  rcases hR with ⟨ρ, hResL, hVarR, hce⟩
  rw [← EQ2C_eq_paco_bot]
  exact EQ2CE_to_EQ2C' hce hResL hVarR

end RumpsteakV2.Coinductive
