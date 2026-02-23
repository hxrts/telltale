import Mathlib
import Paco
import SessionCoTypes.Coinductive.EQ2C

set_option linter.dupNamespace false


EQ2C is defined via an existentially quantified bisimulation, which makes
coinductive proofs awkward. The paco library provides a cleaner coinduction
principle through parametrized greatest fixed points.

The difficulty is connecting our observable-based bisimulation definition with
paco's monotone relation transformers. We need EQ2C = paco EQ2CMono ⊥.

Solution Structure.
1. Define EQ2C_step_paco wrapping ObservableRelC for paco
2. Prove monotonicity (eq2_c_step_mono)
3. Show EQ2C ≤ paco ⊥ by exhibiting the witness
4. Show paco ⊥ ≤ EQ2C by extracting the bisimulation
5. Conclude EQ2C = EQ2C_paco
-/

namespace SessionCoTypes.Coinductive

/-- One-step EQ2C relation for paco: observables match under `R`. -/
def EQ2C_step_paco (R : Paco.Rel LocalTypeC) : Paco.Rel LocalTypeC :=
  fun a b => ∃ _obs_a : ObservableC a, ∃ _obs_b : ObservableC b, ObservableRelC R a b

lemma eq2_c_step_mono : Paco.Monotone2 EQ2C_step_paco := by
  intro R S h a b hstep
  rcases hstep with ⟨obs_a, obs_b, hrel⟩
  exact ⟨obs_a, obs_b, observable_rel_c_mono (fun _ _ hr => h _ _ hr) hrel⟩

/-- `EQ2C_step_paco` bundled as a monotone relation transformer. -/
def EQ2CMono : Paco.MonoRel LocalTypeC where
  F := EQ2C_step_paco
  mono := eq2_c_step_mono

/-- paco characterization of `EQ2C` (with empty parameter). -/
def EQ2C_paco : LocalTypeC → LocalTypeC → Prop :=
  Paco.paco EQ2CMono ⊥

/-- EQ2C implies paco EQ2CMono ⊥. -/
theorem eq2_c_le_paco_bot : EQ2C ≤ EQ2C_paco := by
  intro a b h
  rcases h with ⟨R, hR, hab⟩
  refine ⟨R, ?_, hab⟩
  intro x y hxy
  obtain ⟨obs_x, obs_y, hobs⟩ := hR x y hxy
  refine ⟨obs_x, obs_y, ?_⟩
  -- lift ObservableRelC from R to R ⊔ ⊥
  exact observable_rel_c_mono (fun _ _ hr => Or.inl hr) hobs

/-- paco EQ2CMono ⊥ implies EQ2C. -/
theorem paco_bot_le_eq2_c : EQ2C_paco ≤ EQ2C := by
  intro a b ⟨R, hR, hab⟩
  refine ⟨R, ?_, hab⟩
  intro x y hxy
  have hstep := hR x y hxy
  rcases hstep with ⟨obs_x, obs_y, hobs⟩
  -- R ⊔ ⊥ = R
  simp only [Paco.Rel.sup_bot] at hobs
  exact ⟨obs_x, obs_y, hobs⟩

/-- EQ2C equals paco EQ2CMono ⊥. -/
theorem eq2_c_eq_paco_bot : EQ2C = EQ2C_paco :=
  Paco.Rel.le_antisymm eq2_c_le_paco_bot paco_bot_le_eq2_c

/-- Convert paco result back to EQ2C when the parameter is empty. -/
theorem paco_to_eq2_c {a b : LocalTypeC} (h : EQ2C_paco a b) : EQ2C a b :=
  paco_bot_le_eq2_c a b h

end SessionCoTypes.Coinductive
