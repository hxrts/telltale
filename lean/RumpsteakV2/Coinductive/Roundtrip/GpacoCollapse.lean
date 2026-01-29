import RumpsteakV2.Coinductive.EQ2C
import RumpsteakV2.Coinductive.EQ2CMu
import RumpsteakV2.Coinductive.Roundtrip.Part1

/-!
The Problem. The round-trip proof currently uses ProductiveC to turn
EQ2C_mu_paco into EQ2C_paco. We want to test whether gpaco closures can
provide the observable relation needed for the coinductive step without
assuming productivity.

The difficulty is that ObservableRelC depends on the underlying relation,
so we need a clean way to lift observability from EQ2C_mu_paco to a gpaco
closure, and then collapse to paco via bisimulation.

Solution Structure.
1. Define the gpaco closure relation (GpacoRel).
2. Lift observability from EQ2C_mu_paco to GpacoRel.
3. Show: if GpacoRel is a bisimulation, then μ-paco collapses to paco.
-/

namespace RumpsteakV2.Coinductive

open Paco

/-! ## gpaco closure relation -/

/-- gpaco closure of EQ2C_mu_paco with explicit mu-closure. -/
def GpacoRel : LocalTypeC → LocalTypeC → Prop :=
  -- Use gupaco_clo to wrap mu-paco with a guarded closure.
  Paco.gupaco_clo EQ2CMono mu_clo EQ2C_mu_paco

/-! ## Observability lift -/

/-- Lift ObservableRelC from EQ2C_mu_paco to the gpaco closure.

This is the crux needed for the gpaco-based collapse: once observability
is preserved under the gpaco closure, the coinductive step can proceed
without ProductiveC assumptions. -/
theorem mu_paco_obs_to_gpaco {a b : LocalTypeC}
    (ha : ObservableC a) (hb : ObservableC b) (h : EQ2C_mu_paco a b) :
    ObservableRelC GpacoRel a b := by
  -- Step 1: obtain observability under EQ2C_mu_paco.
  have hobs : ObservableRelC EQ2C_mu_paco a b :=
    EQ2C_mu_paco_to_obs ha hb h
  -- Step 2: lift the relation from EQ2C_mu_paco to GpacoRel.
  have hle : ∀ x y, EQ2C_mu_paco x y → GpacoRel x y := by
    intro x y hx
    -- r_le_gpaco_clo embeds the base relation into the gpaco closure.
    have h' := Paco.r_le_gpaco_clo EQ2CMono mu_clo EQ2C_mu_paco EQ2C_mu_paco x y hx
    simpa [Paco.gupaco_clo_def] using h'
  -- Step 3: apply monotonicity of ObservableRelC.
  exact ObservableRelC_mono hle hobs

/-! ## gpaco collapse under bisimulation -/

/-- Embed μ-paco into the gpaco closure. -/
theorem mu_paco_to_gpaco {a b : LocalTypeC} (h : EQ2C_mu_paco a b) :
    GpacoRel a b := by
  -- Use r_le_gpaco_clo to inject the base relation.
  have h' := Paco.r_le_gpaco_clo EQ2CMono mu_clo EQ2C_mu_paco EQ2C_mu_paco a b h
  simpa [Paco.gupaco_clo_def] using h'

/-- Extract observability from an observable relation. -/
lemma observable_of_ObservableRelC {R : LocalTypeC → LocalTypeC → Prop}
    {a b : LocalTypeC} (hrel : ObservableRelC R a b) :
    ObservableC a ∧ ObservableC b := by
  -- Each observable case witnesses observability on both sides.
  cases hrel with
  | is_end ha hb => exact ⟨ObservableC.is_end ha, ObservableC.is_end hb⟩
  | is_var v ha hb => exact ⟨ObservableC.is_var v ha, ObservableC.is_var v hb⟩
  | is_send p bs cs ha hb _ =>
      exact ⟨ObservableC.is_send p bs ha, ObservableC.is_send p cs hb⟩
  | is_recv p bs cs ha hb _ =>
      exact ⟨ObservableC.is_recv p bs ha, ObservableC.is_recv p cs hb⟩

/-- If GpacoRel is a bisimulation, it collapses to EQ2C_paco. -/
theorem gpaco_to_paco_of_bisim
    (hbis : IsBisimulationC GpacoRel) {a b : LocalTypeC} (h : GpacoRel a b) :
    EQ2C_paco a b := by
  -- Coinduction: show GpacoRel is a post-fixpoint of EQ2CMono.
  refine Paco.paco_coind EQ2CMono GpacoRel ⊥ ?_ h
  intro x y hxy
  -- Use bisimulation to produce observables and an observable relation.
  rcases hbis x y hxy with ⟨obs_x, obs_y, hrel⟩
  -- Lift the relation into the paco step relation (R ⊔ ⊥).
  have hrel' : ObservableRelC (GpacoRel ⊔ ⊥) x y :=
    ObservableRelC_mono (fun _ _ hr => Or.inl hr) hrel
  exact ⟨obs_x, obs_y, hrel'⟩

/-- Collapse μ-paco to paco assuming GpacoRel is a bisimulation. -/
theorem mu_paco_le_paco_of_bisim
    (hbis : IsBisimulationC GpacoRel) {a b : LocalTypeC} (h : EQ2C_mu_paco a b) :
    EQ2C_paco a b := by
  -- Embed into gpaco and reuse the coinduction lemma.
  exact gpaco_to_paco_of_bisim hbis (mu_paco_to_gpaco h)

/-- If μ-paco steps are observable under GpacoRel, then μ-paco collapses to paco. -/
theorem mu_paco_le_paco_of_obs
    (hrr : ∀ a b, EQ2C_mu_paco a b → ObservableRelC GpacoRel a b)
    {a b : LocalTypeC} (h : EQ2C_mu_paco a b) :
    EQ2C_paco a b := by
  -- Build the bisimulation from the observable-step hypothesis.
  have hbis : IsBisimulationC GpacoRel := by
    intro x y hxy
    have hrel : ObservableRelC GpacoRel x y := gupaco_clo_obs_of_rr hrr hxy
    have hobs := observable_of_ObservableRelC hrel
    exact ⟨hobs.1, hobs.2, hrel⟩
  -- Collapse using the bisimulation.
  exact mu_paco_le_paco_of_bisim hbis h

end RumpsteakV2.Coinductive
