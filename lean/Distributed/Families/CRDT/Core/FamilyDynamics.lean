import Distributed.Families.CRDT.Core.OpCoreErasure

/-! # CRDT Family Dynamics and Adequacy

In-scope CRDT family adequacy theorems proving that Register, Counter,
and OR-Set families lower to `OpCore` with observable and envelope
preservation. -/

/-
The Problem. Each CRDT family (Register, Counter, OR-Set) has its own
rich operation type, but must lower to the common `OpCore` representation
for uniform protocol machine execution. We need adequacy theorems ensuring the lowering
preserves observable behavior and stays within the CRDT envelope.

Solution Structure. Define `InScopeFamiliesAdequacy` bundling lowering
adequacy for each family. Prove `in_scope_families_adequate` combining
individual adequacy witnesses. Provide `CoreRepresentableFamily` instances
for uniform interface.
-/

set_option autoImplicit false

namespace Distributed
namespace CRDT

universe u v w x y z

/-! ## In-Scope Families Adequacy -/

structure InScopeFamiliesAdequacy
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program)
    (RegisterRich CounterRich ORSetRich : Type z)
    (OpTag : Type v) (Args : Type w) where
  register : FamilyLoweringAdequacy M RegisterRich OpTag Args
  counter : FamilyLoweringAdequacy M CounterRich OpTag Args
  orset : FamilyLoweringAdequacy M ORSetRich OpTag Args

/-- Main adequacy theorem: every in-scope family lowers to `OpCore` with
observable and envelope preservation. -/
theorem in_scope_families_adequate
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    {RegisterRich CounterRich ORSetRich : Type z}
    {OpTag : Type v} {Args : Type w}
    (A : InScopeFamiliesAdequacy M RegisterRich CounterRich ORSetRich OpTag Args) :
    FamilyEnvelopeAdequate M A.register ∧
    FamilyEnvelopeAdequate M A.counter ∧
    FamilyEnvelopeAdequate M A.orset := by
  refine ⟨family_envelope_adequate_of_lowering A.register, ?_⟩
  exact ⟨family_envelope_adequate_of_lowering A.counter,
    family_envelope_adequate_of_lowering A.orset⟩

/-! ## Rich Family Fragments -/

/-- Register CRDT rich fragment for in-scope lowering adequacy. -/
inductive RegisterRich (OpTag : Type v) (Args : Type w) where
  | op : OpCore OpTag Args → RegisterRich OpTag Args
  deriving Repr, DecidableEq, Inhabited

/-- Counter CRDT rich fragment for in-scope lowering adequacy. -/
inductive CounterRich (OpTag : Type v) (Args : Type w) where
  | op : OpCore OpTag Args → CounterRich OpTag Args
  deriving Repr, DecidableEq, Inhabited

/-- OR-Set CRDT rich fragment for in-scope lowering adequacy. -/
inductive ORSetRich (OpTag : Type v) (Args : Type w) where
  | op : OpCore OpTag Args → ORSetRich OpTag Args
  deriving Repr, DecidableEq, Inhabited

/-! ## Core-Representable Instances -/

instance instCoreRepresentableFamilyRegisterRich
    {OpTag : Type v} {Args : Type w} :
    CoreRepresentableFamily (RegisterRich OpTag Args) OpTag Args where
  toCore
  | .op kc => kc
  ofCore kc := .op kc
  toCore_ofCore _ := rfl
  ofCore_toCore
  | .op _ => rfl

instance instCoreRepresentableFamilyCounterRich
    {OpTag : Type v} {Args : Type w} :
    CoreRepresentableFamily (CounterRich OpTag Args) OpTag Args where
  toCore
  | .op kc => kc
  ofCore kc := .op kc
  toCore_ofCore _ := rfl
  ofCore_toCore
  | .op _ => rfl

instance instCoreRepresentableFamilyORSetRich
    {OpTag : Type v} {Args : Type w} :
    CoreRepresentableFamily (ORSetRich OpTag Args) OpTag Args where
  toCore
  | .op kc => kc
  ofCore kc := .op kc
  toCore_ofCore _ := rfl
  ofCore_toCore
  | .op _ => rfl

/-! ## Lowering Adequacy Constructors -/

/-- Lowering adequacy witness for in-scope register family. -/
def registerLoweringAdequacy
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program)
    {OpTag : Type v} {Args : Type w}
    (interp : OpCoreInterpreter State Context OpTag Args) :
    FamilyLoweringAdequacy M (RegisterRich OpTag Args) OpTag Args :=
  { interp := interp
  , evalRich := evalRichCoreRepresentable interp
  , lower := lowerCoreRepresentable
  , totalLowering := lower_core_representable_total
  , stepObsPreserved := step_obs_preserved_core_representable M interp
  }

/-- Lowering adequacy witness for in-scope counter family. -/
def counterLoweringAdequacy
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program)
    {OpTag : Type v} {Args : Type w}
    (interp : OpCoreInterpreter State Context OpTag Args) :
    FamilyLoweringAdequacy M (CounterRich OpTag Args) OpTag Args :=
  { interp := interp
  , evalRich := evalRichCoreRepresentable interp
  , lower := lowerCoreRepresentable
  , totalLowering := lower_core_representable_total
  , stepObsPreserved := step_obs_preserved_core_representable M interp
  }

/-- Lowering adequacy witness for in-scope OR-Set family. -/
def orsetLoweringAdequacy
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program)
    {OpTag : Type v} {Args : Type w}
    (interp : OpCoreInterpreter State Context OpTag Args) :
    FamilyLoweringAdequacy M (ORSetRich OpTag Args) OpTag Args :=
  { interp := interp
  , evalRich := evalRichCoreRepresentable interp
  , lower := lowerCoreRepresentable
  , totalLowering := lower_core_representable_total
  , stepObsPreserved := step_obs_preserved_core_representable M interp
  }

/-- Concrete in-scope adequacy bundle for register/counter/OR-set families. -/
def inScopeFamiliesAdequacyCoreRepresentable
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program)
    {OpTag : Type v} {Args : Type w}
    (registerInterp counterInterp orsetInterp :
      OpCoreInterpreter State Context OpTag Args) :
    InScopeFamiliesAdequacy M (RegisterRich OpTag Args) (CounterRich OpTag Args)
      (ORSetRich OpTag Args) OpTag Args :=
  { register := registerLoweringAdequacy M registerInterp
  , counter := counterLoweringAdequacy M counterInterp
  , orset := orsetLoweringAdequacy M orsetInterp
  }

/-! ## In-Scope Adequacy Theorem -/

/-- Concrete adequacy theorem for representative in-scope CRDT families. -/
theorem in_scope_families_adequate_core_representable
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    {OpTag : Type v} {Args : Type w}
    (registerInterp counterInterp orsetInterp :
      OpCoreInterpreter State Context OpTag Args) :
    let A := inScopeFamiliesAdequacyCoreRepresentable M registerInterp counterInterp orsetInterp
    FamilyEnvelopeAdequate M A.register ∧
      FamilyEnvelopeAdequate M A.counter ∧
      FamilyEnvelopeAdequate M A.orset := by
  intro A
  exact in_scope_families_adequate A

/-! ## Core Hypothesis (`H_crdt_core`) -/

/-- `H_crdt_core`: merge is a commutative, associative, idempotent join, and
updates are inflationary and monotone. Every `Model` satisfies it
(`hcrdt_core_of_model`), because `Model.lattice` carries the lattice laws. -/
def HcrdtCore
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program) : Prop :=
  (∀ a b, M.lattice.join a b = M.lattice.join b a) ∧
  (∀ a b c, M.lattice.join (M.lattice.join a b) c = M.lattice.join a (M.lattice.join b c)) ∧
  (∀ a, M.lattice.join a a = a) ∧
  (∀ o s, M.lattice.le s (M.apply o s)) ∧
  (∀ o {s t}, M.lattice.le s t → M.lattice.le (M.apply o s) (M.apply o t))

/-- Every CRDT model satisfies `H_crdt_core`. -/
theorem hcrdt_core_of_model
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program) : HcrdtCore M :=
  ⟨M.lattice.join_comm, M.lattice.join_assoc, M.lattice.join_idem,
    M.apply_inflationary, fun o _ _ h => M.apply_monotone o h⟩

/-! ## Convergence-Distance Non-Canonicity -/

/-- Grow-only max-register model with 0/1 convergence distance. -/
def foundationModelDistance01 : Model Nat Unit Unit Nat Unit where
  observe := fun s => s
  distance := fun s₁ s₂ => if s₁ = s₂ then 0 else 1
  lattice := natMaxCRDT
  effect := fun _ => 1

/-- Companion model with the same lattice/observables and a 0/2 distance. -/
def foundationModelDistance02 : Model Nat Unit Unit Nat Unit where
  observe := fun s => s
  distance := fun s₁ s₂ => if s₁ = s₂ then 0 else 2
  lattice := natMaxCRDT
  effect := fun _ => 1

/-- The convergence distance is not determined by lattice, updates, and
observables: two models agreeing on all of them differ in `distance`. -/
theorem dconv_noncanonicity_counterexample :
    (∀ s, foundationModelDistance01.observe s = foundationModelDistance02.observe s) ∧
      (∃ s₁ s₂, foundationModelDistance01.distance s₁ s₂ ≠
        foundationModelDistance02.distance s₁ s₂) :=
  ⟨fun _ => rfl, 0, 1, by simp [foundationModelDistance01, foundationModelDistance02]⟩

/-! ## Dynamics Hypothesis Analysis (`H_crdt_dynamics`) -/

/-- Run-level formalization of a mixing-time claim (eventual constancy). -/
def MixingTimeControlledRun (r : Run Nat) : Prop :=
  ∃ τ, ∀ t, τ ≤ t → r t = r τ

/-- Run-level formalization of hotspot slow-mode boundedness. -/
def HotspotSlowModeBoundedRun (r : Run Nat) : Prop :=
  ∃ B, ∀ t, r t ≤ B

/-- Run-level formalization of drift decay (eventual non-increasing trend). -/
def DriftDecayRun (r : Run Nat) : Prop :=
  ∃ τ, ∀ t, τ ≤ t → r (t + 1) ≤ r t

/-- Counterexample trace used to refute unconditional dynamics bounds. -/
def unboundedCounterexampleRun : Run Nat :=
  fun t => t

/-- Counterexample: the unbounded run does not satisfy mixing-time stabilization. -/
theorem unbounded_run_not_mixing_time_controlled :
    ¬ MixingTimeControlledRun unboundedCounterexampleRun := by
  intro hMix
  rcases hMix with ⟨τ, hτ⟩
  have hEq : unboundedCounterexampleRun (τ + 1) = unboundedCounterexampleRun τ :=
    hτ (τ + 1) (Nat.le_add_right τ 1)
  have hContra : τ + 1 = τ := by
    simp [unboundedCounterexampleRun] at hEq
  exact Nat.succ_ne_self τ hContra

/-- Counterexample: the unbounded run violates hotspot boundedness. -/
theorem unbounded_run_not_hotspot_bounded :
    ¬ HotspotSlowModeBoundedRun unboundedCounterexampleRun := by
  intro hBounded
  rcases hBounded with ⟨B, hB⟩
  have hLe : unboundedCounterexampleRun (B + 1) ≤ B := hB (B + 1)
  have hContra : B + 1 ≤ B := by
    simpa [unboundedCounterexampleRun] using hLe
  exact Nat.not_succ_le_self B hContra

/-- Counterexample: the unbounded run does not satisfy drift decay. -/
theorem unbounded_run_not_drift_decay :
    ¬ DriftDecayRun unboundedCounterexampleRun := by
  intro hDecay
  rcases hDecay with ⟨τ, hτ⟩
  have hLe : unboundedCounterexampleRun (τ + 1) ≤ unboundedCounterexampleRun τ :=
    hτ τ (Nat.le_refl τ)
  have hContra : τ + 1 ≤ τ := by
    simpa [unboundedCounterexampleRun] using hLe
  exact Nat.not_succ_le_self τ hContra

/-- Refutation bundle for `H_crdt_dynamics` without explicit dissemination/fairness assumptions. -/
theorem hcrdt_dynamics_counterexample_traces :
    ¬ MixingTimeControlledRun unboundedCounterexampleRun ∧
      ¬ HotspotSlowModeBoundedRun unboundedCounterexampleRun ∧
      ¬ DriftDecayRun unboundedCounterexampleRun := by
  exact ⟨unbounded_run_not_mixing_time_controlled,
    unbounded_run_not_hotspot_bounded, unbounded_run_not_drift_decay⟩

end CRDT
end Distributed
