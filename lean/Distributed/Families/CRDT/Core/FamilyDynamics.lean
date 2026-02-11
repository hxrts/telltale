import Distributed.Families.CRDT.Core.OpCoreErasure

/-! # CRDT Family Dynamics and Adequacy

In-scope CRDT family adequacy theorems proving that Register, Counter,
and OR-Set families lower to `OpCore` with observable and envelope
preservation. -/

/-
The Problem. Each CRDT family (Register, Counter, OR-Set) has its own
rich operation type, but must lower to the common `OpCore` representation
for uniform VM execution. We need adequacy theorems ensuring the lowering
preserves observable behavior and stays within the CRDT envelope.

Solution Structure. Define `InScopeFamiliesAdequacy` bundling lowering
adequacy for each family. Prove `inScopeFamilies_adequate` combining
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
theorem inScopeFamilies_adequate
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    {RegisterRich CounterRich ORSetRich : Type z}
    {OpTag : Type v} {Args : Type w}
    (A : InScopeFamiliesAdequacy M RegisterRich CounterRich ORSetRich OpTag Args) :
    FamilyEnvelopeAdequate M A.register ∧
    FamilyEnvelopeAdequate M A.counter ∧
    FamilyEnvelopeAdequate M A.orset := by
  refine ⟨familyEnvelopeAdequate_of_lowering A.register, ?_⟩
  exact ⟨familyEnvelopeAdequate_of_lowering A.counter,
    familyEnvelopeAdequate_of_lowering A.orset⟩

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
  , totalLowering := lowerCoreRepresentable_total
  , stepObsPreserved := stepObsPreserved_coreRepresentable M interp
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
  , totalLowering := lowerCoreRepresentable_total
  , stepObsPreserved := stepObsPreserved_coreRepresentable M interp
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
  , totalLowering := lowerCoreRepresentable_total
  , stepObsPreserved := stepObsPreserved_coreRepresentable M interp
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

/-- Concrete adequacy theorem for representative in-scope CRDT families. -/
theorem inScopeFamilies_adequate_coreRepresentable
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
  exact inScopeFamilies_adequate A

/-- Hypothesis block matching `H_crdt_core`. -/
def HcrdtCore
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program) : Prop :=
  M.semilatticeCoreClass ∧ M.opContextLayerClass

/-- Semilattice-only foundation predicate in the `H_crdt_core` analysis. -/
def SemilatticeOnlyFoundation
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program) : Prop :=
  M.semilatticeCoreClass

/-- Distinct primitive algebra required for op-context CRDT correctness. -/
def OpContextPrimitiveAlgebra
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program) : Prop :=
  M.opContextLayerClass

/-- Adequacy theorem: `H_crdt_core` is exactly semilattice + op-context primitive algebra. -/
theorem hcrdtCore_iff_semilattice_plus_opContext
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program} :
    HcrdtCore M ↔
      (SemilatticeOnlyFoundation M ∧ OpContextPrimitiveAlgebra M) := by
  rfl

/-- Concrete model where semilattice and op-context layers are both present. -/
def semilatticeWithOpContextModel : Model Nat Unit Unit Nat Unit where
  observe := natUnitModel.observe
  distance := natUnitModel.distance
  semilatticeCoreClass := True
  opContextLayerClass := True
  minimalOpStateEquivalenceAssumptions := True
  canonicalConvergenceDistanceClass := True
  mixingTimeControlledClass := True
  hotspotSlowModesClass := True
  driftDecayClass := True
  sequenceSubclassClass := True
  epochBarrierClass := True
  boundedMetadataApproxClass := True
  multiscaleObservablesClass := True
  metadataTradeoffFrontierClass := True
  gcCausalDominanceClass := True
  stabilizationLowerBoundClass := True

/-- Concrete model where semilattice core exists but op-context layer is absent. -/
def semilatticeOnlyNoOpContextModel : Model Nat Unit Unit Nat Unit where
  observe := natUnitModel.observe
  distance := natUnitModel.distance
  semilatticeCoreClass := True
  opContextLayerClass := False
  minimalOpStateEquivalenceAssumptions := True
  canonicalConvergenceDistanceClass := True
  mixingTimeControlledClass := True
  hotspotSlowModesClass := True
  driftDecayClass := True
  sequenceSubclassClass := True
  epochBarrierClass := True
  boundedMetadataApproxClass := True
  multiscaleObservablesClass := True
  metadataTradeoffFrontierClass := True
  gcCausalDominanceClass := True
  stabilizationLowerBoundClass := True

/-- Refutation witness: semilattice-only foundations do not imply op-context algebra. -/
theorem semilatticeOnly_not_sufficient_for_opContext :
    SemilatticeOnlyFoundation semilatticeOnlyNoOpContextModel ∧
      ¬ OpContextPrimitiveAlgebra semilatticeOnlyNoOpContextModel := by
  simp [SemilatticeOnlyFoundation, OpContextPrimitiveAlgebra, semilatticeOnlyNoOpContextModel]

/-- Universal refutation of deriving op-context from semilattice-only assumptions. -/
theorem hcrdtCore_refute_semilatticeOnly_derivation :
    ¬ (∀ M : Model Nat Unit Unit Nat Unit,
      SemilatticeOnlyFoundation M → OpContextPrimitiveAlgebra M) := by
  intro hDerive
  have hSemi : SemilatticeOnlyFoundation semilatticeOnlyNoOpContextModel := by
    simp [SemilatticeOnlyFoundation, semilatticeOnlyNoOpContextModel]
  have hOp : OpContextPrimitiveAlgebra semilatticeOnlyNoOpContextModel :=
    hDerive semilatticeOnlyNoOpContextModel hSemi
  simp [OpContextPrimitiveAlgebra, semilatticeOnlyNoOpContextModel] at hOp

/-- Distinct op-context primitive algebra is sufficient together with semilattice core. -/
theorem hcrdtCore_of_semilattice_plus_opContext
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program} :
    SemilatticeOnlyFoundation M ∧ OpContextPrimitiveAlgebra M → HcrdtCore M := by
  intro h
  exact h

/-- Hypothesis block matching `H_crdt_foundation`. -/
def HcrdtFoundation
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program) : Prop :=
  M.minimalOpStateEquivalenceAssumptions ∧ M.canonicalConvergenceDistanceClass

/-- Minimal assumption block for op/state equivalence analysis. -/
def MinimalOpStateConditions
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program) : Prop :=
  M.minimalOpStateEquivalenceAssumptions

/-- Canonical convergence-distance assumption. -/
def CanonicalDConv
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program) : Prop :=
  M.canonicalConvergenceDistanceClass

/-- Two concrete models witnessing non-canonicity of convergence distance. -/
def foundationModelDistance01 : Model Nat Unit Unit Nat Unit where
  observe := fun s => s
  distance := fun s₁ s₂ => if s₁ = s₂ then 0 else 1
  semilatticeCoreClass := True
  opContextLayerClass := True
  minimalOpStateEquivalenceAssumptions := True
  canonicalConvergenceDistanceClass := False
  mixingTimeControlledClass := True
  hotspotSlowModesClass := True
  driftDecayClass := True
  sequenceSubclassClass := True
  epochBarrierClass := True
  boundedMetadataApproxClass := True
  multiscaleObservablesClass := True
  metadataTradeoffFrontierClass := True
  gcCausalDominanceClass := True
  stabilizationLowerBoundClass := True

/-- Companion model with same observables and a different valid distance. -/
def foundationModelDistance02 : Model Nat Unit Unit Nat Unit where
  observe := fun s => s
  distance := fun s₁ s₂ => if s₁ = s₂ then 0 else 2
  semilatticeCoreClass := True
  opContextLayerClass := True
  minimalOpStateEquivalenceAssumptions := True
  canonicalConvergenceDistanceClass := False
  mixingTimeControlledClass := True
  hotspotSlowModesClass := True
  driftDecayClass := True
  sequenceSubclassClass := True
  epochBarrierClass := True
  boundedMetadataApproxClass := True
  multiscaleObservablesClass := True
  metadataTradeoffFrontierClass := True
  gcCausalDominanceClass := True
  stabilizationLowerBoundClass := True

/-- Formal non-canonicity witness for `d_conv` under minimal assumptions. -/
theorem dconv_noncanonicity_counterexample :
    MinimalOpStateConditions foundationModelDistance01 ∧
      MinimalOpStateConditions foundationModelDistance02 ∧
      (∀ s, foundationModelDistance01.observe s = foundationModelDistance02.observe s) ∧
      (∃ s₁ s₂, foundationModelDistance01.distance s₁ s₂ ≠ foundationModelDistance02.distance s₁ s₂) := by
  refine ⟨by simp [MinimalOpStateConditions, foundationModelDistance01], ?_⟩
  refine ⟨by simp [MinimalOpStateConditions, foundationModelDistance02], ?_⟩
  refine ⟨by intro s; rfl, ?_⟩
  refine ⟨0, 1, ?_⟩
  simp [foundationModelDistance01, foundationModelDistance02]

/-- Refutation: minimal op/state assumptions alone do not force canonical `d_conv`. -/
theorem hcrdtFoundation_refute_canonical_from_minimal :
    ¬ (∀ M : Model Nat Unit Unit Nat Unit, MinimalOpStateConditions M → CanonicalDConv M) := by
  intro hDerive
  have hMin : MinimalOpStateConditions foundationModelDistance01 := by
    simp [MinimalOpStateConditions, foundationModelDistance01]
  have hCanon : CanonicalDConv foundationModelDistance01 :=
    hDerive foundationModelDistance01 hMin
  simp [CanonicalDConv, foundationModelDistance01] at hCanon

/-- Hypothesis block matching `H_crdt_dynamics`. -/
def HcrdtDynamics
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program) : Prop :=
  M.mixingTimeControlledClass ∧ M.hotspotSlowModesClass ∧ M.driftDecayClass

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
theorem unboundedRun_not_mixingTimeControlled :
    ¬ MixingTimeControlledRun unboundedCounterexampleRun := by
  intro hMix
  rcases hMix with ⟨τ, hτ⟩
  have hEq : unboundedCounterexampleRun (τ + 1) = unboundedCounterexampleRun τ :=
    hτ (τ + 1) (Nat.le_add_right τ 1)
  have hContra : τ + 1 = τ := by
    simp [unboundedCounterexampleRun] at hEq
  exact Nat.succ_ne_self τ hContra

/-- Counterexample: the unbounded run violates hotspot boundedness. -/
theorem unboundedRun_not_hotspotBounded :
    ¬ HotspotSlowModeBoundedRun unboundedCounterexampleRun := by
  intro hBounded
  rcases hBounded with ⟨B, hB⟩
  have hLe : unboundedCounterexampleRun (B + 1) ≤ B := hB (B + 1)
  have hContra : B + 1 ≤ B := by
    simpa [unboundedCounterexampleRun] using hLe
  exact Nat.not_succ_le_self B hContra

/-- Counterexample: the unbounded run does not satisfy drift decay. -/
theorem unboundedRun_not_driftDecay :
    ¬ DriftDecayRun unboundedCounterexampleRun := by
  intro hDecay
  rcases hDecay with ⟨τ, hτ⟩
  have hLe : unboundedCounterexampleRun (τ + 1) ≤ unboundedCounterexampleRun τ :=
    hτ τ (Nat.le_refl τ)
  have hContra : τ + 1 ≤ τ := by
    simpa [unboundedCounterexampleRun] using hLe
  exact Nat.not_succ_le_self τ hContra

/-- Refutation bundle for `H_crdt_dynamics` without explicit dissemination/fairness assumptions. -/
theorem hcrdtDynamics_counterexample_traces :
    ¬ MixingTimeControlledRun unboundedCounterexampleRun ∧
      ¬ HotspotSlowModeBoundedRun unboundedCounterexampleRun ∧
      ¬ DriftDecayRun unboundedCounterexampleRun := by
  exact ⟨unboundedRun_not_mixingTimeControlled,
    unboundedRun_not_hotspotBounded, unboundedRun_not_driftDecay⟩

end CRDT
end Distributed
