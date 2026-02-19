import Runtime.VM.API

set_option autoImplicit false

/-! # Runtime.Proofs.CompileTime.DeterminismApi

Lean-facing determinism contract API for VM runtime/profile gating.
-/

namespace Runtime
namespace Proofs

section

variable {ι γ π ε ν : Type}
variable [IdentityModel ι] [GuardLayer γ]
variable [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
variable [AuthTree ν] [AccumulatedSet ν]
variable [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
variable [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
variable [IdentityVerificationBridge ι ν]

/-! ## Profiles And Hypothesis Bundles -/

/-- Runtime determinism profiles used for policy/theorem gating. -/
inductive VMDeterminismProfile where
  | full
  | moduloEffectTrace
  | moduloCommutativity
  | replay
  deriving Repr, DecidableEq, Inhabited

/-- Reusable hypothesis bundle for determinism-oriented theorems. -/
structure VMDeterminismHypotheses
    (st₀ : VMState ι γ π ε ν) where
  fullDeterminism : Prop
  fullDeterminismProof : fullDeterminism
  moduloEffectTrace : Prop
  moduloEffectTraceProof : moduloEffectTrace
  moduloCommutativity : Prop
  moduloCommutativityProof : moduloCommutativity
  replayDeterminism : Prop
  replayDeterminismProof : replayDeterminism

/-- Artifact inventory derived from determinism hypotheses. -/
structure VMDeterminismArtifacts where
  full : Bool
  moduloEffectTrace : Bool
  moduloCommutativity : Bool
  replay : Bool

/-! ## Artifact Construction -/

private def witnessToBool {P : Prop} (_h : P) : Bool := true

/-- Build determinism artifacts from a hypothesis bundle. -/
def buildVMDeterminismArtifacts {st₀ : VMState ι γ π ε ν}
    (h : VMDeterminismHypotheses (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) st₀) :
    VMDeterminismArtifacts :=
  { full := witnessToBool h.fullDeterminismProof
  , moduloEffectTrace := witnessToBool h.moduloEffectTraceProof
  , moduloCommutativity := witnessToBool h.moduloCommutativityProof
  , replay := witnessToBool h.replayDeterminismProof
  }

/-! ## Theorem Projections -/

/-- Full determinism theorem from hypotheses. -/
theorem full_determinism_from_hypotheses {st₀ : VMState ι γ π ε ν}
    (h : VMDeterminismHypotheses (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) st₀) :
    h.fullDeterminism :=
  h.fullDeterminismProof

/-- Determinism modulo fixed effect trace from hypotheses. -/
theorem determinism_modulo_effect_trace_from_hypotheses {st₀ : VMState ι γ π ε ν}
    (h : VMDeterminismHypotheses (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) st₀) :
    h.moduloEffectTrace :=
  h.moduloEffectTraceProof

/-- Determinism modulo admissible commutativity from hypotheses. -/
theorem determinism_modulo_commutativity_from_hypotheses {st₀ : VMState ι γ π ε ν}
    (h : VMDeterminismHypotheses (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) st₀) :
    h.moduloCommutativity :=
  h.moduloCommutativityProof

/-- Replay determinism theorem from hypotheses. -/
theorem replay_determinism_from_hypotheses {st₀ : VMState ι γ π ε ν}
    (h : VMDeterminismHypotheses (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) st₀) :
    h.replayDeterminism :=
  h.replayDeterminismProof

/-! ## Runtime Inventory View -/

/-- Inventory projection for runtime capability gates. -/
def determinismInventory (artifacts : VMDeterminismArtifacts) : List (String × Bool) :=
  [ ("determinism_full", artifacts.full)
  , ("determinism_modulo_effect_trace", artifacts.moduloEffectTrace)
  , ("determinism_modulo_commutativity", artifacts.moduloCommutativity)
  , ("determinism_replay", artifacts.replay)
  ]

end

end Proofs
end Runtime
