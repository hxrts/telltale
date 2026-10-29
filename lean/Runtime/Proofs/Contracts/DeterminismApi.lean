import Runtime.ProtocolMachine.API

set_option autoImplicit false

/-! # Runtime.Proofs.Contracts.DeterminismApi

Lean-facing determinism contract API for protocol machine runtime/profile gating.
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
inductive ProtocolMachineDeterminismProfile where
  | full
  | moduloEffectTrace
  | moduloCommutativity
  | replay
  deriving Repr, DecidableEq, Inhabited

/-- Reusable hypothesis bundle for determinism-oriented theorems. -/
structure ProtocolMachineDeterminismHypotheses
    (st₀ : ProtocolMachineState ι γ π ε ν) where
  fullDeterminism : Prop
  fullDeterminismProof : fullDeterminism
  moduloEffectTrace : Prop
  moduloEffectTraceProof : moduloEffectTrace
  moduloCommutativity : Prop
  moduloCommutativityProof : moduloCommutativity
  replayDeterminism : Prop
  replayDeterminismProof : replayDeterminism

/-- A determinism statement packaged with its proof. Artifacts carry this
evidence instead of an erased `Bool`, so a consumer can always recover the
proposition that was established. -/
structure DeterminismEvidence where
  statement : Prop
  proof : statement

/-- Artifact inventory derived from determinism hypotheses. Each profile is
`some evidence` only when a proof of that profile's statement was supplied. -/
structure ProtocolMachineDeterminismArtifacts where
  full : Option DeterminismEvidence
  moduloEffectTrace : Option DeterminismEvidence
  moduloCommutativity : Option DeterminismEvidence
  replay : Option DeterminismEvidence

/-! ## Artifact Construction -/

/-- Build determinism artifacts from a hypothesis bundle, keeping each
statement together with its proof. -/
def buildProtocolMachineDeterminismArtifacts {st₀ : ProtocolMachineState ι γ π ε ν}
    (h : ProtocolMachineDeterminismHypotheses (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) st₀) :
    ProtocolMachineDeterminismArtifacts :=
  { full := some ⟨h.fullDeterminism, h.fullDeterminismProof⟩
  , moduloEffectTrace := some ⟨h.moduloEffectTrace, h.moduloEffectTraceProof⟩
  , moduloCommutativity := some ⟨h.moduloCommutativity, h.moduloCommutativityProof⟩
  , replay := some ⟨h.replayDeterminism, h.replayDeterminismProof⟩
  }

/-- The `full` artifact built from hypotheses carries exactly the bundle's
full-determinism statement. -/
theorem buildProtocolMachineDeterminismArtifacts_full {st₀ : ProtocolMachineState ι γ π ε ν}
    (h : ProtocolMachineDeterminismHypotheses (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) st₀) :
    ((buildProtocolMachineDeterminismArtifacts h).full.map (·.statement)) =
      some h.fullDeterminism :=
  rfl

/-- Any evidence present in an artifact proves its recorded statement. -/
theorem DeterminismEvidence.sound {e? : Option DeterminismEvidence}
    {e : DeterminismEvidence} (hSome : e? = some e) : e.statement := by
  subst hSome
  exact e.proof

/-! ## Theorem Projections -/

/-- Full determinism theorem from hypotheses. -/
theorem full_determinism_from_hypotheses {st₀ : ProtocolMachineState ι γ π ε ν}
    (h : ProtocolMachineDeterminismHypotheses (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) st₀) :
    h.fullDeterminism :=
  h.fullDeterminismProof

/-- Determinism modulo fixed effect trace from hypotheses. -/
theorem determinism_modulo_effect_trace_from_hypotheses {st₀ : ProtocolMachineState ι γ π ε ν}
    (h : ProtocolMachineDeterminismHypotheses (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) st₀) :
    h.moduloEffectTrace :=
  h.moduloEffectTraceProof

/-- Determinism modulo admissible commutativity from hypotheses. -/
theorem determinism_modulo_commutativity_from_hypotheses {st₀ : ProtocolMachineState ι γ π ε ν}
    (h : ProtocolMachineDeterminismHypotheses (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) st₀) :
    h.moduloCommutativity :=
  h.moduloCommutativityProof

/-- Replay determinism theorem from hypotheses. -/
theorem replay_determinism_from_hypotheses {st₀ : ProtocolMachineState ι γ π ε ν}
    (h : ProtocolMachineDeterminismHypotheses (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) st₀) :
    h.replayDeterminism :=
  h.replayDeterminismProof

/-! ## Runtime Inventory View -/

/-- Inventory projection for runtime capability gates: a flag is `true` iff
proof evidence for that profile is present. -/
def determinismInventory (artifacts : ProtocolMachineDeterminismArtifacts) : List (String × Bool) :=
  [ ("determinism_full", artifacts.full.isSome)
  , ("determinism_modulo_effect_trace", artifacts.moduloEffectTrace.isSome)
  , ("determinism_modulo_commutativity", artifacts.moduloCommutativity.isSome)
  , ("determinism_replay", artifacts.replay.isSome)
  ]

end

end Proofs
end Runtime
