import Runtime.ProtocolMachine.Model.Program
import Runtime.Proofs.Lowering.Correctness

set_option autoImplicit false

universe u

/-! Proof-only image witnesses moved out of `Runtime.ProtocolMachine` so the protocol machine tree stays
executable/translation-oriented. -/

structure VerifiedCodeImage (γ ε : Type u) [GuardLayer γ] [EffectRuntime ε]
    [Inhabited (EffectRuntime.EffectAction ε)] where
  artifacts : Runtime.Proofs.Lowering.GeneratedArtifactSurface γ ε
  executableSurface : artifacts.supportsExecution
  artifactRefinement :
    Runtime.Proofs.Lowering.ProtocolMachineRefinesArtifacts artifacts.lowering artifacts

def VerifiedCodeImage.fromSemanticLowering {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    [Inhabited (EffectRuntime.EffectAction ε)]
    (semantic : Runtime.Proofs.Lowering.SemanticLowering)
    (hExec : semantic.ast.executable) : VerifiedCodeImage γ ε :=
  let lowering := Runtime.Proofs.Lowering.lowerSemanticToProtocolMachine semantic
  let artifacts := Runtime.Proofs.Lowering.lowerProtocolMachineToArtifacts
    (γ := γ) (ε := ε) lowering
  { artifacts := artifacts
  , executableSurface := by
      simpa [Runtime.Proofs.Lowering.GeneratedArtifactSurface.supportsExecution,
        Runtime.Proofs.Lowering.lowerSemanticToProtocolMachine] using hExec
  , artifactRefinement := by
      exact Runtime.Proofs.Lowering.lowerProtocolMachineToArtifacts_refines
        (γ := γ) (ε := ε) lowering }
