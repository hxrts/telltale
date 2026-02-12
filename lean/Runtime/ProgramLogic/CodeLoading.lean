import Protocol.Coherence.Consume
import Protocol.DeadlockFreedom
import Runtime.VM.API
import Runtime.Invariants.SessionInv
import IrisExtractionInstance

/-
The Problem. The VM needs a code loading interface with V1 hash checks
and a safe update predicate that preserves protocol coherence.

Solution Structure. Provide hash-based load helpers and a `SafeUpdate`
predicate aligned with runtime.md §10, leaving proofs as stubs.
-/


/-! # Task 21: Code Loading and Hot-Swap

Dynamic code loading and safe protocol update from iris_runtime_2.md §10.

## Definitions

- `loadTrusted` / `loadUntrusted`
- `SafeUpdate` — view shift for protocol replacement
- `hotSwap_preserves_coherent`
- `code_signature_check`

Dependencies: Task 11, Task 16, Shim.Invariants + Shim.WeakestPre.
-/

set_option autoImplicit false

inductive LoadResult (ν : Type) [VerificationModel ν] where
  -- Hash-identified image load result.
  | ok (imageId : VerificationModel.Hash ν)
  | verificationFailed (reason : String)
  | resourceExhausted

def code_image_id {γ ε ν : Type} [GuardLayer γ] [EffectRuntime ε]
    [VerificationModel ν] (img : Program γ ε) : VerificationModel.Hash ν :=
  -- V1 content id uses a transparent hash of program metadata.
  VerificationModel.hash (ν:=ν) (.string img.metadata.name)

def code_signature_check {γ ε ν : Type} [GuardLayer γ] [EffectRuntime ε]
    [VerificationModel ν] (img : UntrustedImage γ ε ν) : Bool :=
  -- Verify the image signature against its content id.
  let payload : Data := .string img.program.metadata.name
  VerificationModel.verifySignature img.signer payload img.signature

/-! ## Code-Image Load Paths -/

def loadTrusted {ι γ π ε ν : Type} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (img : CodeImage γ ε) :
    VMState ι γ π ε ν × LoadResult ν :=
  -- Trusted images replace the current program directly.
  let programs' := st.programs.push img.program
  ({ st with code := img.program, programs := programs' },
    -- V1 hashes the program metadata only.
    .ok (code_image_id (ν:=ν) img.program))

def loadUntrusted {ι γ π ε ν : Type} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (img : UntrustedImage γ ε ν) :
    VMState ι γ π ε ν × LoadResult ν :=
  -- Untrusted images require signature verification.
  if code_signature_check img then
    let programs' := st.programs.push img.program
    ({ st with code := img.program, programs := programs' },
      -- V1 hashes the program metadata only.
      .ok (code_image_id (ν:=ν) img.program))
  else
    (st, .verificationFailed "signature failed")

/-! ## Safe Update Contract -/

def SafeUpdate {ι γ π ε ν : Type} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (current new_ : LocalType) (buffered : List ValType) : Prop :=
  -- V1 safe update: buffered traces agree and new type is communicative.
  (∀ r, Consume r current buffered = Consume r new_ buffered) ∧
  ReachesComm new_

def hotSwap_preserves_coherent {ι γ π ε ν : Type} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (_current _new : LocalType) (_buffered : List ValType) : Prop :=
  -- V1: hot-swap preserves coherence exactly when SafeUpdate holds.
  SafeUpdate (ι:=ι) (γ:=γ) (π:=π) (ε:=ε) (ν:=ν) _current _new _buffered
