import Protocol.Coherence.Consume
import Protocol.Coherence.EdgeCoherenceCore
import Protocol.DeadlockFreedom
import Runtime.ProtocolMachine.API
import Runtime.Invariants
import IrisExtractionInstance

/-
The Problem. The protocol machine needs a code loading interface with V1 hash checks
and a safe update predicate that preserves protocol coherence.

Solution Structure. Content ids and signatures cover the full program image
through an injective `ProgramCodec` (code, entry points, local types, handler
types and metadata). `code_image_id_injective` proves integrity: under a
collision-free hash, distinct images have distinct ids. `SafeUpdate` requires
the new local type to accept every buffered trace the old one accepts, and
`hotSwap_preserves_coherent` proves that swapping an endpoint's type under
`SafeUpdate` preserves `Coherent`.
-/


/-! # Task 21: Code Loading and Hot-Swap

Dynamic code loading and safe protocol update.

## Definitions

- `loadTrusted` / `loadUntrusted`
- `SafeUpdate` — view shift for protocol replacement
- `hotSwap_preserves_coherent` — theorem: safe hot-swap preserves coherence
- `code_image_id`, `code_signature_check`, `code_image_id_injective`

Dependencies: Task 11, Task 16, IrisExtractionInstance.
-/

set_option autoImplicit false

inductive LoadResult (ν : Type) [VerificationModel ν] where
  -- Hash-identified image load result.
  | ok (imageId : VerificationModel.Hash ν)
  | verificationFailed (reason : String)
  | resourceExhausted

/-! ## Image Content Encoding -/

/-- Canonical, injective encoding of a full program image as hashable data.
Injectivity is the stated property: the encoding must cover every field
(bytecode, entry points, local types, handler types and metadata). -/
class ProgramCodec (γ ε : Type) [GuardLayer γ] [EffectRuntime ε] where
  /-- Serialize the whole program image. -/
  encode : Program γ ε → Data
  /-- Distinct images serialize differently. -/
  encode_injective : Function.Injective encode

/-- Content id of a program image: the hash of its full canonical encoding. -/
def code_image_id {γ ε ν : Type} [GuardLayer γ] [EffectRuntime ε]
    [VerificationModel ν] [ProgramCodec γ ε] (img : Program γ ε) : VerificationModel.Hash ν :=
  VerificationModel.hash (ν:=ν) (ProgramCodec.encode img)

/-- Signed payload of an untrusted image: full program encoding plus global type. -/
def untrustedPayload {γ ε ν : Type} [GuardLayer γ] [EffectRuntime ε]
    [VerificationModel ν] [ProgramCodec γ ε] (img : UntrustedImage γ ε ν) : Data :=
  .prod (ProgramCodec.encode img.program) (.string (reprStr img.globalType))

/-- Verify the image signature against the full image content. -/
def code_signature_check {γ ε ν : Type} [GuardLayer γ] [EffectRuntime ε]
    [VerificationModel ν] [ProgramCodec γ ε] (img : UntrustedImage γ ε ν) : Bool :=
  VerificationModel.verifySignature img.signer (untrustedPayload img) img.signature

/-- Integrity: with a collision-free hash, distinct program images have
distinct content ids. -/
theorem code_image_id_injective {γ ε ν : Type} [GuardLayer γ] [EffectRuntime ε]
    [VerificationModel ν] [ProgramCodec γ ε]
    (hHash : Function.Injective (VerificationModel.hash (ν:=ν))) :
    Function.Injective (code_image_id (γ:=γ) (ε:=ε) (ν:=ν)) :=
  fun _ _ h => ProgramCodec.encode_injective (hHash h)

/-- Contrapositive form: images differing anywhere (code or metadata) get
different ids. -/
theorem code_image_id_ne {γ ε ν : Type} [GuardLayer γ] [EffectRuntime ε]
    [VerificationModel ν] [ProgramCodec γ ε]
    (hHash : Function.Injective (VerificationModel.hash (ν:=ν)))
    {p q : Program γ ε} (hpq : p ≠ q) :
    code_image_id (ν:=ν) p ≠ code_image_id (ν:=ν) q :=
  fun h => hpq (code_image_id_injective hHash h)

/-! ## Code-Image Load Paths -/

def loadTrusted {ι γ π ε ν : Type} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν] [ProgramCodec γ ε]
    (st : ProtocolMachineState ι γ π ε ν) (img : CodeImage γ ε) :
    ProtocolMachineState ι γ π ε ν × LoadResult ν :=
  -- Trusted images replace the current program directly.
  let programs' := st.programs.push img.program
  ({ st with code := img.program, programs := programs' },
    .ok (code_image_id (ν:=ν) img.program))

def loadUntrusted {ι γ π ε ν : Type} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν] [ProgramCodec γ ε]
    (st : ProtocolMachineState ι γ π ε ν) (img : UntrustedImage γ ε ν) :
    ProtocolMachineState ι γ π ε ν × LoadResult ν :=
  -- Untrusted images require signature verification.
  if code_signature_check img then
    let programs' := st.programs.push img.program
    ({ st with code := img.program, programs := programs' },
        .ok (code_image_id (ν:=ν) img.program))
  else
    (st, .verificationFailed "signature failed")

/-! ## Safe Update Contract -/

/-- Safe update of a local type: every buffered trace (from any sender) that the
current type can consume, the new type can consume too, and the new type still
reaches communication. -/
def SafeUpdate (current new_ : LocalType) : Prop :=
  (∀ r buf, (Consume r current buf).isSome → (Consume r new_ buf).isSome) ∧
  ReachesComm new_

/-- Helper: an endpoint present before an update is present after it. -/
theorem lookup_present_after_update {G : GEnv} {ep x : Endpoint} {L' Ls : LocalType}
    (h : lookupG G x = some Ls) : ∃ L, lookupG (updateG G ep L') x = some L := by
  by_cases hx : x = ep
  · subst hx; exact ⟨L', by simp⟩
  · exact ⟨Ls, by rw [lookup_g_update_g_ne hx]; exact h⟩

/-- Hot-swapping endpoint `ep` from `current` to `new_` under `SafeUpdate`
preserves coherence of the global environment with its buffers. -/
theorem hotSwap_preserves_coherent {G : GEnv} {D : DEnv} {ep : Endpoint}
    {current new_ : LocalType} (hCoh : Coherent G D)
    (hLookup : lookupG G ep = some current) (hSafe : SafeUpdate current new_) :
    Coherent (updateG G ep new_) D := by
  intro e hAct
  have hOld : EdgeCoherent G D e := hCoh e (active_edge_update_g_inv hAct (by simp [hLookup]))
  simp only [EdgeCoherent] at hOld ⊢
  intro Lrecv hGrecv
  by_cases hx : ({ sid := e.sid, role := e.receiver } : Endpoint) = ep
  · subst hx
    obtain rfl : new_ = Lrecv := Option.some.inj (by simpa using hGrecv)
    obtain ⟨Ls, hLs, hC⟩ := hOld current hLookup
    obtain ⟨L, hL⟩ := lookup_present_after_update (L' := new_) hLs
    exact ⟨L, hL, hSafe.1 _ _ hC⟩
  · rw [lookup_g_update_g_ne hx] at hGrecv
    obtain ⟨Ls, hLs, hC⟩ := hOld Lrecv hGrecv
    obtain ⟨L, hL⟩ := lookup_present_after_update (ep := ep) (L' := new_) hLs
    exact ⟨L, hL, hC⟩
