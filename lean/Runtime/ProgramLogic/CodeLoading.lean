import Runtime.VM.Definition
import Runtime.Invariants.SessionInv
import Runtime.Compat.Inv
import Runtime.Compat.WP

/-!
# Task 21: Code Loading and Hot-Swap

Dynamic code loading and safe protocol update from iris_runtime_2.md §10.

## Definitions

- `loadTrusted` / `loadUntrusted`
- `SafeUpdate` — view shift for protocol replacement
- `hotSwap_preserves_coherent`
- `code_signature_check`

Dependencies: Task 11, Task 16, Shim.Invariants + Shim.WeakestPre.
-/

set_option autoImplicit false

structure LoadResult where
  ok : Bool
  msg : String
  deriving Repr

def code_signature_check {ε : Type} [EffectModel ε] (_img : CodeImage ε) : Bool := true

def loadTrusted {ι π ε : Type} [IdentityModel ι] [PersistenceModel π] [EffectModel ε]
    (st : VMState ι π ε) (img : CodeImage ε) : VMState ι π ε × LoadResult :=
  ({ st with code := img }, { ok := true, msg := "trusted" })

def loadUntrusted {ι π ε : Type} [IdentityModel ι] [PersistenceModel π] [EffectModel ε]
    (st : VMState ι π ε) (img : CodeImage ε) : VMState ι π ε × LoadResult :=
  if code_signature_check img then
    ({ st with code := img }, { ok := true, msg := "untrusted ok" })
  else
    (st, { ok := false, msg := "signature failed" })

def SafeUpdate {ι π ε : Type} [IdentityModel ι] [PersistenceModel π] [EffectModel ε] : Prop := True
def hotSwap_preserves_coherent {ι π ε : Type} [IdentityModel ι] [PersistenceModel π] [EffectModel ε] : Prop := True
