/-
Copyright (c) 2025 Rumpsteak Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Effects.Process
import Effects.Typing
import Effects.Split

/-!
# Process Typing

This module defines the typing judgment for processes with an explicit name supply:
`HasTypeProcN n S G D P n' S' G' D'`

The name supply n tracks the next available channel ID, ensuring freshness
for channel allocation. The judgment transforms typing environments:
- n → n': name supply may increase (by newChan)
- S → S': variable types evolve (by assign, send, recv)
- G → G': session types evolve (by send, recv, newChan)
- D → D': in-flight type traces evolve (by send, recv, newChan)
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

noncomputable section

/-- Process typing with an explicit name supply.
    `HasTypeProcN n S G D P n' S' G' D'` means:
    - Under initial environments (n, S, G, D), process P is well-typed
    - After P completes, environments become (n', S', G', D')
-/
inductive HasTypeProcN :
    ChanId → SEnv → GEnv → DEnv → Process →
    ChanId → SEnv → GEnv → DEnv → Prop where

  /-- Skip is well-typed and leaves environments unchanged. -/
  | skip {n S G D} :
      HasTypeProcN n S G D Process.skip n S G D

  /-- Sequential composition: type P, then Q with P's output environments. -/
  | seq {n S G D P Q n₁ S₁ G₁ D₁ n₂ S₂ G₂ D₂} :
      HasTypeProcN n S G D P n₁ S₁ G₁ D₁ →
      HasTypeProcN n₁ S₁ G₁ D₁ Q n₂ S₂ G₂ D₂ →
      HasTypeProcN n S G D (Process.seq P Q) n₂ S₂ G₂ D₂

  /-- Parallel composition: split S linearly, type both branches. -/
  | par {n S G D P Q S₁ S₂ n₁ n₂} :
      SplitSEnv S S₁ S₂ →
      HasTypeProcN n S₁ G D P n₁ S₁ G D →
      HasTypeProcN n S₂ G D Q n₂ S₂ G D →
      HasTypeProcN n S G D (Process.par P Q) (max n₁ n₂) S G D

  /-- Assignment: update the type environment with the assigned value's type. -/
  | assign {n S G D x v T} :
      HasTypeVal G v T →
      HasTypeProcN n S G D (Process.assign x v) n (updateStr S x T) G D

  /-- Channel creation: allocate fresh endpoints and update all environments. -/
  | newChan {n S G D kL kR T} :
      HasTypeProcN n S G D (Process.newChan kL kR T)
        (n + 1)
        (updateStr (updateStr S kL (ValType.chan T)) kR (ValType.chan T.dual))
        (updateG (updateG G (n, Polarity.L) T) (n, Polarity.R) T.dual)
        (updateD (updateD D (n, Polarity.L) []) (n, Polarity.R) [])

  /-- Send: advance session type from send T U to U, append T to dual's trace. -/
  | send {n S G D k x T U e} :
      lookupStr S k = some (ValType.chan (.send T U)) →
      lookupStr S x = some T →
      lookupG G e = some (.send T U) →
      HasTypeProcN n S G D (Process.send k x)
        n
        (updateStr S k (ValType.chan U))
        (updateG G e U)
        (updateD D e.dual (lookupD D e.dual ++ [T]))

  /-- Receive: advance session type from recv T U to U, pop T from own trace. -/
  | recv {n S G D k x T U e ts} :
      lookupStr S k = some (ValType.chan (.recv T U)) →
      lookupG G e = some (.recv T U) →
      lookupD D e = T :: ts →
      HasTypeProcN n S G D (Process.recv k x)
        n
        (updateStr (updateStr S k (ValType.chan U)) x T)
        (updateG G e U)
        (updateD D e ts)

namespace HasTypeProcN

/-- Skip preserves environments exactly. -/
theorem skip_inv {n n' S S' G G' D D'} (h : HasTypeProcN n S G D Process.skip n' S' G' D') :
    n = n' ∧ S = S' ∧ G = G' ∧ D = D' := by
  cases h
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Name supply is monotonic: it never decreases. -/
theorem name_mono {n S G D P n' S' G' D'} (h : HasTypeProcN n S G D P n' S' G' D') :
    n ≤ n' := by
  induction h with
  | skip => exact Nat.le_refl _
  | seq _ _ ih1 ih2 => exact Nat.le_trans ih1 ih2
  | par _ _ _ ih1 ih2 => exact Nat.le_max_of_le_left ih1
  | assign _ => exact Nat.le_refl _
  | newChan => exact Nat.le_succ _
  | send _ _ _ => exact Nat.le_refl _
  | recv _ _ _ => exact Nat.le_refl _

end HasTypeProcN

/-- Well-typed configuration: combines all invariants.
- Name supply matches configuration's nextId
- Store is well-typed
- Buffers are well-typed against their traces
- Coherence holds
- Process is well-typed
-/
def WTConfigN (n : ChanId) (S : SEnv) (G : GEnv) (D : DEnv) (C : Config) : Prop :=
  C.nextId = n ∧
  StoreTyped S G C.store ∧
  BuffersTyped G D C.bufs ∧
  Coherent G D ∧
  ∃ n' S' G' D', HasTypeProcN n S G D C.proc n' S' G' D'

namespace WTConfigN

/-- A well-typed configuration has a well-typed process. -/
theorem has_proc_typing {n S G D C} (h : WTConfigN n S G D C) :
    ∃ n' S' G' D', HasTypeProcN n S G D C.proc n' S' G' D' :=
  h.2.2.2.2

/-- The nextId matches the name supply. -/
theorem nextId_eq {n S G D C} (h : WTConfigN n S G D C) : C.nextId = n :=
  h.1

/-- The store is well-typed. -/
theorem store_typed {n S G D C} (h : WTConfigN n S G D C) : StoreTyped S G C.store :=
  h.2.1

/-- The buffers are well-typed. -/
theorem buffers_typed {n S G D C} (h : WTConfigN n S G D C) : BuffersTyped G D C.bufs :=
  h.2.2.1

/-- Coherence holds. -/
theorem coherent {n S G D C} (h : WTConfigN n S G D C) : Coherent G D :=
  h.2.2.2.1

end WTConfigN

end
