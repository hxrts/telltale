/-
Copyright (c) 2025 Rumpsteak Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Effects.ProcessTyping
import Effects.Coherence
import Effects.Freshness
import Effects.Semantics

/-!
# Preservation Theorem

This module contains the preservation (subject reduction) theorem for async session effects:
if a well-typed configuration takes a step, the result is also well-typed.

The proof proceeds by case analysis on the step relation:
- Base steps (send, recv, newChan, assign) require updating all environments consistently
- Context steps (seq, par) use the induction hypothesis on the sub-step

Key lemmas used (from `Effects.Coherence`):
- `Coherent_send_preserved`: coherence is maintained after a send
- `Coherent_recv_preserved`: coherence is maintained after a recv

The main theorem is `preservation`.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

noncomputable section

/-! ## Helper: HasTypeVal Stability under G Update -/

/-- HasTypeVal is stable under G updates for non-channel values. -/
theorem HasTypeVal_updateG_nonChan {G : GEnv} {e : Endpoint} {U : SType}
    {v : Value} {T : ValType} (hv : HasTypeVal G v T) (hne : ∀ e', v = Value.chan e' → e' ≠ e) :
    HasTypeVal (updateG G e U) v T := by
  cases hv with
  | unit => exact HasTypeVal.unit
  | bool b => exact HasTypeVal.bool b
  | loc => exact HasTypeVal.loc
  | chan hlook =>
    rename_i e' S
    have hne' : e' ≠ e := hne e' rfl
    have h := lookupG_update_neq G e e' U hne'
    exact HasTypeVal.chan (by simpa [h] using hlook)

/-! ## Preservation for Send Step -/

/-- Preservation lemma specifically for the send step.

This is the key lemma showing that a send step preserves well-typedness:
- Inverts the process typing to extract T and U from `send T U`
- Uses `Coherent_send_preserved` for coherence
- Uses `BuffersTyped.enqueue` for buffer typing
- Handles store typing by case analysis on whether the variable is the channel
-/
theorem preservation_send_step
    (n : ChanId) (S : SEnv) (G : GEnv) (D : DEnv)
    (C : Config) (k x : Var) (e : Endpoint) (v : Value)
    (hWT : WTConfigN n S G D C)
    (hProc : C.proc = Process.send k x)
    (hk : lookupStr C.store k = some (Value.chan e))
    (hx : lookupStr C.store x = some v) :
    ∃ T U,
      -- Extracted from the typing derivation
      lookupStr S k = some (ValType.chan (.send T U)) ∧
      lookupStr S x = some T ∧
      lookupG G e = some (.send T U) ∧
      -- Post-configuration is well-typed under evolved environments
      WTConfigN n
        (updateStr S k (ValType.chan U))
        (updateG G e U)
        (updateD D e.dual (lookupD D e.dual ++ [T]))
        (sendStep C e v) := by
  -- Unpack the well-typed configuration
  rcases hWT with ⟨hN, hStore, hBufs, hCoh, hProcTy⟩
  subst hProc
  rcases hProcTy with ⟨n', S', G', D', hTy⟩

  -- Invert process typing: must be the send rule
  cases hTy with
  | send hkTy hxTy hGe =>
    -- Return the extracted T and U
    refine ⟨_, _, hkTy, hxTy, hGe, ?_⟩

    -- Build WTConfigN for the post-configuration
    unfold WTConfigN
    refine ⟨?_, ?_, ?_, ?_, ?_⟩

    · -- nextId unchanged
      simp only [sendStep]
      exact hN

    · -- StoreTyped under updated S and G
      -- Store is unchanged by sendStep, but S and G are updated
      intro y w Ty hy hw

      -- Store lookup is unchanged
      have hy' : lookupStr C.store y = some w := by simp only [sendStep] at hy; exact hy

      by_cases hyk : y = k
      · -- y = k: the channel variable
        subst hyk
        -- w must be Value.chan e
        have hw_eq : w = Value.chan e := by
          have := hy'.symm.trans hk
          exact Option.some_injective _ this
        subst hw_eq

        -- Ty must be ValType.chan U (from updated S lookup)
        have hTy_eq : Ty = ValType.chan U := by
          have h : lookupStr (updateStr S k (ValType.chan U)) k = some (ValType.chan U) :=
            lookupStr_update_eq S k (ValType.chan U)
          exact Option.some_injective _ (hw.symm.trans h)
        subst hTy_eq

        -- Type (chan e) at (chan U) under updated G
        exact HasTypeVal.chan (lookupG_update_eq G e U)

      · -- y ≠ k: type unchanged in S, need to lift HasTypeVal through G update
        -- Get the original type from S
        have hSy : lookupStr S y = some Ty := by
          have h := lookupStr_update_neq S k y (ValType.chan U) (Ne.symm hyk)
          simpa [h] using hw

        -- Get HasTypeVal under old G
        have hvOld : HasTypeVal G w Ty := hStore y w Ty hy' hSy

        -- Lift to updated G
        cases w with
        | unit => cases hvOld; exact HasTypeVal.unit
        | bool b => cases hvOld; exact HasTypeVal.bool b
        | loc l => cases hvOld; exact HasTypeVal.loc
        | chan e0 =>
          cases hvOld with
          | chan hlook =>
            by_cases he0 : e0 = e
            · -- e0 = e: this would mean y also holds endpoint e
              -- But k holds e, and y ≠ k, so this violates linearity
              -- In a full development with StoreNoAlias, this case is impossible
              -- For now, we use the fact that after update, e has type U
              subst he0
              -- The type Ty came from S[y], but y ≠ k, so S[y] wasn't updated
              -- This means S[y] = chan S' for some S' (the old type of e)
              -- But we're updating G[e] to U, so we need Ty = chan U
              -- This is the "aliasing" issue - for now we admit it
              sorry
            · -- e0 ≠ e: lookup unchanged
              have h := lookupG_update_neq G e e0 U (Ne.symm he0)
              exact HasTypeVal.chan (by simpa [h] using hlook)

    · -- BuffersTyped: use the enqueue lemma
      -- Get payload type from store typing
      have hvT : HasTypeVal G v _ := hStore x v _ hx hxTy

      -- Apply BuffersTyped.enqueue
      have hB := BuffersTyped.enqueue G D C.bufs e.dual v _ hBufs hvT
      simp only [sendStep]
      -- The sendStep updates bufs at e.dual with (lookupBuf C.bufs e.dual ++ [v])
      -- which matches what BuffersTyped.enqueue produces
      convert hB using 2
      · -- Show the buffer update matches
        rfl

    · -- Coherent: use Coherent_send_preserved
      exact Coherent_send_preserved G D e _ _ hCoh hGe

    · -- Process typing: skip is well-typed
      refine ⟨n, updateStr S k (ValType.chan _), updateG G e _, updateD D e.dual _, HasTypeProcN.skip⟩

/-! ## Main Preservation Theorem -/

/-- Preservation: if C is well-typed and steps to C', then C' is well-typed.
    This is the subject reduction theorem for async session effects. -/
theorem preservation
    (n : ChanId) (S : SEnv) (G : GEnv) (D : DEnv)
    (C C' : Config)
    (hWT : WTConfigN n S G D C)
    (hStep : Step C C') :
    ∃ n' S' G' D', WTConfigN n' S' G' D' C' := by
  rcases hWT with ⟨hN, hStore, hBufs, hCoh, hProc⟩

  induction hStep with
  | base hBase =>
    cases hBase with
    | seq2 =>
      -- seq skip Q → Q: environments unchanged
      rcases hProc with ⟨n', S', G', D', hTy⟩
      -- Need to invert the seq typing to extract Q's typing
      sorry

    | par_skip_left =>
      -- par skip Q → Q: similar
      sorry

    | par_skip_right =>
      -- par P skip → P: similar
      sorry

    | assign hSafe =>
      -- assign x v: update store and type environment
      rcases hProc with ⟨n', S', G', D', hTy⟩
      cases hTy with
      | assign hv =>
        refine ⟨n, updateStr S _ _, G, D, ?_⟩
        refine ⟨rfl, ?_, hBufs, hCoh, ⟨n, updateStr S _ _, G, D, HasTypeProcN.skip⟩⟩
        -- StoreTyped after update
        sorry

    | newChan =>
      -- newChan: allocate fresh channel, update all environments
      -- Use SupplyInv_newChan for freshness preservation
      sorry

    | send hk hx hq =>
      -- send: enqueue at dual endpoint
      -- Use Coherent_send_preserved
      sorry

    | recv hk hq =>
      -- recv: dequeue from own endpoint
      sorry

  | seq_left _ hP hP' ih =>
    -- Context step in seq left
    -- Apply IH and rebuild seq typing
    sorry

  | par_left _ hP hP' ih =>
    -- Context step in par left
    sorry

  | par_right _ hQ hQ' ih =>
    -- Context step in par right
    sorry

/-! ## Progress Theorem (Partial) -/

/-- A well-typed configuration either terminates or can step.
    Note: recv may be blocked waiting for a message. -/
theorem progress_weak
    (n : ChanId) (S : SEnv) (G : GEnv) (D : DEnv) (C : Config)
    (hWT : WTConfigN n S G D C) :
    Step.Terminates C ∨ (∃ C', Step C C') ∨ (∃ k x e, C.proc = Process.recv k x ∧
      lookupStr C.store k = some (Value.chan e) ∧ lookupBuf C.bufs e = []) := by
  rcases hWT with ⟨_, _, _, _, hProc⟩
  rcases hProc with ⟨_, _, _, _, hTy⟩
  sorry  -- Full proof requires case analysis on process structure

end
