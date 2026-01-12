/-
Copyright (c) 2025 Rumpsteak Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Effects.Typing
import Effects.Environments

/-!
# Coherence Preservation Lemmas

This module contains the key preservation lemmas for the coherence invariant:
- `Coherent_send_preserved`: coherence is maintained after a send operation
- `Coherent_recv_preserved`: coherence is maintained after a receive operation

These are the core "session-type" lemmas that make async communication type-safe.
The proofs use the Consume function to track how session types evolve as messages
are sent (appended to dual's trace) and received (popped from own trace).
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

noncomputable section

/-! ## Helper Lemmas -/

/-- Dual endpoint is not equal to itself. -/
theorem Endpoint.dual_ne (e : Endpoint) : e.dual ≠ e := by
  cases e with
  | mk n p =>
    cases p <;> simp [Endpoint.dual, Polarity.dual]

/-- An endpoint is not equal to its dual. -/
theorem Endpoint.ne_dual (e : Endpoint) : e ≠ e.dual := by
  intro h
  exact Endpoint.dual_ne e h.symm

/-! ## Coherence Preservation for Send -/

/-- Coherence is preserved by a send step.

When endpoint e sends type T (advancing from `send T U` to `U`),
we update:
- G at e: from `send T U` to `U`
- D at e.dual: append T to the in-flight trace

The proof proceeds by case analysis on which endpoint we're checking coherence for:
1. a = e (the sender): queue is empty, dual's queue gets T appended
2. a = e.dual (the receiver's endpoint): symmetric reasoning
3. a unrelated to e: environments unchanged at a and a.dual
-/
theorem Coherent_send_preserved
    (G : GEnv) (D : DEnv) (e : Endpoint) (T : ValType) (U : SType)
    (hC : Coherent G D)
    (hGe : lookupG G e = some (.send T U)) :
    Coherent (updateG G e U) (updateD D e.dual (lookupD D e.dual ++ [T])) := by
  intro a Sa hGa
  let a' := a.dual

  -- Case split on whether a is e, e.dual, or unrelated
  by_cases hae : a = e
  · -- Case: a = e (the sender endpoint)
    subst hae

    -- Sa must be U (the updated type at e)
    have hSaU : Sa = U := by
      have h : lookupG (updateG G e U) e = some U := lookupG_update_eq G e U
      simp only [h] at hGa
      exact Option.some_injective _ hGa

    subst hSaU

    -- Use old coherence at e with send T U
    have hOld := hC e (.send T U) hGe
    rcases hOld with ⟨Sdual, q, qdual, hGdual, hq, hqdual, hmatch⟩

    -- Extract that Consume produces some values (from the match)
    have hConsumes : ∃ S1 S2,
        Consume (.send T U) q = some S1 ∧
        Consume Sdual qdual = some S2 ∧
        S1 = S2.dual := by
      cases hC1 : Consume (.send T U) q <;>
      cases hC2 : Consume Sdual qdual <;>
      simp only [hC1, hC2] at hmatch
      · exact ⟨_, _, hC1, hC2, hmatch⟩

    rcases hConsumes with ⟨S1, S2, hCsend, hCdual, hEq⟩

    -- Consume (send T U) q forces q = [] and S1 = send T U
    have hqnil := Consume.send_some hCsend
    have qnil : q = [] := hqnil.1
    subst qnil

    -- S1 = send T U, so hEq gives send T U = dual S2
    have hS2 : S2 = (.send T U).dual := by
      have h1 : .send T U = S2.dual := by simpa [hqnil.2] using hEq
      calc S2 = S2.dual.dual := (SType.dual_dual S2).symm
           _ = (.send T U).dual := by rw [← h1]

    -- Therefore Consume Sdual qdual = some (recv T (dual U))
    have hCdual' : Consume Sdual qdual = some (.recv T U.dual) := by
      simp only [SType.dual] at hS2
      simpa [hS2] using hCdual

    -- Appending T to qdual consumes that T and yields dual U
    have hCdualApp : Consume Sdual (qdual ++ [T]) = some U.dual :=
      Consume.append_recv Sdual qdual T U.dual hCdual'

    -- Consume U [] = some U
    have hCU : Consume U [] = some U := Consume.nil U

    -- Build the coherence witness for e in the new environments
    refine ⟨Sdual, [], qdual ++ [T], ?_, ?_, ?_, ?_⟩

    · -- Dual endpoint type unchanged in G' (only e was updated)
      have hne : e.dual ≠ e := Endpoint.dual_ne e
      have h := lookupG_update_neq G e e.dual U hne
      simpa [h] using hGdual

    · -- q = lookupD D' e = [] (D only changed at e.dual, not at e)
      have hne : e ≠ e.dual := Endpoint.ne_dual e
      have h := lookupD_update_neq D e.dual e (lookupD D e.dual ++ [T]) hne
      simpa [h, hq]

    · -- q' = lookupD D' e.dual = qdual ++ [T]
      simp only [lookupD_update_eq, hqdual]

    · -- Match: Consume U [] and Consume Sdual (qdual ++ [T]) are dual
      simp only [hCU, hCdualApp, SType.dual_dual]

  · by_cases had : a = e.dual
    · -- Case: a = e.dual (the receiver's endpoint)
      subst had

      have hne : e.dual ≠ e := Endpoint.dual_ne e

      -- lookupG' at a = e.dual is unchanged (since e.dual ≠ e)
      have hGa0 : lookupG (updateG G e U) e.dual = lookupG G e.dual :=
        lookupG_update_neq G e e.dual U hne

      -- Get Sa from old G
      have hGa_old : lookupG G e.dual = some Sa := by simpa [hGa0] using hGa

      -- Use old coherence at e.dual
      have hOld := hC e.dual Sa hGa_old
      rcases hOld with ⟨Sdual, q, qdual, hGdual, hq, hqdual, hmatch⟩

      -- The dual of e.dual is e, so hGdual says lookupG G e = some Sdual
      -- But we know lookupG G e = some (send T U), so Sdual = send T U
      have hSdual : Sdual = .send T U := by
        have h1 : lookupG G e = some (.send T U) := hGe
        have h2 : lookupG G e = some Sdual := by
          simp only [Endpoint.dual_dual] at hGdual
          exact hGdual
        exact Option.some_injective _ (h2.symm.trans h1)

      subst hSdual

      -- Extract Consume results from match
      have hConsumes : ∃ S1 S2,
          Consume (.send T U) qdual = some S1 ∧
          Consume Sa q = some S2 ∧
          S1 = S2.dual := by
        cases hC1 : Consume Sa q <;>
        cases hC2 : Consume (.send T U) qdual <;>
        simp only [hC1, hC2] at hmatch
        · refine ⟨_, _, hC2, hC1, ?_⟩
          -- hmatch says S2 = S1.dual, we need S1 = S2.dual
          have := hmatch.symm
          rw [SType.dual_dual] at this
          exact this

      rcases hConsumes with ⟨S1, S2, hCsend, hCsa, hEq⟩

      -- Consume (send T U) qdual forces qdual = []
      have hqdualNil := Consume.send_some hCsend
      have qdNil : qdual = [] := hqdualNil.1
      subst qdNil

      -- S2 = recv T (dual U) after applying duality
      have hS2 : S2 = (.send T U).dual := by
        have h1 : .send T U = S2.dual := by simpa [hqdualNil.2] using hEq
        calc S2 = S2.dual.dual := (SType.dual_dual S2).symm
             _ = (.send T U).dual := by rw [← h1]

      -- Consume Sa q = some (recv T (dual U))
      have hCsa' : Consume Sa q = some (.recv T U.dual) := by
        simp only [SType.dual] at hS2
        simpa [hS2] using hCsa

      -- Therefore Consume Sa (q ++ [T]) = some (dual U)
      have hCsaApp : Consume Sa (q ++ [T]) = some U.dual :=
        Consume.append_recv Sa q T U.dual hCsa'

      -- Build witness: dual endpoint (which is e) now has type U
      refine ⟨U, q ++ [T], [], ?_, ?_, ?_, ?_⟩

      · -- lookupG' e = some U
        exact lookupG_update_eq G e U

      · -- q = lookupD D' (e.dual) = lookupD D (e.dual) ++ [T]
        simp only [lookupD_update_eq, hq]

      · -- q' = lookupD D' e = lookupD D e = [] (unchanged, since D update was at e.dual)
        have hne' : e ≠ e.dual := Endpoint.ne_dual e
        have h := lookupD_update_neq D e.dual e (lookupD D e.dual ++ [T]) hne'
        simp only [Endpoint.dual_dual]
        simpa [h, hqdual]

      · -- Match: Consume Sa (q++[T]) and Consume U []
        have hCU : Consume U [] = some U := Consume.nil U
        simp only [hCsaApp, hCU, SType.dual_dual]

    · -- Case: a is unrelated (neither e nor e.dual)
      -- Both G and D are unchanged at a and a.dual

      have hGa_old : lookupG G a = some Sa := by
        have h := lookupG_update_neq G e a U hae
        simpa [h] using hGa

      have hOld := hC a Sa hGa_old
      rcases hOld with ⟨Sdual, q, qdual, hGdual, hq, hqdual, hmatch⟩

      -- Show the same witness works in updated envs
      refine ⟨Sdual, q, qdual, ?_, ?_, ?_, ?_⟩

      · -- Type of dual endpoint unchanged
        have hne1 : a.dual ≠ e := by
          intro hcontra
          -- If a.dual = e then a = e.dual, contradicting had
          have : a = e.dual := by
            calc a = a.dual.dual := (Endpoint.dual_dual a).symm
                 _ = e.dual := by rw [hcontra]
          exact had this
        have h := lookupG_update_neq G e a.dual U hne1
        simpa [h] using hGdual

      · -- q unchanged (D update only at e.dual)
        have hne2 : a ≠ e.dual := had
        have h := lookupD_update_neq D e.dual a (lookupD D e.dual ++ [T]) (Ne.symm hne2)
        simpa [h, hq]

      · -- qdual unchanged
        have hne3 : a.dual ≠ e.dual := by
          intro hcontra
          -- If a.dual = e.dual then a = e, contradicting hae
          have : a = e := by
            calc a = a.dual.dual := (Endpoint.dual_dual a).symm
                 _ = e.dual.dual := by rw [hcontra]
                 _ = e := Endpoint.dual_dual e
          exact hae this
        have h := lookupD_update_neq D e.dual a.dual (lookupD D e.dual ++ [T]) (Ne.symm hne3)
        simpa [h, hqdual]

      · -- Match unchanged
        exact hmatch

/-! ## Coherence Preservation for Recv -/

/-- Coherence is preserved by a recv step.

When endpoint e receives type T (advancing from `recv T U` to `U`),
we update:
- G at e: from `recv T U` to `U`
- D at e: pop T from the front of the in-flight trace

This is the dual of the send case.
-/
theorem Coherent_recv_preserved
    (G : GEnv) (D : DEnv) (e : Endpoint) (T : ValType) (U : SType) (ts : List ValType)
    (hC : Coherent G D)
    (hGe : lookupG G e = some (.recv T U))
    (hDe : lookupD D e = T :: ts) :
    Coherent (updateG G e U) (updateD D e ts) := by
  intro a Sa hGa
  let a' := a.dual

  by_cases hae : a = e
  · -- Case: a = e (the receiver endpoint)
    subst hae

    -- Sa must be U
    have hSaU : Sa = U := by
      have h : lookupG (updateG G e U) e = some U := lookupG_update_eq G e U
      exact Option.some_injective _ (h.symm.trans hGa)
    subst hSaU

    -- Use old coherence at e
    have hOld := hC e (.recv T U) hGe
    rcases hOld with ⟨Sdual, q, qdual, hGdual, hq, hqdual, hmatch⟩

    -- q = T :: ts by hDe and hq
    have hqTs : q = T :: ts := by rw [hq, hDe]

    -- From hmatch, Consume (recv T U) (T :: ts) must succeed
    have hConsumes : ∃ S1 S2,
        Consume (.recv T U) q = some S1 ∧
        Consume Sdual qdual = some S2 ∧
        S1 = S2.dual := by
      cases hC1 : Consume (.recv T U) q <;>
      cases hC2 : Consume Sdual qdual <;>
      simp only [hC1, hC2] at hmatch
      · exact ⟨_, _, hC1, hC2, hmatch⟩

    rcases hConsumes with ⟨S1, S2, hCrecv, hCdual, hEq⟩

    -- Consume (recv T U) (T :: ts) = Consume U ts
    have hCrecv' : Consume U ts = some S1 := by
      rw [hqTs] at hCrecv
      simp only [Consume.recv_match] at hCrecv
      exact hCrecv

    -- Build witness with updated trace
    refine ⟨Sdual, ts, qdual, ?_, ?_, ?_, ?_⟩

    · -- Dual type unchanged
      have hne : e.dual ≠ e := Endpoint.dual_ne e
      have h := lookupG_update_neq G e e.dual U hne
      simpa [h] using hGdual

    · -- q = lookupD D' e = ts
      simp only [lookupD_update_eq]

    · -- qdual unchanged
      have hne : e.dual ≠ e := Endpoint.dual_ne e
      have h := lookupD_update_neq D e e.dual ts hne
      simpa [h, hqdual]

    · -- Match holds with same S1, S2
      simp only [hCrecv', hCdual, hEq]

  · by_cases had : a = e.dual
    · -- Case: a = e.dual
      subst had

      have hne : e.dual ≠ e := Endpoint.dual_ne e

      have hGa_old : lookupG G e.dual = some Sa := by
        have h := lookupG_update_neq G e e.dual U hne
        simpa [h] using hGa

      have hOld := hC e.dual Sa hGa_old
      rcases hOld with ⟨Sdual, q, qdual, hGdual, hq, hqdual, hmatch⟩

      -- The dual is e, so Sdual = recv T U
      have hSdual : Sdual = .recv T U := by
        simp only [Endpoint.dual_dual] at hGdual
        exact Option.some_injective _ (hGdual.symm.trans hGe)
      subst hSdual

      -- qdual = T :: ts
      have hqdualTs : qdual = T :: ts := by
        simp only [Endpoint.dual_dual] at hqdual
        rw [hqdual, hDe]

      -- Build witness
      refine ⟨U, q, ts, ?_, ?_, ?_, ?_⟩

      · -- lookupG' e = some U
        simp only [Endpoint.dual_dual]
        exact lookupG_update_eq G e U

      · -- q unchanged (D update at e, not e.dual)
        have hne' : e.dual ≠ e := Endpoint.dual_ne e
        have h := lookupD_update_neq D e e.dual ts hne'
        simpa [h, hq]

      · -- lookupD D' e = ts
        simp only [Endpoint.dual_dual, lookupD_update_eq]

      · -- Match: need Consume Sa q and Consume U ts to be dual
        have hConsumes : ∃ S1 S2,
            Consume (.recv T U) qdual = some S1 ∧
            Consume Sa q = some S2 ∧
            S1 = S2.dual := by
          cases hC1 : Consume Sa q <;>
          cases hC2 : Consume (.recv T U) qdual <;>
          simp only [hC1, hC2] at hmatch
          · refine ⟨_, _, hC2, hC1, ?_⟩
            rw [SType.dual_dual]
            exact hmatch.symm

        rcases hConsumes with ⟨S1, S2, hCrecv, hCsa, hEqOld⟩

        -- Consume (recv T U) (T :: ts) = Consume U ts
        have hCU : Consume U ts = some S1 := by
          rw [hqdualTs] at hCrecv
          simp only [Consume.recv_match] at hCrecv
          exact hCrecv

        simp only [hCsa, hCU, hEqOld]

    · -- Case: a unrelated
      have hGa_old : lookupG G a = some Sa := by
        have h := lookupG_update_neq G e a U hae
        simpa [h] using hGa

      have hOld := hC a Sa hGa_old
      rcases hOld with ⟨Sdual, q, qdual, hGdual, hq, hqdual, hmatch⟩

      refine ⟨Sdual, q, qdual, ?_, ?_, ?_, ?_⟩

      · have hne1 : a.dual ≠ e := by
          intro hcontra
          have : a = e.dual := by
            calc a = a.dual.dual := (Endpoint.dual_dual a).symm
                 _ = e.dual := by rw [hcontra]
          exact had this
        have h := lookupG_update_neq G e a.dual U hne1
        simpa [h] using hGdual

      · have hne2 : a ≠ e := hae
        have h := lookupD_update_neq D e a ts hne2
        simpa [h, hq]

      · have hne3 : a.dual ≠ e := by
          intro hcontra
          have : a = e.dual := by
            calc a = a.dual.dual := (Endpoint.dual_dual a).symm
                 _ = e.dual := by rw [hcontra]
          exact had this
        have h := lookupD_update_neq D e a.dual ts hne3
        simpa [h, hqdual]

      · exact hmatch

end
