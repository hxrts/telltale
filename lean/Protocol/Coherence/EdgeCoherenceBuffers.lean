import Protocol.Coherence.EdgeCoherenceCore

/-! # Protocol.Coherence.EdgeCoherenceBuffers

Buffer typing and value-typing lemmas layered on top of edge coherence.
-/

/-
The Problem. Coherence-preservation proofs also need typed-buffer invariants,
including head typing and lookup/inversion lemmas for runtime values.

Solution Structure.
1. Define `BufferTyped`/`BuffersTyped`.
2. Provide `HasTypeVal` inversion/uniqueness transport lemmas.
3. Relate typed buffer heads to trace heads.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section
/-! ## Buffer Typing -/

/-- A value has a given type under GEnv. -/
inductive HasTypeVal (G : GEnv) : Value → ValType → Prop where
  | unit : HasTypeVal G .unit .unit
  | bool (b : Bool) : HasTypeVal G (.bool b) .bool
  | nat (n : Nat) : HasTypeVal G (.nat n) .nat
  | string (s : String) : HasTypeVal G (.string s) .string
  | prod {v₁ v₂ T₁ T₂} :
      HasTypeVal G v₁ T₁ →
      HasTypeVal G v₂ T₂ →
      HasTypeVal G (.prod v₁ v₂) (.prod T₁ T₂)
  | chan {e L} :
      lookupG G e = some L →
      HasTypeVal G (.chan e) (.chan e.sid e.role)

/-! ### Value Type Inversion Lemmas

These lemmas extract concrete value forms from typing judgments.
Reference: `work/effects/008.lean:313-324, 521-524` -/

/-- If a value has channel type, it must be a channel value with matching endpoint.
    Reference: `work/effects/008.lean:313-318` -/
theorem HasTypeVal_chan_inv {G : GEnv} {v : Value} {sid : SessionId} {role : Role}
    (h : HasTypeVal G v (.chan sid role)) :
    v = .chan ⟨sid, role⟩ := by
  cases h with
  | chan hLookup => rfl

/-- If a value has string type, it must be a string value.
    Reference: `work/effects/008.lean:521-524` -/
theorem HasTypeVal_string_inv {G : GEnv} {v : Value}
    (h : HasTypeVal G v .string) :
    ∃ s, v = .string s := by
  cases h with
  | string s => exact ⟨s, rfl⟩

/-- If a value has bool type, it must be a bool value. -/
theorem HasTypeVal_bool_inv {G : GEnv} {v : Value}
    (h : HasTypeVal G v .bool) :
    ∃ b, v = .bool b := by
  cases h with
  | bool b => exact ⟨b, rfl⟩

/-- If a value has nat type, it must be a nat value. -/
theorem HasTypeVal_nat_inv {G : GEnv} {v : Value}
    (h : HasTypeVal G v .nat) :
    ∃ n, v = .nat n := by
  cases h with
  | nat n => exact ⟨n, rfl⟩

/-- If a value has unit type, it must be unit. -/
theorem HasTypeVal_unit_inv {G : GEnv} {v : Value}
    (h : HasTypeVal G v .unit) :
    v = .unit := by
  cases h; rfl

/-- If a value has product type, it must be a product value. -/
theorem HasTypeVal_prod_inv {G : GEnv} {v : Value} {T₁ T₂ : ValType}
    (h : HasTypeVal G v (.prod T₁ T₂)) :
    ∃ v₁ v₂, v = .prod v₁ v₂ ∧ HasTypeVal G v₁ T₁ ∧ HasTypeVal G v₂ T₂ := by
  cases h with
  | prod h1 h2 => exact ⟨_, _, rfl, h1, h2⟩

/-- HasTypeVal is deterministic: each value has exactly one type.
    This is essential for deriving trace types from buffer values. -/
theorem HasTypeVal_unique {G : GEnv} {v : Value} {T₁ T₂ : ValType}
    (h₁ : HasTypeVal G v T₁) (h₂ : HasTypeVal G v T₂) : T₁ = T₂ := by
  induction h₁ generalizing T₂ with
  | unit => cases h₂; rfl
  | bool => cases h₂; rfl
  | nat => cases h₂; rfl
  | string => cases h₂; rfl
  | prod _ _ ih₁ ih₂ =>
    cases h₂ with
    | prod h₂a h₂b => congr 1 <;> [exact ih₁ h₂a; exact ih₂ h₂b]
  | chan _ => cases h₂; rfl

/-- HasTypeVal is preserved when extending GEnv if channel endpoints are preserved. -/
theorem HasTypeVal_mono (G G' : GEnv) (v : Value) (T : ValType)
    (hHas : HasTypeVal G v T)
    (hMono : ∀ e L, lookupG G e = some L → lookupG G' e = some L) :
    HasTypeVal G' v T := by
  induction hHas generalizing G' with
  | unit => exact HasTypeVal.unit
  | bool b => exact HasTypeVal.bool b
  | nat n => exact HasTypeVal.nat n
  | string s => exact HasTypeVal.string s
  | prod h1 h2 ih1 ih2 => exact HasTypeVal.prod (ih1 G' hMono) (ih2 G' hMono)
  | chan hLookup => exact HasTypeVal.chan (hMono _ _ hLookup)

/-- HasTypeVal is preserved when prepending disjoint endpoints to GEnv. -/
theorem HasTypeVal_prepend (G1 G2 : GEnv) (v : Value) (T : ValType)
    (hHas : HasTypeVal G2 v T)
    (hDisjoint : ∀ e L, lookupG G2 e = some L → G1.lookup e = none) :
    HasTypeVal (G1 ++ G2) v T := by
  apply HasTypeVal_mono G2 (G1 ++ G2) v T hHas
  intro e L hLookup
  simp only [lookupG, List.lookup_append]
  have hNone := hDisjoint e L hLookup
  simp only [hNone, Option.none_or]
  exact hLookup

/-- A buffer at edge e is typed by the type trace at e. -/
def BufferTyped (G : GEnv) (D : DEnv) (bufs : Buffers) (e : Edge) : Prop :=
  let buf := lookupBuf bufs e
  let trace := lookupD D e
  ∃ h : buf.length = trace.length,
    ∀ i (hi : i < buf.length),
      HasTypeVal G (buf.get ⟨i, hi⟩) (trace.get ⟨i, h ▸ hi⟩)

/-- All buffers are typed. -/
def BuffersTyped (G : GEnv) (D : DEnv) (bufs : Buffers) : Prop :=
  ∀ e, BufferTyped G D bufs e

namespace List

@[simp] theorem get_map {α β} (f : α → β) (l : List α) (i : Nat) (hi : i < l.length) :
    (l.map f).get ⟨i, by simpa [List.length_map] using hi⟩ = f (l.get ⟨i, hi⟩) := by
  induction l generalizing i with
  | nil =>
      cases hi
  | cons a tl ih =>
      cases i with
      | zero =>
          simp
      | succ i =>
          have hi' : i < tl.length := by
            simpa using hi
          simp

end List

/-- If buffer has head v with type T, then trace has head T.
    Key lemma for deriving trace head in recv case.
    Proof strategy: BufferTyped gives buf[i] : trace[i] for all i.
    At i=0, buf[0]=v has type trace[0]. Since hv says v:T, by
    HasTypeVal_unique, trace[0]=T, so trace.head? = some T. -/
theorem trace_head_from_buffer {G : GEnv} {D : DEnv} {bufs : Buffers} {e : Edge}
    {v : Value} {vs : List Value} {T : ValType}
    (hBuf : lookupBuf bufs e = v :: vs)
    (hv : HasTypeVal G v T)
    (hTyped : BufferTyped G D bufs e) :
    (lookupD D e).head? = some T := by
  -- Unpack the buffer typing proof.
  rcases hTyped with ⟨hLen, hTyping⟩
  -- Buffer is non-empty at index 0.
  have h0buf : 0 < (lookupBuf bufs e).length := by
    simp [hBuf]
  -- Trace is also non-empty by length equality.
  have h0trace : 0 < (lookupD D e).length := by
    simpa [hLen] using h0buf
  -- Typing of the head element.
  have hTyped0 := hTyping 0 h0buf
  have hTyped0' : HasTypeVal G v ((lookupD D e).get ⟨0, h0trace⟩) := by
    simpa [hBuf] using hTyped0
  -- Split on the trace to extract its head and finish by uniqueness.
  cases hTrace : lookupD D e with
  | nil =>
      -- Contradiction: trace must be non-empty.
      simp [hTrace] at h0trace
  | cons t ts =>
      have hTypeTrace0 : HasTypeVal G v t := by
        simpa [hTrace] using hTyped0'
      have hEq : T = t := HasTypeVal_unique hv hTypeTrace0
      -- head? is the first element of the trace.
      simp [hEq]



end
