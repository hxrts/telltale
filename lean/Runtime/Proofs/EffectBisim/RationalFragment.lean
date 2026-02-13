import Runtime.Proofs.EffectBisim.Core
import SessionCoTypes.Coinductive.RationalFragment

/-! # Runtime.Proofs.EffectBisim.RationalFragment

Rational-fragment interface for effect-level bisimulation transport.
-/

/-
The Problem. Phase-D tasks require an effect-level "rational fragment" with
finite witnesses, transport into the existing coinductive finite-erasure
pipeline, a checker interface, and a strict boundary witness.

Solution Structure. Reuse the already-proved `SessionCoTypes` rational-fragment
infrastructure by introducing an explicit effect-to-coinductive encoding. The
effect fragment is then defined as "encoded state is rational". Finite witness
and strict-boundary theorems are transported through that encoding.
-/

set_option autoImplicit false

namespace Runtime.Proofs.EffectBisim

open SessionCoTypes.Coinductive

section

universe u

/-! ## Effect-to-Coinductive Encoding -/

/-- Encoding of effect states into the coinductive local-type universe. -/
structure EffectEncoding (σ : Type u) where
  encode : σ → LocalTypeC

/-- Effect-level rational fragment: encoded state lies in `RationalC`. -/
def RationalEffectFragment {σ : Type u} (enc : EffectEncoding σ) (s : σ) : Prop :=
  RationalC (enc.encode s)

/-- Effect-level finite-erasure transportability for an encoded state. -/
def EffectFiniteTransportable {σ : Type u} (enc : EffectEncoding σ) (s : σ) : Prop :=
  FiniteErasureTransportable (enc.encode s)

/-! ## Finite Witness Representation -/

/-- Finite witness object for effect-level rational states. -/
structure EffectFiniteWitness {σ : Type u} (enc : EffectEncoding σ) (s : σ) where
  n : Nat
  sys : FiniteSystem n
  start : Fin n
  bisim : Bisim (enc.encode s) (SystemToCoind sys start)

/-- Rational fragment members admit explicit finite witnesses. -/
theorem rationalEffect_has_finiteWitness {σ : Type u}
    (enc : EffectEncoding σ) (s : σ)
    (hRat : RationalEffectFragment enc s) :
    Nonempty (EffectFiniteWitness enc s) := by
  rcases rational_has_finite_bisimulation (enc.encode s) hRat with ⟨n, sys, start, hBisim⟩
  exact ⟨⟨n, sys, start, hBisim⟩⟩

/-- Any finite witness certifies effect-level finite-erasure transportability. -/
theorem finiteWitness_transportable {σ : Type u}
    {enc : EffectEncoding σ} {s : σ}
    (w : EffectFiniteWitness enc s) :
    EffectFiniteTransportable enc s :=
  ⟨w.n, w.sys, w.start, w.bisim⟩

/-- Finite witnesses are adequate for rational-fragment membership. -/
theorem finiteWitness_rational {σ : Type u}
    {enc : EffectEncoding σ} {s : σ}
    (w : EffectFiniteWitness enc s) :
    RationalEffectFragment enc s :=
  finite_erasure_transportable_implies_rational (enc.encode s) (finiteWitness_transportable w)

/-! ## Transport Bridge into Existing Pipeline -/

/-- Rational effect states transport into finite-erasure transportability. -/
theorem rationalEffect_transport_bridge {σ : Type u}
    (enc : EffectEncoding σ) (s : σ)
    (hRat : RationalEffectFragment enc s) :
    EffectFiniteTransportable enc s :=
  (rational_iff_finite_erasure_transportable (enc.encode s)).1 hRat

/-- Rational effect states admit a finite-system bisimulation witness. -/
theorem rationalEffect_transport_to_regularSystem {σ : Type u}
    (enc : EffectEncoding σ) (s : σ)
    (hRat : RationalEffectFragment enc s) :
    ∃ (n : Nat) (sys : FiniteSystem n) (start : Fin n),
      Bisim (enc.encode s) (SystemToCoind sys start) :=
  rational_has_finite_bisimulation (enc.encode s) hRat

/-! ## Decidable Checker Interface (Witness-Passing Form) -/

/-- Executable checker: accepts exactly explicit witness payloads. -/
def checkRationalEffectWitness {σ : Type u}
    {enc : EffectEncoding σ} {s : σ}
    (candidate : Option (EffectFiniteWitness enc s)) : Bool :=
  candidate.isSome

/-- Soundness: accepted witness payloads certify rational-fragment membership. -/
theorem checkRationalEffectWitness_sound {σ : Type u}
    {enc : EffectEncoding σ} {s : σ}
    {candidate : Option (EffectFiniteWitness enc s)}
    (hCheck : checkRationalEffectWitness candidate = true) :
    RationalEffectFragment enc s := by
  cases candidate with
  | none =>
      simp [checkRationalEffectWitness] at hCheck
  | some w =>
      simpa [checkRationalEffectWitness] using finiteWitness_rational (w := w)

/-- Completeness: every rational-fragment member has an accepted witness payload. -/
theorem checkRationalEffectWitness_complete {σ : Type u}
    (enc : EffectEncoding σ) (s : σ)
    (hRat : RationalEffectFragment enc s) :
    ∃ candidate : Option (EffectFiniteWitness enc s),
      checkRationalEffectWitness candidate = true := by
  rcases rationalEffect_has_finiteWitness enc s hRat with ⟨w⟩
  exact ⟨some w, rfl⟩

/-! ## Strict Boundary Witness -/

/-- Identity encoding from coinductive types into the effect-level fragment API. -/
def coinductiveIdentityEncoding : EffectEncoding LocalTypeC where
  encode := id

/-- Strict boundary witness: some encoded states are outside the rational
    fragment and therefore outside finite-erasure transportability. -/
theorem strict_boundary_witness_effect :
    ∃ s : LocalTypeC,
      ¬ RationalEffectFragment coinductiveIdentityEncoding s ∧
      ¬ EffectFiniteTransportable coinductiveIdentityEncoding s := by
  rcases strict_boundary_witness with ⟨t, hNotRat, hNotTransport⟩
  exact ⟨t, hNotRat, hNotTransport⟩

end

end Runtime.Proofs.EffectBisim
