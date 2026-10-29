import Mathlib.LinearAlgebra.Lagrange

set_option autoImplicit false

/-! # Distributed.Families.DataAvailability

Data availability derived from a concrete erasure-coding and custody model:
- the data is a polynomial of degree `< k` over a field `F` (Reed–Solomon),
- shard `i : Fin n` is its evaluation at the distinct point `points i`,
- each custodian holds one shard index and returns a response,
- responses are checked against a binding commitment (`verify`),
- honest custodians return their shard faithfully.

From at least `k` honest custodians holding distinct shards we prove (via
Lagrange interpolation, not by assumption) that `k` verified shards are
available and that interpolating any `≥ k` verified shards recovers the data.
-/

/-
The Problem. Earlier versions assumed sampling coverage and a withholding
bound whose conjunction was the availability conclusion, and assumed
reconstruction soundness of an abstract code.
Solution Structure. Fix Reed–Solomon coding, prove k-of-n reconstruction
with `Lagrange.eq_interpolate_of_eval_eq`, and derive availability from the
honest-custodian count.
-/

/-! ## Core Development -/

namespace Distributed
namespace DataAvailability

open Polynomial

universe u v

/-- Erasure-coded data with custody. `verify i y` is the commitment check that
`y` is the correct value of shard `i`. -/
structure Model (F : Type u) [Field F] (Party : Type v) where
  n : Nat
  k : Nat
  points : Fin n → F
  data : F[X]
  custody : Party → Fin n
  response : Party → F
  verify : Fin n → F → Prop

variable {F : Type u} [Field F] {Party : Type v}

/-- Decoder: Lagrange interpolation of the values `val` on shard indices `I`. -/
noncomputable def decode (M : Model F Party) (I : Finset (Fin M.n)) (val : Fin M.n → F) :
    F[X] :=
  Lagrange.interpolate I M.points val

/-! ## Properties -/

/-- Availability: some set of custodians serves `≥ k` distinct shards whose
responses pass the commitment check. -/
def DataAvailability (M : Model F Party) : Prop :=
  ∃ S : Finset Party, M.k ≤ (S.image M.custody).card ∧
    ∀ p ∈ S, M.verify (M.custody p) (M.response p)

/-- Retrievability: every `≥ k` set of verified shard values decodes to the data,
and such a set exists. -/
def DataRetrievability (M : Model F Party) : Prop :=
  (∀ (I : Finset (Fin M.n)) (val : Fin M.n → F),
    M.k ≤ I.card → (∀ i ∈ I, M.verify i (val i)) → decode M I val = M.data) ∧
  ∃ (I : Finset (Fin M.n)) (val : Fin M.n → F),
    M.k ≤ I.card ∧ ∀ i ∈ I, M.verify i (val i)

/-! ## Assumptions -/

/-- Coding, commitment, and custody assumptions. None mentions availability or
decoding: the commitment fields are standard binding/completeness of the
commitment scheme; the rest are concrete, decidable custody facts. -/
structure Assumptions [DecidableEq Party] (M : Model F Party) where
  honest : Finset Party
  pointsInjective : Function.Injective M.points
  dataDegree : M.data.degree < M.k
  verifyBinding : ∀ i y, M.verify i y → y = M.data.eval (M.points i)
  verifyComplete : ∀ i, M.verify i (M.data.eval (M.points i))
  honestServes : ∀ p ∈ honest, M.response p = M.data.eval (M.points (M.custody p))
  custodyDistinct : Set.InjOn M.custody honest
  honestCustodians : M.k ≤ honest.card

/-! ## k-of-n Reconstruction -/

/-- Reed–Solomon reconstruction: correct values on `≥ k` distinct points determine
a degree-`< k` polynomial. -/
theorem decode_correct (M : Model F Party) (hInj : Function.Injective M.points)
    (hDeg : M.data.degree < M.k) (I : Finset (Fin M.n)) (val : Fin M.n → F)
    (hI : M.k ≤ I.card) (hval : ∀ i ∈ I, M.data.eval (M.points i) = val i) :
    decode M I val = M.data := by
  have hd : M.data.degree < I.card :=
    lt_of_lt_of_le hDeg (by exact_mod_cast hI)
  exact (Lagrange.eq_interpolate_of_eval_eq val (hInj.injOn) hd hval).symm

/-- Verified shards decode to the data (binding commitments). -/
theorem decode_verified [DecidableEq Party] {M : Model F Party} (a : Assumptions M)
    (I : Finset (Fin M.n)) (val : Fin M.n → F) (hI : M.k ≤ I.card)
    (hv : ∀ i ∈ I, M.verify i (val i)) : decode M I val = M.data :=
  decode_correct M a.pointsInjective a.dataDegree I val hI
    (fun i hi => (a.verifyBinding i (val i) (hv i hi)).symm)

/-! ## Availability from Honest Custodians -/

/-- Honest custodians cover `≥ k` distinct shard indices. -/
theorem honest_shards_card [DecidableEq Party] {M : Model F Party} (a : Assumptions M) :
    M.k ≤ (a.honest.image M.custody).card := by
  rw [Finset.card_image_of_injOn a.custodyDistinct]
  exact a.honestCustodians

/-- Honest responses pass the commitment check. -/
theorem honest_verified [DecidableEq Party] {M : Model F Party} (a : Assumptions M)
    {p : Party} (hp : p ∈ a.honest) : M.verify (M.custody p) (M.response p) := by
  rw [a.honestServes p hp]; exact a.verifyComplete _

/-- Data availability, proved from `≥ k` honest custodians. -/
theorem availability_of_assumptions [DecidableEq Party] {M : Model F Party}
    (a : Assumptions M) : DataAvailability M :=
  ⟨a.honest, honest_shards_card a, fun _ hp => honest_verified a hp⟩

/-- Data retrievability, proved from interpolation and honest custody. -/
theorem retrievability_of_assumptions [DecidableEq Party] {M : Model F Party}
    (a : Assumptions M) : DataRetrievability M := by
  refine ⟨fun I val hI hv => decode_verified a I val hI hv, ?_⟩
  refine ⟨a.honest.image M.custody, fun i => M.data.eval (M.points i),
    honest_shards_card a, fun i _ => a.verifyComplete i⟩

/-- Sampling: a sample of any shard held by an honest custodian succeeds with a
correct value. -/
theorem sample_honest_shard [DecidableEq Party] {M : Model F Party} (a : Assumptions M)
    {p : Party} (hp : p ∈ a.honest) :
    M.verify (M.custody p) (M.response p) ∧
      M.response p = M.data.eval (M.points (M.custody p)) :=
  ⟨honest_verified a hp, a.honestServes p hp⟩

/-! ## Assumption Validation API -/

/-- Decidable custody/coding conditions. -/
inductive Assumption where
  | pointsInjective
  | custodyDistinct
  | honestCustodians
  deriving Repr, DecidableEq, Inhabited

/-- Proposition named by each label. -/
def Assumption.Holds [DecidableEq Party] (M : Model F Party) (honest : Finset Party) :
    Assumption → Prop
  | .pointsInjective => ∀ i j : Fin M.n, M.points i = M.points j → i = j
  | .custodyDistinct => ∀ p ∈ honest, ∀ q ∈ honest, M.custody p = M.custody q → p = q
  | .honestCustodians => M.k ≤ honest.card

instance [DecidableEq F] [DecidableEq Party] (M : Model F Party) (honest : Finset Party)
    (h : Assumption) : Decidable (h.Holds M honest) := by
  cases h <;> unfold Assumption.Holds <;> infer_instance

/-- Core labels. -/
def coreAssumptions : List Assumption := [.pointsInjective, .custodyDistinct, .honestCustodians]

/-- Decide one label. -/
def validateAssumption [DecidableEq F] [DecidableEq Party] (M : Model F Party)
    (honest : Finset Party) (h : Assumption) : Bool :=
  decide (h.Holds M honest)

/-- Soundness of the decision procedure. -/
theorem validateAssumption_sound [DecidableEq F] [DecidableEq Party] (M : Model F Party)
    (honest : Finset Party) (h : Assumption)
    (hPass : validateAssumption M honest h = true) : h.Holds M honest :=
  of_decide_eq_true hPass

/-- Validate all labels in a list. -/
def runAssumptionValidation [DecidableEq F] [DecidableEq Party] (M : Model F Party)
    (honest : Finset Party) (hs : List Assumption) : Bool :=
  hs.all (validateAssumption M honest)

/-- Soundness of list validation. -/
theorem runAssumptionValidation_sound [DecidableEq F] [DecidableEq Party]
    (M : Model F Party) (honest : Finset Party) (hs : List Assumption)
    (hAll : runAssumptionValidation M honest hs = true) : ∀ h ∈ hs, h.Holds M honest :=
  fun h hm => validateAssumption_sound M honest h (List.all_eq_true.1 hAll h hm)

end DataAvailability
end Distributed
