import Mathlib.LinearAlgebra.Lagrange

set_option autoImplicit false

/-! # Distributed.Families.DataAvailability

Data availability derived from a concrete erasure-coding, custody, and
withholding-adversary model:
- the data is a polynomial of degree `< k` over a field `F` (Reed–Solomon),
- shard `i : Fin n` is its evaluation at the distinct point `points i`,
- each custodian holds one shard index and answers a query with
  `response p : Option F`; `none` is withholding. Byzantine custodians are
  unconstrained (withhold, or serve arbitrary values); honest custodians serve
  their correct shard,
- a retriever queries every custodian and keeps, per shard, a response that
  passes the commitment check `verify` (`collect`); a shard sample succeeds
  iff `collect` yields a value (`SampleSucceeds`),
- the commitment's binding property is a separately named cryptographic
  assumption (`CommitmentBinding`): verified openings are correct. It says
  nothing about whether anything is served.

Theorems: with `≥ k` honest custodians on distinct shards, `≥ k` shards are
retrievable despite withholding (`availability_of_assumptions`), and decoding
the retrieved shards yields the data (`retrievability_of_assumptions`, via
Lagrange interpolation in `decode_correct`). Sampling: if availability fails,
every sample set of size `≥ k` contains a failing sample
(`sampling_detects_unavailability`). Probabilistic sampling amplification is
not modelled.
-/

/-
The Problem. An earlier version made `verify` definitionally correctness and
stated availability as the honest-serving count itself.
Solution Structure. Model withholding responses and a concrete collection
procedure; state binding as a named cryptographic assumption; prove that the
procedure retrieves `≥ k` shards and decodes the data.
-/

/-! ## Core Development -/

namespace Distributed
namespace DataAvailability

open Polynomial

universe u v

/-- Erasure-coded data with custody and possibly withheld responses.
`verify i y` is the commitment check for an opening of shard `i` to `y`. -/
structure Model (F : Type u) [Field F] (Party : Type v) where
  n : Nat
  k : Nat
  points : Fin n → F
  data : F[X]
  custody : Party → Fin n
  response : Party → Option F
  verify : Fin n → F → Prop

variable {F : Type u} [Field F] {Party : Type v}

/-- Decoder: Lagrange interpolation of the values `val` on shard indices `I`. -/
noncomputable def decode (M : Model F Party) (I : Finset (Fin M.n)) (val : Fin M.n → F) :
    F[X] :=
  Lagrange.interpolate I M.points val

/-- Some custodian of shard `i` served `y`, and `y` passes the commitment check. -/
def Served (M : Model F Party) (i : Fin M.n) (y : F) : Prop :=
  ∃ p, M.custody p = i ∧ M.response p = some y ∧ M.verify i y

open Classical in
/-- Retrieval: for each shard, a verified served value, if any. -/
noncomputable def collect (M : Model F Party) (i : Fin M.n) : Option F :=
  if h : ∃ y, Served M i y then some (Classical.choose h) else none

/-- A sample of shard `i` succeeds iff retrieval yields a verified value. -/
def SampleSucceeds (M : Model F Party) (i : Fin M.n) : Prop := (collect M i).isSome

open Classical in
/-- Shards the retriever obtains. -/
noncomputable def retrievable (M : Model F Party) : Finset (Fin M.n) :=
  Finset.univ.filter (SampleSucceeds M)

/-- The retriever's output: decode the retrieved shards. -/
noncomputable def retrieved (M : Model F Party) : F[X] :=
  decode M (retrievable M) (fun i => (collect M i).getD 0)

/-! ## Properties -/

/-- Availability: the retriever obtains at least `k` distinct verified shards. -/
def DataAvailability (M : Model F Party) : Prop := M.k ≤ (retrievable M).card

/-- Retrievability: the retriever's decoded output is the data. -/
def DataRetrievability (M : Model F Party) : Prop := retrieved M = M.data

/-- Commitment binding (cryptographic assumption, e.g. KZG binding under its
hardness assumption): any opening that verifies is the true evaluation. It
constrains only what verifies, not what is served. -/
def CommitmentBinding (M : Model F Party) : Prop :=
  ∀ i y, M.verify i y → y = M.data.eval (M.points i)

/-! ## Assumptions -/

/-- Coding, commitment, and custody assumptions. Non-honest custodians'
responses are unconstrained (the withholding adversary). -/
structure Assumptions [DecidableEq Party] (M : Model F Party) where
  honest : Finset Party
  pointsInjective : Function.Injective M.points
  dataDegree : M.data.degree < M.k
  /-- Cryptographic binding of the commitment. -/
  binding : CommitmentBinding M
  /-- Completeness of the commitment: correct openings verify. -/
  verifyComplete : ∀ i, M.verify i (M.data.eval (M.points i))
  honestServes : ∀ p ∈ honest, M.response p = some (M.data.eval (M.points (M.custody p)))
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

/-- Verified shards decode to the data (under commitment binding). -/
theorem decode_verified [DecidableEq Party] {M : Model F Party} (a : Assumptions M)
    (I : Finset (Fin M.n)) (val : Fin M.n → F) (hI : M.k ≤ I.card)
    (hv : ∀ i ∈ I, M.verify i (val i)) : decode M I val = M.data :=
  decode_correct M a.pointsInjective a.dataDegree I val hI
    (fun i hi => (a.binding i (val i) (hv i hi)).symm)

/-! ## Retrieval -/

/-- A collected value was served and verifies. -/
theorem collect_verified {M : Model F Party} {i : Fin M.n} {y : F}
    (h : collect M i = some y) : M.verify i y := by
  unfold collect at h
  split at h
  · next hs =>
    cases h
    obtain ⟨_, _, _, hv⟩ := Classical.choose_spec hs
    exact hv
  · cases h

/-- Retrieved shards carry verified values. -/
theorem retrievable_verified {M : Model F Party} {i : Fin M.n} (hi : i ∈ retrievable M) :
    M.verify i ((collect M i).getD 0) := by
  classical
  simp only [retrievable, Finset.mem_filter, SampleSucceeds] at hi
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hi.2
  rw [hy]; exact collect_verified hy

/-- Shards of honest custodians are retrievable, whatever others withhold. -/
theorem honest_shard_retrievable [DecidableEq Party] {M : Model F Party} (a : Assumptions M)
    {p : Party} (hp : p ∈ a.honest) : M.custody p ∈ retrievable M := by
  classical
  have hs : ∃ y, Served M (M.custody p) y :=
    ⟨_, p, rfl, a.honestServes p hp, a.verifyComplete _⟩
  simp [retrievable, SampleSucceeds, collect, hs]

/-! ## Availability and Retrievability -/

/-- Data availability, proved from `≥ k` honest custodians on distinct shards. -/
theorem availability_of_assumptions [DecidableEq Party] {M : Model F Party}
    (a : Assumptions M) : DataAvailability M := by
  have h : a.honest.image M.custody ⊆ retrievable M := by
    intro i hi
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hi
    exact honest_shard_retrievable a hp
  have := Finset.card_le_card h
  rw [Finset.card_image_of_injOn a.custodyDistinct] at this
  exact le_trans a.honestCustodians this

/-- Data retrievability: decoding the retrieved shards yields the data. -/
theorem retrievability_of_assumptions [DecidableEq Party] {M : Model F Party}
    (a : Assumptions M) : DataRetrievability M :=
  decode_verified a _ _ (availability_of_assumptions a) fun _ hi => retrievable_verified hi

/-- Sampling: if fewer than `k` shards are retrievable, every sample set of size
`≥ k` contains a failing sample. -/
theorem sampling_detects_unavailability {M : Model F Party} (hU : ¬ DataAvailability M)
    (T : Finset (Fin M.n)) (hT : M.k ≤ T.card) : ∃ i ∈ T, ¬ SampleSucceeds M i := by
  classical
  by_contra h
  have hsub : T ⊆ retrievable M := fun i hi => by
    simp only [retrievable, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Classical.byContradiction fun hn => h ⟨i, hi, hn⟩
  exact hU (le_trans hT (Finset.card_le_card hsub))

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
