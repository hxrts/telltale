import Mathlib.Data.Finset.Basic

set_option autoImplicit false

/-! # Distributed.Families.Coordination

CALM-style coordination characterization for a concrete query model:
- a query maps a finite set of delivered input facts to a set of output facts,
- a coordination-free replica answers on whatever prefix of a delivery order
  it has received so far,
- it is safe iff no answer emitted on a prefix is retracted once the rest of
  the input arrives.

We prove: coordination-free answering is safe iff the query is monotone, and a
non-monotone query has a delivery order on which a coordination-free answer
is retracted (so the replica must coordinate to learn the input is complete).

Scope: this is the order-theoretic core of CALM. It does not model
transducer networks or prove the distributed-computability direction.
-/

/-
The Problem. Earlier versions carried both halves of the characterization as
premises plus an excluded-middle "assumption".
Solution Structure. Define safety over delivery orders, then prove both
directions from the definition of monotonicity; no assumptions remain.
-/

/-! ## Core Development -/

namespace Distributed
namespace Coordination

universe u v

/-- A query over finite sets of delivered input facts. -/
structure Model (Input : Type u) (Output : Type v) where
  query : Finset Input → Set Output

variable {Input : Type u} {Output : Type v} [DecidableEq Input]

/-- Facts delivered by a list of messages. -/
def delivered (xs : List Input) : Finset Input := xs.toFinset

/-- Monotone query: more input never removes output facts. -/
def MonotoneUpdates (M : Model Input Output) : Prop :=
  ∀ I J : Finset Input, I ⊆ J → M.query I ⊆ M.query J

/-- Coordination-free safety: answering on any delivered prefix never emits a
fact that the answer on the full delivery retracts. -/
def CoordinationFreeSafety (M : Model Input Output) : Prop :=
  ∀ pre rest : List Input, M.query (delivered pre) ⊆ M.query (delivered (pre ++ rest))

/-- Coordination required: some delivery prefix yields an output fact that the
full delivery retracts. -/
def CoordinationRequired (M : Model Input Output) : Prop :=
  ∃ (pre rest : List Input) (o : Output),
    o ∈ M.query (delivered pre) ∧ o ∉ M.query (delivered (pre ++ rest))

/-- Combined coordination characterization. -/
def CoordinationCharacterization (M : Model Input Output) : Prop :=
  (MonotoneUpdates M → CoordinationFreeSafety M) ∧
  (¬ MonotoneUpdates M → CoordinationRequired M)

/-! ## Proofs -/

/-- A prefix delivers a subset of the full delivery. -/
theorem delivered_prefix_subset (pre rest : List Input) :
    delivered pre ⊆ delivered (pre ++ rest) := by
  intro x hx
  simp only [delivered, List.mem_toFinset, List.mem_append] at hx ⊢
  exact Or.inl hx

/-- Every pair `I ⊆ J` is realised by a delivery prefix and its extension. -/
theorem delivered_realises {I J : Finset Input} (h : I ⊆ J) :
    delivered I.toList = I ∧ delivered (I.toList ++ (J \ I).toList) = J := by
  refine ⟨by simp [delivered], ?_⟩
  ext x
  simp only [delivered, List.mem_toFinset, List.mem_append, Finset.mem_toList,
    Finset.mem_sdiff]
  constructor
  · rintro (hx | ⟨hx, _⟩)
    exacts [h hx, hx]
  · intro hx; by_cases hI : x ∈ I
    exacts [Or.inl hI, Or.inr ⟨hx, hI⟩]

/-- Monotone queries are safe without coordination. -/
theorem coordination_free_of_monotone (M : Model Input Output)
    (h : MonotoneUpdates M) : CoordinationFreeSafety M :=
  fun pre rest => h _ _ (delivered_prefix_subset pre rest)

/-- Coordination-free safety forces monotonicity (converse of CALM). -/
theorem monotone_of_coordination_free (M : Model Input Output)
    (h : CoordinationFreeSafety M) : MonotoneUpdates M := by
  intro I J hIJ
  obtain ⟨h1, h2⟩ := delivered_realises hIJ
  have := h I.toList (J \ I).toList
  rwa [h1, h2] at this

/-- Monotonicity characterises coordination-free safety. -/
theorem monotone_iff_coordination_free (M : Model Input Output) :
    MonotoneUpdates M ↔ CoordinationFreeSafety M :=
  ⟨coordination_free_of_monotone M, monotone_of_coordination_free M⟩

/-- Non-monotone queries require coordination. -/
theorem coordination_required_of_non_monotone (M : Model Input Output)
    (h : ¬ MonotoneUpdates M) : CoordinationRequired M := by
  have hNot : ¬ CoordinationFreeSafety M := fun hc => h (monotone_of_coordination_free M hc)
  simp only [CoordinationFreeSafety, Set.subset_def, not_forall] at hNot
  obtain ⟨pre, rest, o, ho, hno⟩ := hNot
  exact ⟨pre, rest, o, ho, hno⟩

/-- The coordination characterization, proved for every query model. -/
theorem coordination_characterization (M : Model Input Output) :
    CoordinationCharacterization M :=
  ⟨coordination_free_of_monotone M, coordination_required_of_non_monotone M⟩

end Coordination
end Distributed
