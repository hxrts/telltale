import Mathlib
import RumpsteakV2.Coinductive.LocalTypeC

set_option linter.dupNamespace false

/-!
The Problem. Coinductive local types (LocalTypeC) are infinite trees built
from a polynomial functor. Unlike inductive types, we cannot pattern match
on their structure directly. To reason about them, we need a notion of
"observability" - what the type looks like after finitely many mu-unfoldings.

The difficulty is that mu nodes can be nested arbitrarily deep. A type like
`mu x. mu y. send p [l: end]` requires two unfoldings before we see the send.
We need a relation that captures "after some finite unfolding, the head is H".

Solution Structure.
1. Define one-step unfolding (UnfoldsC) for mu nodes
2. Take reflexive-transitive closure to get finite unfolding (UnfoldsToC)
3. Define observable predicates: UnfoldsToEndC, UnfoldsToVarC, CanSendC, CanRecvC
4. Combine into ObservableC - the type has some observable head
5. Define ClosedC (no free variables) and WellFormedC (closed + observable)
-/

namespace RumpsteakV2.Coinductive

open RumpsteakV2.Protocol.GlobalType

/-! ## Finite Unfolding -/

/-- One-step unfolding of a `mu` node.
    If t = mu x. body, then UnfoldsC t body holds. -/
def UnfoldsC (t u : LocalTypeC) : Prop :=
  ∃ x f, PFunctor.M.dest t = ⟨LocalTypeHead.mu x, f⟩ ∧ u = f ()

/-- Finite unfolding closure: t unfolds to u in zero or more mu steps. -/
def UnfoldsToC (t u : LocalTypeC) : Prop :=
  Relation.ReflTransGen UnfoldsC t u

/-! ## Branch Extraction -/

/-- Extract the branch list from a send/recv node.
    Returns the list of (label, continuation) pairs. -/
def branchesOf (t : LocalTypeC) : List (Label × LocalTypeC) :=
  match PFunctor.M.dest t with
  | ⟨LocalTypeHead.send _ labels, f⟩ =>
      List.ofFn fun i => (labels.get i, f i)
  | ⟨LocalTypeHead.recv _ labels, f⟩ =>
      List.ofFn fun i => (labels.get i, f i)
  | _ => []

@[simp]
lemma branchesOf_mkSend (p : String) (bs : List (Label × LocalTypeC)) :
    branchesOf (mkSend p bs) = bs := by
  simp only [branchesOf, mkSend, PFunctor.M.dest_mk]
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_map]
  · intro n h1 h2
    simp only [List.getElem_ofFn, castFin]
    ext <;> simp [List.get_eq_getElem]

@[simp]
lemma branchesOf_mkRecv (p : String) (bs : List (Label × LocalTypeC)) :
    branchesOf (mkRecv p bs) = bs := by
  simp only [branchesOf, mkRecv, PFunctor.M.dest_mk]
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_map]
  · intro n h1 h2
    simp only [List.getElem_ofFn, castFin]
    ext <;> simp [List.get_eq_getElem]

/-! ## Observable Heads -/

/-- The type unfolds to `end` after finitely many mu steps. -/
def UnfoldsToEndC (t : LocalTypeC) : Prop :=
  ∃ u, UnfoldsToC t u ∧ head u = .end

/-- The type unfolds to `var v` after finitely many mu steps. -/
def UnfoldsToVarC (t : LocalTypeC) (v : String) : Prop :=
  ∃ u, UnfoldsToC t u ∧ head u = .var v

/-- The type unfolds to `send p [...]` after finitely many mu steps.
    The branches are extracted via branchesOf. -/
def CanSendC (t : LocalTypeC) (p : String) (bs : List (Label × LocalTypeC)) : Prop :=
  ∃ u labels, UnfoldsToC t u ∧ head u = .send p labels ∧ bs = branchesOf u

/-- The type unfolds to `recv p [...]` after finitely many mu steps.
    The branches are extracted via branchesOf. -/
def CanRecvC (t : LocalTypeC) (p : String) (bs : List (Label × LocalTypeC)) : Prop :=
  ∃ u labels, UnfoldsToC t u ∧ head u = .recv p labels ∧ bs = branchesOf u

/-! ## Base cases from head equality -/

lemma UnfoldsToEndC_of_head {t : LocalTypeC} (h : head t = .end) : UnfoldsToEndC t := by
  exact ⟨t, Relation.ReflTransGen.refl, h⟩

lemma UnfoldsToVarC_of_head {t : LocalTypeC} {v : String} (h : head t = .var v) :
    UnfoldsToVarC t v := by
  exact ⟨t, Relation.ReflTransGen.refl, h⟩

lemma CanSendC_of_head {t : LocalTypeC} {p : String} {labels : List Label}
    (h : head t = .send p labels) : CanSendC t p (branchesOf t) := by
  exact ⟨t, labels, Relation.ReflTransGen.refl, h, rfl⟩

lemma CanRecvC_of_head {t : LocalTypeC} {p : String} {labels : List Label}
    (h : head t = .recv p labels) : CanRecvC t p (branchesOf t) := by
  exact ⟨t, labels, Relation.ReflTransGen.refl, h, rfl⟩

/-! ## Observability -/

/-- A coinductive type is observable if it reaches some communication head
    (end, var, send, or recv) after finitely many mu unfoldings.

    This is the fundamental well-formedness property: it ensures the type
    has a meaningful structure we can reason about. -/
inductive ObservableC (t : LocalTypeC) : Prop
  | is_end  : UnfoldsToEndC t → ObservableC t
  | is_var  (v : String) : UnfoldsToVarC t v → ObservableC t
  | is_send (p : String) (bs : List (Label × LocalTypeC)) : CanSendC t p bs → ObservableC t
  | is_recv (p : String) (bs : List (Label × LocalTypeC)) : CanRecvC t p bs → ObservableC t

/-! ## Closedness and Well-Formedness -/

/-- A coinductive local type is closed if no free variable is reachable.
    This means UnfoldsToVarC t v is false for all v. -/
def ClosedC (t : LocalTypeC) : Prop :=
  ∀ v, ¬ UnfoldsToVarC t v

/-- A coinductive local type is well-formed if it is both closed (no free
    variables) and observable (has a meaningful head structure).

    Well-formed types are the ones we can actually work with in proofs:
    - ClosedC ensures no dangling variable references
    - ObservableC ensures the type has observable behavior -/
structure WellFormedC (t : LocalTypeC) : Prop where
  closed : ClosedC t
  observable : ObservableC t

end RumpsteakV2.Coinductive
