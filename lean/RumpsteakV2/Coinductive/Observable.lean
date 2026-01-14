import Mathlib
import RumpsteakV2.Coinductive.LocalTypeC

set_option linter.dupNamespace false

/-!
# Observables for LocalTypeC

Defines a simple notion of observability by allowing finite unfolding of `mu`
constructors to reveal an `end/var/send/recv` head.
-/

namespace RumpsteakV2.Coinductive

open RumpsteakV2.Protocol.GlobalType

/-- One-step unfolding of a `mu` node. -/
def UnfoldsC (t u : LocalTypeC) : Prop :=
  ∃ x f, PFunctor.M.dest t = ⟨LocalTypeHead.mu x, f⟩ ∧ u = f ()

/-- Finite unfolding closure. -/
def UnfoldsToC (t u : LocalTypeC) : Prop :=
  Relation.ReflTransGen UnfoldsC t u

/-- Branch list derived from the head of a node. -/
def branchesOf (t : LocalTypeC) : List (Label × LocalTypeC) :=
  match PFunctor.M.dest t with
  | ⟨LocalTypeHead.send _ labels, f⟩ =>
      let g : Fin labels.length → (Label × LocalTypeC) := fun i =>
        (labels.get i, f i)
      List.ofFn g
  | ⟨LocalTypeHead.recv _ labels, f⟩ =>
      let g : Fin labels.length → (Label × LocalTypeC) := fun i =>
        (labels.get i, f i)
      List.ofFn g
  | _ => []

@[simp]
lemma branchesOf_mkSend (p : String) (bs : List (Label × LocalTypeC)) :
    branchesOf (mkSend p bs) = bs := by
  -- expand `branchesOf` on the `mkSend` constructor
  simp only [branchesOf, mkSend, PFunctor.M.dest_mk]
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_map]
  · intro n h1 h2
    simp only [List.getElem_ofFn, castFin]
    -- Goal: ((bs.map Prod.fst).get ⟨n, _⟩, bs.get ⟨n, _⟩.2) = bs[n]
    ext
    · simp [List.get_eq_getElem]
    · simp [List.get_eq_getElem]

@[simp]
lemma branchesOf_mkRecv (p : String) (bs : List (Label × LocalTypeC)) :
    branchesOf (mkRecv p bs) = bs := by
  -- expand `branchesOf` on the `mkRecv` constructor
  simp only [branchesOf, mkRecv, PFunctor.M.dest_mk]
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_map]
  · intro n h1 h2
    simp only [List.getElem_ofFn, castFin]
    -- Goal: ((bs.map Prod.fst).get ⟨n, _⟩, bs.get ⟨n, _⟩.2) = bs[n]
    ext
    · simp [List.get_eq_getElem]
    · simp [List.get_eq_getElem]

/-- Unfolds to end after finitely many `mu` steps. -/
def UnfoldsToEndC (t : LocalTypeC) : Prop :=
  ∃ u, UnfoldsToC t u ∧ head u = .end

/-- Unfolds to var after finitely many `mu` steps. -/
def UnfoldsToVarC (t : LocalTypeC) (v : String) : Prop :=
  ∃ u, UnfoldsToC t u ∧ head u = .var v

/-- Unfolds to send with derived branches. -/
def CanSendC (t : LocalTypeC) (p : String) (bs : List (Label × LocalTypeC)) : Prop :=
  ∃ u labels,
    UnfoldsToC t u ∧ head u = .send p labels ∧ bs = branchesOf u

/-- Unfolds to recv with derived branches. -/
def CanRecvC (t : LocalTypeC) (p : String) (bs : List (Label × LocalTypeC)) : Prop :=
  ∃ u labels,
    UnfoldsToC t u ∧ head u = .recv p labels ∧ bs = branchesOf u

/-- Observable heads reachable by finite `mu` unfolding. -/
inductive ObservableC (t : LocalTypeC) : Prop
  | is_end : UnfoldsToEndC t → ObservableC t
  | is_var (v : String) : UnfoldsToVarC t v → ObservableC t
  | is_send (p : String) (bs : List (Label × LocalTypeC)) : CanSendC t p bs → ObservableC t
  | is_recv (p : String) (bs : List (Label × LocalTypeC)) : CanRecvC t p bs → ObservableC t

/-! ## Closedness and WellFormedness -/

/-- A coinductive local type is closed if no variable head is reachable. -/
def ClosedC (t : LocalTypeC) : Prop :=
  ∀ v, ¬ UnfoldsToVarC t v

/-- WellFormed coinductive local types: closed and observable. -/
structure WellFormedC (t : LocalTypeC) : Prop where
  closed : ClosedC t
  observable : ObservableC t

end RumpsteakV2.Coinductive
