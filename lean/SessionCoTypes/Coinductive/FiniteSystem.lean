import Mathlib
import SessionCoTypes.Coinductive.LocalTypeC
import SessionCoTypes.Coinductive.Regularity

set_option linter.dupNamespace false

/-!
The Problem. To convert regular coinductive types back to inductive types or
to reason about them algorithmically, we need a finite representation. A regular
type has finitely many reachable states, so we can index them with Fin n.

Solution Structure.
1. Extract the reachable states as a list (ReachableList)
2. Assign each state an index (StateIndex)
3. Define FiniteSystem as a coalgebra on Fin n
4. Build RegularSystem: the finite coalgebra extracted from a regular type
5. Provide SystemToCoind: reconstruct LocalTypeC from a finite system
-/

namespace SessionCoTypes.Coinductive

open Classical

/-! ## State Indexing -/

/-- List of reachable states from an explicit finite witness. -/
def ReachableList {t : LocalTypeC} (w : Regular t) : List LocalTypeC :=
  w.states

/-- Index a state in the witness list. Defaults to 0 if not found. -/
def StateIndex [DecidableEq LocalTypeC] {t : LocalTypeC} (w : Regular t) (s : LocalTypeC) :
    Fin (ReachableList w).length :=
  match (ReachableList w).finIdxOf? s with
  | some i => i
  | none =>
      ⟨0, by
        exact List.length_pos_of_mem w.root_mem⟩

/-! ## Finite Coalgebra -/

/-- A finite coalgebra presentation: maps each state index to its one-step unfolding. -/
def FiniteSystem (n : Nat) := Fin n → LocalTypeF.Obj (Fin n)

/-- Reconstruct a coinductive type from a finite system and start state. -/
def SystemToCoind {n : Nat} (sys : FiniteSystem n) (start : Fin n) : LocalTypeC :=
  PFunctor.M.corec sys start

/-! ## Extraction from Regular Types -/

/-- Extract a finite coalgebra from a regular coinductive type.
    Each reachable state maps to its destructor with children indexed. -/
def RegularSystem [DecidableEq LocalTypeC] {t : LocalTypeC} (w : Regular t) :
    FiniteSystem (ReachableList w).length :=
  fun i =>
    match PFunctor.M.dest ((ReachableList w).get i) with
    | ⟨.end, _⟩      => ⟨.end, PEmpty.elim⟩
    | ⟨.var v, _⟩    => ⟨.var v, PEmpty.elim⟩
    | ⟨.mu v, f⟩     => ⟨.mu v, fun _ => StateIndex w (f ())⟩
    | ⟨.send p ls, f⟩ => ⟨.send p ls, fun j => StateIndex w (f j)⟩
    | ⟨.recv p ls, f⟩ => ⟨.recv p ls, fun j => StateIndex w (f j)⟩

/-! ## Bridge from `Regular` -/

/-- Extract list-based reachable witness data from a constructive regular witness. -/
def witnessOfRegular {t : LocalTypeC} (h : Regular t) : Regular t := h

end SessionCoTypes.Coinductive
