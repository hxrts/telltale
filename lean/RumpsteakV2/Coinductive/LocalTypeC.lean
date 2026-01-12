import Mathlib
import RumpsteakV2.Protocol.GlobalType

set_option linter.dupNamespace false

/-!
# LocalTypeC (Coinductive Session Types)

This module defines a coinductive session type `LocalTypeC` as the M-type of a
polynomial functor. It provides smart constructors and basic head/injectivity
lemmas to support case analysis and distinctness proofs.
-/

namespace RumpsteakV2.Coinductive

open RumpsteakV2.Protocol.GlobalType

/-- Constructor tags for coinductive local types. -/
inductive LocalTypeHead where
  | end : LocalTypeHead
  | var : String → LocalTypeHead
  | mu : String → LocalTypeHead
  | send : String → List Label → LocalTypeHead
  | recv : String → List Label → LocalTypeHead
  deriving Repr, DecidableEq

/-- Children positions for each constructor tag. -/
def LocalTypeChild : LocalTypeHead → Type
  | .end => PEmpty
  | .var _ => PEmpty
  | .mu _ => Unit
  | .send _ labels => Fin labels.length
  | .recv _ labels => Fin labels.length

instance : Fintype PEmpty := by
  refine ⟨∅, ?_⟩
  intro x
  cases x

instance (h : LocalTypeHead) : Fintype (LocalTypeChild h) :=
  match h with
  | .end =>
      ⟨∅, by
        intro x
        cases x⟩
  | .var _ =>
      ⟨∅, by
        intro x
        cases x⟩
  | .mu _ =>
      (inferInstance : Fintype Unit)
  | .send _ labels =>
      (inferInstance : Fintype (Fin labels.length))
  | .recv _ labels =>
      (inferInstance : Fintype (Fin labels.length))

/-- Base functor for coinductive local types. -/
def LocalTypeF : PFunctor := ⟨LocalTypeHead, LocalTypeChild⟩

/-- Coinductive local types as an M-type. -/
abbrev LocalTypeC := PFunctor.M LocalTypeF

/-- Access the head tag of a coinductive local type. -/
def head (t : LocalTypeC) : LocalTypeHead := (PFunctor.M.dest t).fst

/-- Access the child function of a coinductive local type. -/
def children (t : LocalTypeC) : LocalTypeChild (head t) → LocalTypeC :=
  (PFunctor.M.dest t).snd

/-- Cast a `Fin` index across an equality of lengths. -/
def castFin {n m : Nat} (h : n = m) : Fin n → Fin m := fun i =>
  ⟨i.1, by simpa [h] using i.2⟩

/-- Smart constructor for `.end`. -/
def mkEnd : LocalTypeC :=
  PFunctor.M.mk ⟨LocalTypeHead.end, fun x => PEmpty.elim x⟩

/-- Smart constructor for `.var`. -/
def mkVar (x : String) : LocalTypeC :=
  PFunctor.M.mk ⟨LocalTypeHead.var x, fun x => PEmpty.elim x⟩

/-- Smart constructor for `.mu`. -/
def mkMu (x : String) (body : LocalTypeC) : LocalTypeC :=
  PFunctor.M.mk ⟨LocalTypeHead.mu x, fun _ => body⟩

/-- Smart constructor for `.send` with branch labels. -/
def mkSend (p : String) (bs : List (Label × LocalTypeC)) : LocalTypeC :=
  let labels := bs.map Prod.fst
  let hlen : labels.length = bs.length := by
    simp [labels]
  let f : Fin labels.length → LocalTypeC := fun i =>
    let i' : Fin bs.length := castFin hlen i
    (bs.get i').2
  PFunctor.M.mk ⟨LocalTypeHead.send p labels, f⟩

/-- Smart constructor for `.recv` with branch labels. -/
def mkRecv (p : String) (bs : List (Label × LocalTypeC)) : LocalTypeC :=
  let labels := bs.map Prod.fst
  let hlen : labels.length = bs.length := by
    simp [labels]
  let f : Fin labels.length → LocalTypeC := fun i =>
    let i' : Fin bs.length := castFin hlen i
    (bs.get i').2
  PFunctor.M.mk ⟨LocalTypeHead.recv p labels, f⟩

@[simp] theorem head_mkEnd : head mkEnd = LocalTypeHead.end := rfl
@[simp] theorem head_mkVar (x : String) : head (mkVar x) = LocalTypeHead.var x := rfl
@[simp] theorem head_mkMu (x : String) (body : LocalTypeC) :
    head (mkMu x body) = LocalTypeHead.mu x := rfl

@[simp] theorem head_mkSend (p : String) (bs : List (Label × LocalTypeC)) :
    head (mkSend p bs) = LocalTypeHead.send p (bs.map Prod.fst) := rfl

@[simp] theorem head_mkRecv (p : String) (bs : List (Label × LocalTypeC)) :
    head (mkRecv p bs) = LocalTypeHead.recv p (bs.map Prod.fst) := rfl

/-- Injectivity for `mkVar` via head tags. -/
@[simp] theorem mkVar_inj {x y : String} (h : mkVar x = mkVar y) : x = y := by
  have h' := congrArg head h
  cases h'
  rfl

/-- Injectivity for `mkMu` via head tags. -/
@[simp] theorem mkMu_inj {x y : String} {a b : LocalTypeC} (h : mkMu x a = mkMu y b) : x = y := by
  have h' := congrArg head h
  cases h'
  rfl

/-- Distinctness: `.end` is not a `.var`. -/
@[simp] theorem mkEnd_ne_mkVar (x : String) : mkEnd ≠ mkVar x := by
  intro h
  have h' := congrArg head h
  cases h'

/-- Distinctness: `.send` is not a `.recv`. -/
@[simp] theorem mkSend_ne_mkRecv (p q : String) (bs cs : List (Label × LocalTypeC)) :
    mkSend p bs ≠ mkRecv q cs := by
  intro h
  have h' := congrArg head h
  cases h'

end RumpsteakV2.Coinductive
