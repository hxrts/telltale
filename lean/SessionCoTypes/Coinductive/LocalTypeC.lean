import Mathlib
import SessionTypes.GlobalType

set_option linter.dupNamespace false

/-! # Coinductive Local Types

Coinductive representation of session types via polynomial functors. -/

/-
The Problem. Session types in Lean are naturally inductive, but some operations
(like bisimulation and coinductive equivalence) require an infinite/coinductive
representation supporting pattern matching on heads.

Solution Structure. Defines LocalTypeHead as constructor tags, LocalTypeChild for
children counts, builds the polynomial functor LocalTypeF and its M-type LocalTypeC.
Provides smart constructors (mkEnd, mkVar, mkMu, mkSend, mkRecv) with simp lemmas
for head extraction, children access, injectivity, and distinctness.
-/

namespace SessionCoTypes.Coinductive

open SessionTypes.GlobalType

/-! ## Polynomial Functor Components -/

/-- Constructor tags for coinductive local types.
    These are the "shapes" of nodes in the infinite tree. -/
inductive LocalTypeHead where
  | end  : LocalTypeHead
  | var  : String → LocalTypeHead
  | mu   : String → LocalTypeHead
  | send : String → List Label → LocalTypeHead
  | recv : String → List Label → LocalTypeHead
  deriving Repr, DecidableEq

/-- Children positions for each constructor tag.
    - end/var: no children (PEmpty)
    - mu: one child (Unit)
    - send/recv: one child per branch label (Fin n) -/
def LocalTypeChild : LocalTypeHead → Type
  | .end       => PEmpty
  | .var _     => PEmpty
  | .mu _      => Unit
  | .send _ ls => Fin ls.length
  | .recv _ ls => Fin ls.length

instance : Fintype PEmpty := ⟨∅, fun x => x.elim⟩

instance (h : LocalTypeHead) : Fintype (LocalTypeChild h) :=
  match h with
  | .end =>
      ⟨∅, by intro x; cases x⟩
  | .var _ =>
      ⟨∅, by intro x; cases x⟩
  | .mu _ =>
      (inferInstance : Fintype Unit)
  | .send _ labels =>
      (inferInstance : Fintype (Fin labels.length))
  | .recv _ labels =>
      (inferInstance : Fintype (Fin labels.length))

/-! ## The Coinductive Type -/

/-- Base functor for coinductive local types. -/
def LocalTypeF : PFunctor := ⟨LocalTypeHead, LocalTypeChild⟩

/-- Coinductive local types as an M-type (greatest fixpoint of LocalTypeF). -/
abbrev LocalTypeC := PFunctor.M LocalTypeF

/-! ## Accessors -/

/-- Extract the head tag of a coinductive local type. -/
def head (t : LocalTypeC) : LocalTypeHead :=
  (PFunctor.M.dest t).fst

/-- Extract the child function of a coinductive local type. -/
def children (t : LocalTypeC) : LocalTypeChild (head t) → LocalTypeC :=
  (PFunctor.M.dest t).snd

/-- Cast a Fin index across an equality of lengths. -/
def castFin {n m : Nat} (h : n = m) : Fin n → Fin m :=
  fun i => ⟨i.1, by simpa [h] using i.2⟩

/-! ## Smart Constructors -/

/-- Construct the terminated session type. -/
def mkEnd : LocalTypeC :=
  PFunctor.M.mk ⟨.end, PEmpty.elim⟩

/-- Construct a type variable reference. -/
def mkVar (x : String) : LocalTypeC :=
  PFunctor.M.mk ⟨.var x, PEmpty.elim⟩

/-- Construct a recursive type (mu-binding). -/
def mkMu (x : String) (body : LocalTypeC) : LocalTypeC :=
  PFunctor.M.mk ⟨.mu x, fun _ => body⟩

/-- Construct a send type with labeled branches. -/
def mkSend (p : String) (bs : List (Label × LocalTypeC)) : LocalTypeC :=
  let labels := bs.map Prod.fst
  let hlen : labels.length = bs.length := by simp [labels]
  let f : Fin labels.length → LocalTypeC := fun i =>
    (bs.get (castFin hlen i)).2
  PFunctor.M.mk ⟨.send p labels, f⟩

/-- Construct a receive type with labeled branches. -/
def mkRecv (p : String) (bs : List (Label × LocalTypeC)) : LocalTypeC :=
  let labels := bs.map Prod.fst
  let hlen : labels.length = bs.length := by simp [labels]
  let f : Fin labels.length → LocalTypeC := fun i =>
    (bs.get (castFin hlen i)).2
  PFunctor.M.mk ⟨.recv p labels, f⟩

/-! ## Head Extraction Lemmas -/

@[simp] theorem head_mkEnd : head mkEnd = .end := rfl
@[simp] theorem head_mkVar (x : String) : head (mkVar x) = .var x := rfl
@[simp] theorem head_mkMu (x : String) (body : LocalTypeC) : head (mkMu x body) = .mu x := rfl
@[simp] theorem head_mkSend (p : String) (bs : List (Label × LocalTypeC)) :
    head (mkSend p bs) = .send p (bs.map Prod.fst) := rfl
@[simp] theorem head_mkRecv (p : String) (bs : List (Label × LocalTypeC)) :
    head (mkRecv p bs) = .recv p (bs.map Prod.fst) := rfl

/-! ## Children Access Lemmas -/

@[simp] lemma children_mkSend (p : String) (bs : List (Label × LocalTypeC))
    (i : Fin (bs.map Prod.fst).length) :
    children (mkSend p bs) i = (bs.get (castFin (by simp) i)).2 := by
  simp [children, mkSend]

@[simp] lemma children_mkRecv (p : String) (bs : List (Label × LocalTypeC))
    (i : Fin (bs.map Prod.fst).length) :
    children (mkRecv p bs) i = (bs.get (castFin (by simp) i)).2 := by
  simp [children, mkRecv]

/-! ## Injectivity and Distinctness -/

@[simp] theorem mkVar_inj {x y : String} (h : mkVar x = mkVar y) : x = y := by
  have h' := congrArg head h; cases h'; rfl

@[simp] theorem mkMu_inj {x y : String} {a b : LocalTypeC} (h : mkMu x a = mkMu y b) : x = y := by
  have h' := congrArg head h; cases h'; rfl

@[simp] theorem mkEnd_ne_mkVar (x : String) : mkEnd ≠ mkVar x := by
  intro h; have h' := congrArg head h; cases h'

@[simp] theorem mkSend_ne_mkRecv (p q : String) (bs cs : List (Label × LocalTypeC)) :
    mkSend p bs ≠ mkRecv q cs := by
  intro h; have h' := congrArg head h; cases h'

end SessionCoTypes.Coinductive
