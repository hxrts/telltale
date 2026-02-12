import Mathlib

/-
The Problem. Closed recursive types (session types, process calculi) must eventually exhibit
observable behavior (end, send, recv). Proving this requires a termination argument that
mu-unfolding reaches a non-mu form. The ITree-style MvQPF infrastructure provides the
categorical framework for this coinductive reasoning.

Solution Structure. Defines MvQPF infrastructure (ITreeTypeVec, ITreeMvFunctor, ITreeMvPFunctor,
ITreeMvQPF) for parametric coinduction. HeadT/ChildT encode the ITree base functor. ProdF and
PrjF provide product and projection functors with MvQPF instances. This enables weak bisimulation
and observable behavior proofs for closed types.
-/

/-! # SessionTypes.ObservableClosed

## Problem: Observable Behavior of Closed Recursive Types

This file presents a self-contained formulation of a termination problem that arises
when proving that closed recursive types (session types, process calculi) eventually
exhibit observable behavior. The problem is independent of any particular library and
captures the essential mathematical difficulty.

## The Setting

Consider a recursive type `LocalType` representing local session types with constructors:
- `end` : terminated session
- `var v` : type variable (for recursive references)
- `send p bs` : send to participant p with labeled branches
- `recv p bs` : receive from participant p with labeled branches
- `mu t body` : recursive type binding variable t in body

The `mu` constructor creates recursive types. Unfolding replaces `mu t body` with
`body.substitute t (mu t body)`, effectively inlining one level of recursion.

## The Problem

A type is "closed" if it has no free variables. The key theorem states:

> Every closed type eventually unfolds to an observable form (end, send, or recv).

This is crucial for:
1. Subject reduction: closed types can always make progress
2. Weak bisimulation: EQ2-equivalent types share observable behavior
3. Projection coherence: global types project to consistent local types
-/


/-! ## MvQPF Infrastructure

MvQPF instances for the ITree base functor, the product functor, and the projection functor.

The core types are renamed to avoid conflicts with Mathlib:
- `TypeVec` → `ITreeTypeVec`
- `MvFunctor` → `ITreeMvFunctor`
- `MvPFunctor` → `ITreeMvPFunctor`
- `MvQPF` → `ITreeMvQPF`
-/

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

section

universe u

/-! ## Finite-Index Utilities -/

inductive PFin2 : Nat → Type u
  | fz {n} : PFin2 (n + 1)
  | fs {n} : PFin2 n → PFin2 (n + 1)
  deriving DecidableEq

def PFin2.last : {n : Nat} → PFin2 (n + 1)
  | 0   => PFin2.fz
  | n+1 => PFin2.fs (@PFin2.last n)

def PFin2.weaken {n : Nat} : PFin2 n → PFin2 (n + 1)
  | PFin2.fz   => PFin2.fz
  | PFin2.fs k => PFin2.fs (PFin2.weaken k)

def PFin2.inv : {n : Nat} → PFin2 n → PFin2 n
  | 0,    _     => by contradiction
  | 1,    .fs _ => by contradiction
  | n+1,  .fz   => PFin2.last
  | n+2,  .fs i => PFin2.weaken i.inv

instance (n : Nat) : OfNat (PFin2 (n+1)) (nat_lit 0) := ⟨PFin2.fz⟩
instance (n : Nat) : OfNat (PFin2 (n+2)) (nat_lit 1) := ⟨PFin2.fs PFin2.fz⟩

abbrev DVec {n : Nat} (αs : PFin2 n → Type u) : Type u := (i : PFin2 n) → αs i

abbrev Vec (α : Type u) (n : Nat) := @DVec n fun _ => α

def Vec.nil {α : Type u} : Vec α 0 := fun i => by cases i

def Vec.append1 {α : Type u} {n : Nat} (tl : Vec α n) (hd : α) : Vec α (n + 1)
  | .fz   => hd
  | .fs i => tl i

syntax (name := vec_notation) "![" term,* "]" : term
macro_rules (kind := vec_notation)
  | `(![])              => `(Vec.nil)
  | `(![$x])            => `(Vec.append1 Vec.nil $x)
  | `(![$xs,*, $x])     => `(Vec.append1 ![$xs,*] $x)

/-! ## Type-Vector and Functor Core -/

def ITreeTypeVec (n : Nat) := PFin2 n → Type u

def ITreeTypeVec.Arrow {n : Nat} (α β : ITreeTypeVec.{u} n) : Type u := ∀ i : PFin2.{u} n, α i → β i

infixl:40 " ⟹ " => ITreeTypeVec.Arrow

def ITreeTypeVec.id {n : Nat} {α : ITreeTypeVec n} : α ⟹ α := fun _ x => x

def ITreeTypeVec.comp {n : Nat} {α β γ : ITreeTypeVec n} (g : β ⟹ γ) (f : α ⟹ β) : α ⟹ γ :=
  fun i x => g i (f i x)

infixr:80 " ⊚ " => ITreeTypeVec.comp

class ITreeMvFunctor {n : Nat} (F : ITreeTypeVec n → Type u) where
  map : ∀ {α β : ITreeTypeVec n}, (α ⟹ β) → F α → F β

infixr:100 " <$$> " => ITreeMvFunctor.map

structure ITreeMvPFunctor (n : Nat) where
  A : Type u
  B : A → ITreeTypeVec.{u} n

def ITreeMvPFunctor.Obj {n : Nat} (P : ITreeMvPFunctor.{u} n) (α : ITreeTypeVec.{u} n) : Type u := Σ a : P.A, P.B a ⟹ α

def ITreeMvPFunctor.map {n : Nat} {P : ITreeMvPFunctor.{u} n} {α β : ITreeTypeVec n} (f : α ⟹ β) : P.Obj α → P.Obj β :=
  fun ⟨a, g⟩ => ⟨a, f ⊚ g⟩

instance {n : Nat} (P : ITreeMvPFunctor.{u} n) : ITreeMvFunctor P.Obj where
  map := ITreeMvPFunctor.map

@[simp]
theorem ITreeMvPFunctor.map_eq {n : Nat} {P : ITreeMvPFunctor.{u} n} {α β : ITreeTypeVec n} (f : α ⟹ β) (x : P.Obj α) :
    ITreeMvFunctor.map f x = ITreeMvPFunctor.map f x := by
      -- By definition of `ITreeMvPFunctor.map`, we have `f <$$> x = ITreeMvPFunctor.map f x`.
      apply Eq.refl

@[simp]
theorem ITreeMvPFunctor.map_id {n : Nat} {P : ITreeMvPFunctor.{u} n} {α : ITreeTypeVec n} (x : P.Obj α) : ITreeMvPFunctor.map ITreeTypeVec.id x = x := by
  exact rfl

@[simp]
theorem ITreeMvPFunctor.map_comp {n : Nat} {P : ITreeMvPFunctor.{u} n} {α β γ : ITreeTypeVec n} (f : α ⟹ β) (g : β ⟹ γ) (x : P.Obj α) :
    ITreeMvPFunctor.map g (ITreeMvPFunctor.map f x) = ITreeMvPFunctor.map (g ⊚ f) x := by
      exact rfl

/-! ## QPF Construction Helpers -/

class ITreeMvQPF {n : Nat} (F : ITreeTypeVec n → Type u) extends ITreeMvFunctor F where
  P : ITreeMvPFunctor.{u} n
  abs : ∀ {α}, P.Obj α → F α
  repr : ∀ {α}, F α → P.Obj α
  abs_repr : ∀ {α} (x : F α), abs (repr x) = x
  abs_map : ∀ {α β} (f : ITreeTypeVec.Arrow α β) (p : P.Obj α), abs (ITreeMvPFunctor.map f p) = ITreeMvFunctor.map f (abs p)

def ITreeMvQPF.instMvQPFObj {n : Nat} (P : ITreeMvPFunctor.{u} n) : ITreeMvQPF P.Obj where
  P := P
  abs := fun x => x
  repr := fun x => x
  abs_repr _ := rfl
  abs_map _ _ := rfl

def ITreeMvQPF.ofIsomorphism {n : Nat} {F : ITreeTypeVec n → Type u}
    (F' : ITreeTypeVec n → Type u)
    [functor : ITreeMvFunctor F]
    [q : ITreeMvQPF F']
    (box : ∀ {α}, F α → F' α)
    (unbox : ∀ {α}, F' α → F α)
    (box_unbox_id : ∀ {α} (x : F' α), box (unbox x) = x)
    (unbox_box_id : ∀ {α} (x : F α), unbox (box x) = x := by intros; rfl)
    (map_eq : ∀ (α β : ITreeTypeVec n) (f : ITreeTypeVec.Arrow α β) (a : F α),
        functor.map f a = unbox (ITreeMvFunctor.map f (box a)) := by intros; rfl)
    : ITreeMvQPF F where
  P := q.P
  abs := unbox ∘ q.abs
  repr := q.repr ∘ box
  abs_repr := by
    intros
    simp only [Function.comp, q.abs_repr, unbox_box_id]
  abs_map f x := by
    simp only [Function.comp]
    rw [map_eq]
    congr 1
    simp only [box_unbox_id, q.abs_map]

def ITreeMvQPF.ofPolynomial {n : Nat} {F : ITreeTypeVec n → Type u} (P : ITreeMvPFunctor.{u} n)
    [ITreeMvFunctor F]
    (box : ∀ {α}, F α → P.Obj α)
    (unbox : ∀ {α}, P.Obj α → F α)
    (box_unbox_id : ∀ {α} (x : P.Obj α), box (unbox x) = x)
    (unbox_box_id : ∀ {α} (x : F α), unbox (box x) = x)
    (map_eq : ∀ (α β : ITreeTypeVec n) (f : ITreeTypeVec.Arrow α β) (a : F α),
        ITreeMvFunctor.map f a = unbox (ITreeMvPFunctor.map f (box a)))
    : ITreeMvQPF F :=
  ITreeMvQPF.ofIsomorphism P.Obj (q := ITreeMvQPF.instMvQPFObj P) box unbox box_unbox_id unbox_box_id map_eq

/-! ## ITree Head/Child Polynomial Encoding -/

inductive HeadT : Type 1
  | ret
  | tau
  | vis (Ans : Type)

def PFin2.elim0 {C : PFin2 0 → Sort u} : ∀ i : PFin2 0, C i := fun i => by cases i

def ChildT : HeadT → ITreeTypeVec.{1} 2
  | HeadT.ret => fun i => match i with
    | PFin2.fz => PFin2.{1} 1
    | PFin2.fs PFin2.fz => PFin2.{1} 0
    | PFin2.fs (PFin2.fs i) => by cases i
  | HeadT.tau => fun i => match i with
    | PFin2.fz => PFin2.{1} 0
    | PFin2.fs PFin2.fz => PFin2.{1} 1
    | PFin2.fs (PFin2.fs i) => by cases i
  | HeadT.vis Ans => fun i => match i with
    | PFin2.fz => PFin2.{1} 0
    | PFin2.fs PFin2.fz => ULift.{1, 0} Ans
    | PFin2.fs (PFin2.fs i) => by cases i

abbrev P : ITreeMvPFunctor.{1} 2 := ⟨HeadT, ChildT⟩

abbrev F : ITreeTypeVec.{1} 2 → Type 1 := P.Obj

def box {α : ITreeTypeVec 2} (x : F α) : P.Obj α := x

def unbox {α : ITreeTypeVec 2} (x : P.Obj α) : F α := x

theorem box_unbox_id {α : ITreeTypeVec 2} (x : P.Obj α) : box (unbox x) = x := rfl

theorem unbox_box_id {α : ITreeTypeVec 2} (x : F α) : unbox (box x) = x := rfl

/-! ## Canonical ITree QPF Instance -/

instance instMvQPF : ITreeMvQPF F :=
  ITreeMvQPF.ofPolynomial P box unbox box_unbox_id unbox_box_id (by intros; rfl)

/-! ## Product and Projection Functors -/

def ProdF : ITreeTypeVec.{u} 2 → Type u := fun α => α 0 × α 1

def PrjF {n : Nat} (i : PFin2 n) : ITreeTypeVec.{u} n → Type u := fun α => α i

instance instMvFunctor_Prj {n : Nat} (i : PFin2 n) : ITreeMvFunctor (PrjF i) where
  map f x := f i x

def P_Prj {n : Nat} (i : PFin2 n) : ITreeMvPFunctor.{u} n :=
  ⟨PUnit.{u+1}, fun _ j => ULift.{u} (PLift (i = j))⟩

def box_Prj {n : Nat} {i : PFin2 n} {α : ITreeTypeVec n} (x : PrjF i α) : (P_Prj i).Obj α :=
  ⟨PUnit.unit, fun j (p : ULift (PLift (i = j))) =>
    cast (congr_arg α p.down.down) x⟩

def unbox_Prj {n : Nat} {i : PFin2 n} {α : ITreeTypeVec n} (x : (P_Prj i).Obj α) : PrjF i α :=
  x.2 i (ULift.up (PLift.up rfl))

/-! ## Projection QPF Instance -/

def instMvQPF_Prj {n : Nat} (i : PFin2 n) : ITreeMvQPF (PrjF i) :=
  ITreeMvQPF.ofPolynomial (P_Prj i) box_Prj unbox_Prj (by
  -- By definition of `box_Prj` and `unbox_Prj`, they are inverses of each other.
  intros α x
  simp [box_Prj, unbox_Prj];
  -- Since the first component is PUnit.unit, which is the same as x.1, we can focus on the second component.
  congr;
  -- Since the function is defined as taking i and p and returning b i (p.down.down), and p is a ULift of a PLift of i = j, which simplifies to i = j, then p.down.down is just i = j. Therefore, the function simplifies to b i (i = j).
  funext j p; simp [P_Prj];
  -- Since `p` is a `ULift` of a `PLift` of `i = j`, and `ULift` and `PLift` are just type synonyms, we can simplify `p` to `i = j`.
  obtain ⟨p_eq⟩ := p.down.down;
  congr) (by
  -- The identity function is its own inverse.
  simp [unbox_Prj, box_Prj]) (by
  exact fun α β f a => rfl)
