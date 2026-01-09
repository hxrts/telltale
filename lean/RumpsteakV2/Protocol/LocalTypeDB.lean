import Mathlib.Data.List.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic
import RumpsteakV2.Protocol.GlobalType

/-! # RumpsteakV2.Protocol.LocalTypeDB

De Bruijn indexed local types for cleaner substitution proofs.

This module provides a de Bruijn representation of local types where:
- Variables are natural numbers (de Bruijn indices)
- `mu` binds index 0 in its body
- Substitution and lifting follow standard de Bruijn conventions

The key advantage: guardedness and contractiveness proofs are simpler
because bound variables are structurally separate from free variables.
-/

namespace RumpsteakV2.Protocol

open RumpsteakV2.Protocol.GlobalType

/-- De Bruijn indexed local types.
    Variables are represented as natural numbers (de Bruijn indices).
    `mu` binds index 0 in its body. -/
inductive LocalTypeDB where
  | end : LocalTypeDB
  | var : Nat → LocalTypeDB
  | send : String → List (Label × LocalTypeDB) → LocalTypeDB
  | recv : String → List (Label × LocalTypeDB) → LocalTypeDB
  | mu : LocalTypeDB → LocalTypeDB
  deriving Repr, Inhabited

/-! ## Core Operations -/

mutual
  /-- Lift free variables by `c` at cutoff `k`. -/
  def LocalTypeDB.lift : Nat → Nat → LocalTypeDB → LocalTypeDB
    | _, _, .end => .end
    | c, k, .var n =>
        if n < k then .var n else .var (n + c)
    | c, k, .send p bs => .send p (liftBranches c k bs)
    | c, k, .recv p bs => .recv p (liftBranches c k bs)
    | c, k, .mu body => .mu (body.lift c (k + 1))

  /-- Lift over branches. -/
  def liftBranches : Nat → Nat → List (Label × LocalTypeDB) → List (Label × LocalTypeDB)
    | _, _, [] => []
    | c, k, (l, t) :: rest => (l, t.lift c k) :: liftBranches c k rest
end

/-! ## Substitution -/

mutual
  /-- Substitute term `e` for index `k` (removing the binder at `k`). -/
  def LocalTypeDB.subst : LocalTypeDB → Nat → LocalTypeDB → LocalTypeDB
    | .end, _, _ => .end
    | .var n, k, e =>
        if n = k then e
        else if n > k then .var (n - 1) else .var n
    | .send p bs, k, e => .send p (substBranches bs k e)
    | .recv p bs, k, e => .recv p (substBranches bs k e)
    | .mu body, k, e => .mu (body.subst (k + 1) (e.lift 1 0))

  /-- Substitute over branches. -/
  def substBranches : List (Label × LocalTypeDB) → Nat → LocalTypeDB → List (Label × LocalTypeDB)
    | [], _, _ => []
    | (l, t) :: rest, k, e => (l, t.subst k e) :: substBranches rest k e
end

/-- Unfold one level of recursion: μT ↦ T[μT/0]. -/
def LocalTypeDB.unfold : LocalTypeDB → LocalTypeDB
  | lt@(.mu body) => body.subst 0 lt
  | lt => lt

/-- Height for mu unfolding - counts nested mus at the head. -/
def LocalTypeDB.muHeight : LocalTypeDB → Nat
  | .mu body => 1 + body.muHeight
  | _ => 0

/-- Fully unfold a local type by iterating unfold until non-mu form. -/
def LocalTypeDB.fullUnfold (lt : LocalTypeDB) : LocalTypeDB :=
  (LocalTypeDB.unfold)^[lt.muHeight] lt

/-! ## Closedness -/

mutual
  /-- A term is closed at depth `k` if all variables are < k. -/
  def LocalTypeDB.isClosedAt : Nat → LocalTypeDB → Bool
    | _, .end => true
    | k, .var n => n < k
    | k, .send _ bs => isClosedAtBranches k bs
    | k, .recv _ bs => isClosedAtBranches k bs
    | k, .mu body => body.isClosedAt (k + 1)

  def isClosedAtBranches : Nat → List (Label × LocalTypeDB) → Bool
    | _, [] => true
    | k, (_, t) :: rest => t.isClosedAt k && isClosedAtBranches k rest
end

/-- A term is closed if it is closed at depth 0. -/
def LocalTypeDB.isClosed (t : LocalTypeDB) : Bool := t.isClosedAt 0

/-! ## Guardedness / Contractiveness -/

mutual
  /-- A variable index `i` is guarded if it never appears at the head. -/
  def LocalTypeDB.isGuarded : Nat → LocalTypeDB → Bool
    | _, .end => true
    | i, .var n => n != i
    | _, .send _ _ => true
    | _, .recv _ _ => true
    | i, .mu body => body.isGuarded (i + 1)

  def isGuardedBranches : Nat → List (Label × LocalTypeDB) → Bool
    | _, [] => true
    | i, (_, t) :: rest => t.isGuarded i && isGuardedBranches i rest
end

mutual
  /-- A term is contractive if every `mu` binder guards its bound variable. -/
  def LocalTypeDB.isContractive : LocalTypeDB → Bool
    | .end => true
    | .var _ => true
    | .send _ bs => isContractiveBranches bs
    | .recv _ bs => isContractiveBranches bs
    | .mu body => body.isGuarded 0 && body.isContractive

  def isContractiveBranches : List (Label × LocalTypeDB) → Bool
    | [] => true
    | (_, c) :: rest => c.isContractive && isContractiveBranches rest
end

/-! ## Lift/Subst Interaction Laws (axioms) -/

axiom lift_subst_cancel (e : LocalTypeDB) (t : LocalTypeDB) :
  (e.lift 1 0).subst 0 t = e

axiom lift_subst_cancel_at_depth (e : LocalTypeDB) (k : Nat) (t : LocalTypeDB) :
  (e.lift 1 (k + 1)).subst (k + 1) (t.lift 1 k) = e

axiom liftBranches_substBranches_cancel
  (bs : List (Label × LocalTypeDB)) (t : LocalTypeDB) :
  substBranches (liftBranches 1 0 bs) 0 t = bs

axiom liftBranches_substBranches_cancel_at_depth
  (bs : List (Label × LocalTypeDB)) (k : Nat) (t : LocalTypeDB) :
  substBranches (liftBranches 1 (k + 1) bs) (k + 1) (t.lift 1 k) = bs

/-! ## Closedness Preservation (axioms) -/

axiom isClosedAt_lift (t : LocalTypeDB) (c k : Nat) :
  t.isClosedAt k = true → (t.lift c k).isClosedAt (k + c) = true

axiom isClosedAt_lift_branches (bs : List (Label × LocalTypeDB)) (c k : Nat) :
  isClosedAtBranches k bs = true →
  isClosedAtBranches (k + c) (liftBranches c k bs) = true

axiom isClosedAt_subst (t e : LocalTypeDB) (k : Nat) :
  t.isClosedAt (k + 1) = true → e.isClosedAt k = true →
  (t.subst k e).isClosedAt k = true

axiom isClosedAt_subst_branches (bs : List (Label × LocalTypeDB)) (e : LocalTypeDB) (k : Nat) :
  isClosedAtBranches (k + 1) bs = true → e.isClosedAt k = true →
  isClosedAtBranches k (substBranches bs k e) = true

/-! ## Contractiveness Preservation (axioms) -/

axiom isContractive_subst (body e : LocalTypeDB) (k : Nat) :
  body.isContractive = true → e.isContractive = true →
  (body.subst k e).isContractive = true

axiom isContractive_subst_branches (bs : List (Label × LocalTypeDB)) (e : LocalTypeDB) (k : Nat) :
  isContractiveBranches bs = true → e.isContractive = true →
  isContractiveBranches (substBranches bs k e) = true

axiom isContractive_subst_mu (body : LocalTypeDB) :
  body.isContractive = true → (LocalTypeDB.mu body).isContractive = true →
  (body.subst 0 (LocalTypeDB.mu body)).isContractive = true

axiom isContractive_unfold (t : LocalTypeDB) :
  t.isContractive = true → t.unfold.isContractive = true

axiom isContractive_iter_unfold (k : Nat) (t : LocalTypeDB) :
  t.isContractive = true → ((LocalTypeDB.unfold)^[k] t).isContractive = true

axiom isContractive_fullUnfold (t : LocalTypeDB) :
  t.isContractive = true → t.fullUnfold.isContractive = true

end RumpsteakV2.Protocol
