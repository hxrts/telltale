import Mathlib.Data.List.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic
import SessionTypes.GlobalType

set_option linter.unusedSimpArgs false

/-
The Problem. Named variable representations require complex variable capture avoidance
during substitution. De Bruijn indices eliminate this by encoding binding depth numerically,
making substitution purely structural but requiring lifting operations.

Solution Structure. Defines `LocalTypeDB` with natural number indices where `mu` binds index 0.
Provides `lift` to shift indices above a cutoff and `subst` for capture-avoiding substitution.
`unfold` substitutes a mu into its body. Closedness (`isClosedAt`), guardedness (`isGuarded`),
and contractiveness (`isContractive`) predicates enable well-formedness reasoning.
-/

/-! # SessionTypes.LocalTypeDB

De Bruijn indexed local types for clean substitution proofs.

This module provides a de Bruijn representation of local types where:
- Variables are natural numbers (de Bruijn indices)
- `mu` binds index 0 in its body
- Substitution and lifting follow standard de Bruijn conventions

The key advantage: guardedness and contractiveness proofs are simpler
because bound variables are structurally separate from free variables.
-/

namespace SessionTypes

open SessionTypes.GlobalType

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

/-! ## Lift/Subst Interaction Laws -/

/-! ## Lift/Subst Cancellation at Depth k+1 -/

private theorem lift_subst_cancel_at_depth_any (e : LocalTypeDB) (k : Nat) (s : LocalTypeDB) :
    (e.lift 1 (k + 1)).subst (k + 1) s = e := by
  let P1 : LocalTypeDB → Prop :=
    fun e => ∀ k s, (e.lift 1 (k + 1)).subst (k + 1) s = e
  let P2 : List (Label × LocalTypeDB) → Prop :=
    fun bs => ∀ k s, substBranches (liftBranches 1 (k + 1) bs) (k + 1) s = bs
  let P3 : Label × LocalTypeDB → Prop :=
    fun b => P1 b.2
  have hrec : P1 e := by
    refine (LocalTypeDB.rec (motive_1 := P1) (motive_2 := P2) (motive_3 := P3)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ e)
    -- end case
    · intro k s
      simp [LocalTypeDB.lift, LocalTypeDB.subst]
    -- var case
    · intro n k s
      by_cases hlt : n < k + 1
      · have hne : n ≠ k + 1 := by omega
        have hgt : ¬ n > k + 1 := by omega
        simp [LocalTypeDB.lift, LocalTypeDB.subst, hlt, hne, hgt]
      · have hge : k + 1 ≤ n := by omega
        have hgt : n + 1 > k + 1 := by omega
        have hne : n + 1 ≠ k + 1 := by omega
        have hne' : n ≠ k := by omega
        simp only [LocalTypeDB.lift, LocalTypeDB.subst, hlt, hgt, hne, ite_false, ite_true]
        simp only [Nat.add_sub_cancel]
    -- send case
    · intro p bs hbs k s
      simp [LocalTypeDB.lift, LocalTypeDB.subst]
      exact hbs k s
    -- recv case
    · intro p bs hbs k s
      simp [LocalTypeDB.lift, LocalTypeDB.subst]
      exact hbs k s
    -- mu case
    · intro body hbody k s
      simp [LocalTypeDB.lift, LocalTypeDB.subst]
      exact hbody (k + 1) (s.lift 1 0)
    -- nil case
    · intro k s
      simp [liftBranches, substBranches]
    -- cons case
    · intro head tail hhead htail k s
      obtain ⟨l, t⟩ := head
      simp [liftBranches, substBranches, hhead k s, htail k s]
    -- pair case
    · intro l t ht
      exact ht
  exact hrec k s

/-! ## Branch Lift/Subst Cancellation -/

private theorem liftBranches_substBranches_cancel_at_depth_any
    (bs : List (Label × LocalTypeDB)) (k : Nat) (s : LocalTypeDB) :
    substBranches (liftBranches 1 (k + 1) bs) (k + 1) s = bs := by
  induction bs with
  | nil => simp [liftBranches, substBranches]
  | cons head rest ih =>
      obtain ⟨l, t⟩ := head
      simp [liftBranches, substBranches, lift_subst_cancel_at_depth_any, ih]

/-! ## Lift/Subst Cancellation at Depth 0 -/

/-- Lifting then substituting at depth 0 is identity: `(e.lift 1 0).subst 0 t = e`. -/
theorem lift_subst_cancel (e : LocalTypeDB) (t : LocalTypeDB) :
    (e.lift 1 0).subst 0 t = e := by
  let P1 : LocalTypeDB → Prop :=
    fun e => ∀ t, (e.lift 1 0).subst 0 t = e
  let P2 : List (Label × LocalTypeDB) → Prop :=
    fun bs => ∀ t, substBranches (liftBranches 1 0 bs) 0 t = bs
  let P3 : Label × LocalTypeDB → Prop :=
    fun b => P1 b.2
  have hrec : P1 e := by
    refine (LocalTypeDB.rec (motive_1 := P1) (motive_2 := P2) (motive_3 := P3)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ e)
    -- end case
    · intro t
      simp [LocalTypeDB.lift, LocalTypeDB.subst]
    -- var case
    · intro n t
      have hgt : n + 1 > 0 := Nat.succ_pos n
      simp [LocalTypeDB.lift, LocalTypeDB.subst, hgt]
    -- send case
    · intro p bs hbs t
      simp [LocalTypeDB.lift, LocalTypeDB.subst, hbs t]
    -- recv case
    · intro p bs hbs t
      simp [LocalTypeDB.lift, LocalTypeDB.subst, hbs t]
    -- mu case
    · intro body hbody t
      simp [LocalTypeDB.lift, LocalTypeDB.subst]
      exact lift_subst_cancel_at_depth_any body 0 (t.lift 1 0)
    -- nil case
    · intro t
      simp [liftBranches, substBranches]
    -- cons case
    · intro head tail hhead htail t
      obtain ⟨l, t'⟩ := head
      simp [liftBranches, substBranches, hhead t, htail t]
    -- pair case
    · intro l t ht
      exact ht
  exact hrec t

theorem lift_subst_cancel_at_depth (e : LocalTypeDB) (k : Nat) (t : LocalTypeDB) :
  (e.lift 1 (k + 1)).subst (k + 1) (t.lift 1 k) = e := by
  exact lift_subst_cancel_at_depth_any e k (t.lift 1 k)

theorem liftBranches_substBranches_cancel
  (bs : List (Label × LocalTypeDB)) (t : LocalTypeDB) :
  substBranches (liftBranches 1 0 bs) 0 t = bs := by
  induction bs with
  | nil =>
      simp [liftBranches, substBranches]
  | cons head rest ih =>
      cases head with
      | mk l t' =>
          simp [liftBranches, substBranches, lift_subst_cancel, ih]

theorem liftBranches_substBranches_cancel_at_depth
  (bs : List (Label × LocalTypeDB)) (k : Nat) (t : LocalTypeDB) :
  substBranches (liftBranches 1 (k + 1) bs) (k + 1) (t.lift 1 k) = bs := by
  exact liftBranches_substBranches_cancel_at_depth_any bs k (t.lift 1 k)

end SessionTypes
