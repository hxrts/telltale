import Mathlib.Data.List.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic
import RumpsteakV2.Protocol.GlobalType

set_option linter.unusedSimpArgs false

/-! # RumpsteakV2.Protocol.LocalTypeDB

De Bruijn indexed local types for clean substitution proofs.

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

/-! ## Lift/Subst Interaction Laws -/

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

private theorem liftBranches_substBranches_cancel_at_depth_any
    (bs : List (Label × LocalTypeDB)) (k : Nat) (s : LocalTypeDB) :
    substBranches (liftBranches 1 (k + 1) bs) (k + 1) s = bs := by
  induction bs with
  | nil => simp [liftBranches, substBranches]
  | cons head rest ih =>
      obtain ⟨l, t⟩ := head
      simp [liftBranches, substBranches, lift_subst_cancel_at_depth_any, ih]

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

/-! ## Closedness Preservation -/

private theorem isClosedAt_lift_at (t : LocalTypeDB) (c k d : Nat) :
    t.isClosedAt d = true → (t.lift c k).isClosedAt (d + c) = true := by
  intro h
  let P1 : LocalTypeDB → Prop :=
    fun t => ∀ c k d, t.isClosedAt d = true → (t.lift c k).isClosedAt (d + c) = true
  let P2 : List (Label × LocalTypeDB) → Prop :=
    fun bs => ∀ c k d, isClosedAtBranches d bs = true →
      isClosedAtBranches (d + c) (liftBranches c k bs) = true
  let P3 : Label × LocalTypeDB → Prop :=
    fun b => P1 b.2
  have hrec : P1 t := by
    refine (LocalTypeDB.rec (motive_1 := P1) (motive_2 := P2) (motive_3 := P3)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ t)
    -- end case
    · intro c k d h
      simp [LocalTypeDB.isClosedAt, LocalTypeDB.lift] at *
    -- var case
    · intro n c k d h
      simp only [LocalTypeDB.isClosedAt, decide_eq_true_eq] at h
      simp only [LocalTypeDB.lift]
      by_cases hnk : n < k
      · simp only [hnk, ite_true, LocalTypeDB.isClosedAt, decide_eq_true_eq]
        exact Nat.lt_of_lt_of_le h (Nat.le_add_right d c)
      · simp only [hnk, ite_false, LocalTypeDB.isClosedAt, decide_eq_true_eq]
        exact Nat.add_lt_add_right h c
    -- send case
    · intro p bs hbs c k d h
      simp only [LocalTypeDB.isClosedAt, LocalTypeDB.lift] at h ⊢
      exact hbs c k d h
    -- recv case
    · intro p bs hbs c k d h
      simp only [LocalTypeDB.isClosedAt, LocalTypeDB.lift] at h ⊢
      exact hbs c k d h
    -- mu case
    · intro body hbody c k d h
      simp only [LocalTypeDB.isClosedAt, LocalTypeDB.lift] at h ⊢
      have heq : d + c + 1 = d + 1 + c := by omega
      rw [heq]
      exact hbody c (k + 1) (d + 1) h
    -- nil case
    · intro c k d h
      simp [isClosedAtBranches, liftBranches] at h ⊢
    -- cons case
    · intro head tail hhead htail c k d h
      obtain ⟨l, t⟩ := head
      simp [isClosedAtBranches, liftBranches, Bool.and_eq_true] at h ⊢
      rcases h with ⟨ht, hrest⟩
      constructor
      · exact hhead c k d ht
      · exact htail c k d hrest
    -- pair case
    · intro l t ht
      exact ht
  exact hrec c k d h

private theorem isClosedAt_lift_at_branches (bs : List (Label × LocalTypeDB)) (c k d : Nat) :
    isClosedAtBranches d bs = true →
    isClosedAtBranches (d + c) (liftBranches c k bs) = true := by
  intro h
  induction bs with
  | nil => simp [isClosedAtBranches, liftBranches] at h ⊢
  | cons head rest ih =>
      obtain ⟨l, t⟩ := head
      simp [isClosedAtBranches, liftBranches, Bool.and_eq_true] at h ⊢
      rcases h with ⟨ht, hrest⟩
      constructor
      · exact isClosedAt_lift_at t c k d ht
      · exact ih hrest

/-- Lifting preserves closedness: if `t` is closed at `k`, then `t.lift c k` is closed at `k + c`. -/
theorem isClosedAt_lift (t : LocalTypeDB) (c k : Nat) :
  t.isClosedAt k = true → (t.lift c k).isClosedAt (k + c) = true := by
  intro h
  exact isClosedAt_lift_at t c k k h

theorem isClosedAt_lift_branches (bs : List (Label × LocalTypeDB)) (c k : Nat) :
  isClosedAtBranches k bs = true →
  isClosedAtBranches (k + c) (liftBranches c k bs) = true := by
  intro h
  exact isClosedAt_lift_at_branches bs c k k h

/-- Substitution preserves closedness: if `t` is closed at `k+1` and `e` is closed at `k`,
    then `t.subst k e` is closed at `k`. -/
theorem isClosedAt_subst (t e : LocalTypeDB) (k : Nat) :
    t.isClosedAt (k + 1) = true → e.isClosedAt k = true →
    (t.subst k e).isClosedAt k = true := by
  intro ht he
  let P1 : LocalTypeDB → Prop :=
    fun t => ∀ e k, t.isClosedAt (k + 1) = true → e.isClosedAt k = true →
      (t.subst k e).isClosedAt k = true
  let P2 : List (Label × LocalTypeDB) → Prop :=
    fun bs => ∀ e k, isClosedAtBranches (k + 1) bs = true → e.isClosedAt k = true →
      isClosedAtBranches k (substBranches bs k e) = true
  let P3 : Label × LocalTypeDB → Prop :=
    fun b => P1 b.2
  have hrec : P1 t := by
    refine (LocalTypeDB.rec (motive_1 := P1) (motive_2 := P2) (motive_3 := P3)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ t)
    -- end case
    · intro e k ht he
      simp [LocalTypeDB.subst, LocalTypeDB.isClosedAt] at *
    -- var case
    · intro n e k ht he
      simp [LocalTypeDB.isClosedAt] at ht
      by_cases hnk : n = k
      · simp [LocalTypeDB.subst, LocalTypeDB.isClosedAt, hnk, he]
      · by_cases hgt : n > k
        · have hge : k + 1 ≤ n := Nat.succ_le_of_lt hgt
          have hcontra : False := (Nat.not_lt_of_ge hge) ht
          exact (False.elim hcontra)
        · have hle : n ≤ k := Nat.le_of_not_gt hgt
          have hlt : n < k := Nat.lt_of_le_of_ne hle hnk
          simp [LocalTypeDB.subst, LocalTypeDB.isClosedAt, hnk, hgt, hlt]
    -- send case
    · intro p bs hbs e k ht he
      simp [LocalTypeDB.subst, LocalTypeDB.isClosedAt] at ht ⊢
      exact hbs e k ht he
    -- recv case
    · intro p bs hbs e k ht he
      simp [LocalTypeDB.subst, LocalTypeDB.isClosedAt] at ht ⊢
      exact hbs e k ht he
    -- mu case
    · intro body hbody e k ht he
      simp [LocalTypeDB.subst, LocalTypeDB.isClosedAt] at ht ⊢
      have h_lift : (e.lift 1 0).isClosedAt (k + 1) = true :=
        isClosedAt_lift_at e 1 0 k he
      exact hbody (e.lift 1 0) (k + 1) ht h_lift
    -- nil case
    · intro e k hbs he
      simp [isClosedAtBranches, substBranches] at hbs ⊢
    -- cons case
    · intro head tail hhead htail e k hbs he
      obtain ⟨l, t⟩ := head
      simp [isClosedAtBranches, substBranches, Bool.and_eq_true] at hbs ⊢
      rcases hbs with ⟨ht, hrest⟩
      constructor
      · exact hhead e k ht he
      · exact htail e k hrest he
    -- pair case
    · intro l t ht
      exact ht
  exact hrec e k ht he

theorem isClosedAt_subst_branches (bs : List (Label × LocalTypeDB)) (e : LocalTypeDB) (k : Nat) :
    isClosedAtBranches (k + 1) bs = true → e.isClosedAt k = true →
    isClosedAtBranches k (substBranches bs k e) = true := by
  intro hbs he
  induction bs with
  | nil => simp [isClosedAtBranches, substBranches] at hbs ⊢
  | cons head rest ih =>
      obtain ⟨l, t⟩ := head
      simp [isClosedAtBranches, substBranches, Bool.and_eq_true] at hbs ⊢
      rcases hbs with ⟨ht, hrest⟩
      constructor
      · exact isClosedAt_subst t e k ht he
      · exact ih hrest

/-! ## Contractiveness Preservation -/

/-- Guardedness is preserved by lifting when the index is below the cutoff. -/
theorem isGuarded_lift_lt (t : LocalTypeDB) (i c k : Nat) :
    i < k → t.isGuarded i = true → (t.lift c k).isGuarded i = true := by
  intro hik hguard
  let P1 : LocalTypeDB → Prop :=
    fun t => ∀ i c k, i < k → t.isGuarded i = true → (t.lift c k).isGuarded i = true
  let P2 : List (Label × LocalTypeDB) → Prop := fun _ => True
  let P3 : Label × LocalTypeDB → Prop := fun b => P1 b.2
  have hrec : P1 t := by
    refine (LocalTypeDB.rec (motive_1 := P1) (motive_2 := P2) (motive_3 := P3)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ t)
    -- end case
    · intro i c k hik hguard
      simp [LocalTypeDB.isGuarded, LocalTypeDB.lift] at *
    -- var case
    · intro n i c k hik hguard
      by_cases hnk : n < k
      · simpa [LocalTypeDB.isGuarded, LocalTypeDB.lift, hnk] using hguard
      · have hle : k ≤ n := Nat.le_of_not_lt hnk
        have hlt : i < n + c := by
          have hin : i < n := lt_of_lt_of_le hik hle
          exact lt_of_lt_of_le hin (Nat.le_add_right _ _)
        have hne : n + c ≠ i := ne_of_gt hlt
        have hbne : (n + c != i) = true := (bne_iff_ne).2 hne
        simpa [LocalTypeDB.isGuarded, LocalTypeDB.lift, hnk] using hbne
    -- send case
    · intro p bs _ i c k hik hguard
      simp [LocalTypeDB.isGuarded, LocalTypeDB.lift]
    -- recv case
    · intro p bs _ i c k hik hguard
      simp [LocalTypeDB.isGuarded, LocalTypeDB.lift]
    -- mu case
    · intro body hbody i c k hik hguard
      simp [LocalTypeDB.isGuarded, LocalTypeDB.lift] at hguard ⊢
      exact hbody (i + 1) c (k + 1) (Nat.succ_lt_succ hik) hguard
    -- nil case
    · trivial
    -- cons case
    · intro _ _ _ _; trivial
    -- pair case
    · intro l t ht
      exact ht
  exact hrec i c k hik hguard

/-- Guardedness is preserved by lifting when the index is at or above the cutoff (shifted). -/
theorem isGuarded_lift_ge (t : LocalTypeDB) (i c k : Nat) :
    k ≤ i → t.isGuarded i = true → (t.lift c k).isGuarded (i + c) = true := by
  intro hik hguard
  let P1 : LocalTypeDB → Prop :=
    fun t => ∀ i c k, k ≤ i → t.isGuarded i = true → (t.lift c k).isGuarded (i + c) = true
  let P2 : List (Label × LocalTypeDB) → Prop := fun _ => True
  let P3 : Label × LocalTypeDB → Prop := fun b => P1 b.2
  have hrec : P1 t := by
    refine (LocalTypeDB.rec (motive_1 := P1) (motive_2 := P2) (motive_3 := P3)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ t)
    -- end case
    · intro i c k hik hguard
      simp [LocalTypeDB.isGuarded, LocalTypeDB.lift] at *
    -- var case
    · intro n i c k hik hguard
      have hne : n ≠ i := (bne_iff_ne).1 hguard
      by_cases hnk : n < k
      · have hni : n < i := lt_of_lt_of_le hnk hik
        have hlt : n < i + c := lt_of_lt_of_le hni (Nat.le_add_right _ _)
        have hne' : n ≠ i + c := ne_of_lt hlt
        have hbne : (n != i + c) = true := (bne_iff_ne).2 hne'
        simpa [LocalTypeDB.isGuarded, LocalTypeDB.lift, hnk] using hbne
      · have hne' : n + c ≠ i + c := by
          exact fun h => hne (Nat.add_right_cancel h)
        have hbne : (n + c != i + c) = true := (bne_iff_ne).2 hne'
        simpa [LocalTypeDB.isGuarded, LocalTypeDB.lift, hnk] using hbne
    -- send case
    · intro p bs _ i c k hik hguard
      simp [LocalTypeDB.isGuarded, LocalTypeDB.lift]
    -- recv case
    · intro p bs _ i c k hik hguard
      simp [LocalTypeDB.isGuarded, LocalTypeDB.lift]
    -- mu case
    · intro body hbody i c k hik hguard
      simp [LocalTypeDB.isGuarded, LocalTypeDB.lift] at hguard ⊢
      have heq : i + c + 1 = i + 1 + c := by omega
      rw [heq]
      exact hbody (i + 1) c (k + 1) (Nat.succ_le_succ hik) hguard
    -- nil case
    · trivial
    -- cons case
    · intro _ _ _ _; trivial
    -- pair case
    · intro l t ht
      exact ht
  exact hrec i c k hik hguard

/-- After lifting by 1 at cutoff k, index k cannot appear (it's in a gap). -/
theorem isGuarded_lift_at_cutoff (t : LocalTypeDB) (k : Nat) :
    (t.lift 1 k).isGuarded k = true := by
  let P1 : LocalTypeDB → Prop := fun t => ∀ k, (t.lift 1 k).isGuarded k = true
  let P2 : List (Label × LocalTypeDB) → Prop := fun _ => True
  let P3 : Label × LocalTypeDB → Prop := fun b => P1 b.2
  have hrec : P1 t := by
    refine (LocalTypeDB.rec (motive_1 := P1) (motive_2 := P2) (motive_3 := P3)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ t)
    -- end case
    · intro k
      simp [LocalTypeDB.lift, LocalTypeDB.isGuarded]
    -- var case
    · intro n k
      by_cases hnk : n < k
      · -- n stays as n, which is < k, so n ≠ k
        have hne : n ≠ k := Nat.ne_of_lt hnk
        simp [LocalTypeDB.lift, LocalTypeDB.isGuarded, hnk, bne_iff_ne, hne]
      · -- n becomes n + 1, which is > k (since n >= k)
        have hge : k ≤ n := Nat.le_of_not_lt hnk
        have hgt : n + 1 > k := by omega
        have hne : n + 1 ≠ k := Nat.ne_of_gt hgt
        simp [LocalTypeDB.lift, LocalTypeDB.isGuarded, hnk, bne_iff_ne, hne]
    -- send case
    · intro p bs _ k
      simp [LocalTypeDB.lift, LocalTypeDB.isGuarded]
    -- recv case
    · intro p bs _ k
      simp [LocalTypeDB.lift, LocalTypeDB.isGuarded]
    -- mu case
    · intro body hbody k
      simp [LocalTypeDB.lift, LocalTypeDB.isGuarded]
      exact hbody (k + 1)
    -- nil case
    · trivial
    -- cons case
    · intro _ _ _ _; trivial
    -- pair case
    · intro l t ht; exact ht
  exact hrec k

/-- Lifting by 1 at cutoff 0 always guards index 0. -/
theorem isGuarded_lift_zero (t : LocalTypeDB) : (t.lift 1 0).isGuarded 0 = true :=
  isGuarded_lift_at_cutoff t 0

/-- Substitution preserves guardedness when the index is below the substitution point. -/
theorem isGuarded_subst_lt (t e : LocalTypeDB) (i k : Nat) :
    i < k → t.isGuarded i = true → e.isGuarded i = true →
    (t.subst k e).isGuarded i = true := by
  intro hik hguard heguard
  let P1 : LocalTypeDB → Prop :=
    fun t => ∀ e i k, i < k → t.isGuarded i = true → e.isGuarded i = true →
      (t.subst k e).isGuarded i = true
  let P2 : List (Label × LocalTypeDB) → Prop := fun _ => True
  let P3 : Label × LocalTypeDB → Prop := fun b => P1 b.2
  have hrec : P1 t := by
    refine (LocalTypeDB.rec (motive_1 := P1) (motive_2 := P2) (motive_3 := P3)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ t)
    -- end case
    · intro e i k hik hguard heguard
      simp [LocalTypeDB.subst, LocalTypeDB.isGuarded]
    -- var case
    · intro n e i k hik hguard heguard
      by_cases hnk : n = k
      · simpa [LocalTypeDB.subst, LocalTypeDB.isGuarded, hnk] using heguard
      · by_cases hgt : n > k
        · have hle : k ≤ n - 1 := Nat.le_pred_of_lt hgt
          have hlt : i < n - 1 := lt_of_lt_of_le hik hle
          have hne : n - 1 ≠ i := ne_of_gt hlt
          have hbne : (n - 1 != i) = true := (bne_iff_ne).2 hne
          simpa [LocalTypeDB.subst, LocalTypeDB.isGuarded, hnk, hgt] using hbne
        · have hlt : n < k := lt_of_le_of_ne (Nat.le_of_not_gt hgt) hnk
          simpa [LocalTypeDB.subst, LocalTypeDB.isGuarded, hnk, hgt, hlt] using hguard
    -- send case
    · intro p bs _ e i k hik hguard heguard
      simp [LocalTypeDB.subst, LocalTypeDB.isGuarded]
    -- recv case
    · intro p bs _ e i k hik hguard heguard
      simp [LocalTypeDB.subst, LocalTypeDB.isGuarded]
    -- mu case
    · intro body hbody e i k hik hguard heguard
      simp [LocalTypeDB.isGuarded] at hguard
      have hik' : i + 1 < k + 1 := Nat.succ_lt_succ hik
      have heguard' : (e.lift 1 0).isGuarded (i + 1) = true := by
        have hge := isGuarded_lift_ge e i 1 0 (Nat.zero_le i) heguard
        simpa using hge
      have hsub := hbody (e.lift 1 0) (i + 1) (k + 1) hik' hguard heguard'
      simpa [LocalTypeDB.subst, LocalTypeDB.isGuarded] using hsub
    -- nil case
    · trivial
    -- cons case
    · intro _ _ _ _; trivial
    -- pair case
    · intro l t ht; exact ht
  exact hrec e i k hik hguard heguard

private theorem isContractive_lift (t : LocalTypeDB) (c k : Nat) :
    t.isContractive = true → (t.lift c k).isContractive = true := by
  intro h
  let P1 : LocalTypeDB → Prop :=
    fun t => ∀ c k, t.isContractive = true → (t.lift c k).isContractive = true
  let P2 : List (Label × LocalTypeDB) → Prop :=
    fun bs => ∀ c k, isContractiveBranches bs = true → isContractiveBranches (liftBranches c k bs) = true
  let P3 : Label × LocalTypeDB → Prop := fun b => P1 b.2
  have hrec : P1 t := by
    refine (LocalTypeDB.rec (motive_1 := P1) (motive_2 := P2) (motive_3 := P3)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ t)
    -- end case
    · intro c k h
      simp [LocalTypeDB.isContractive, LocalTypeDB.lift] at *
    -- var case
    · intro n c k h
      show (if n < k then LocalTypeDB.var n else LocalTypeDB.var (n + c)).isContractive = true
      split <;> simp [LocalTypeDB.isContractive]
    -- send case
    · intro p bs hbs c k h
      have hbs' : isContractiveBranches bs = true := by
        simpa [LocalTypeDB.isContractive] using h
      have hbs'' := hbs c k hbs'
      simpa [LocalTypeDB.isContractive, LocalTypeDB.lift] using hbs''
    -- recv case
    · intro p bs hbs c k h
      have hbs' : isContractiveBranches bs = true := by
        simpa [LocalTypeDB.isContractive] using h
      have hbs'' := hbs c k hbs'
      simpa [LocalTypeDB.isContractive, LocalTypeDB.lift] using hbs''
    -- mu case
    · intro body hbody c k h
      have hpair : body.isGuarded 0 = true ∧ body.isContractive = true := by
        simpa [LocalTypeDB.isContractive, Bool.and_eq_true] using h
      rcases hpair with ⟨hguard, hcontr⟩
      have hguard' : (body.lift c (k + 1)).isGuarded 0 = true :=
        isGuarded_lift_lt body 0 c (k + 1) (Nat.succ_pos k) hguard
      have hcontr' : (body.lift c (k + 1)).isContractive = true := hbody c (k + 1) hcontr
      simp [LocalTypeDB.isContractive, LocalTypeDB.lift, hguard', hcontr']
    -- nil case
    · intro c k h
      simp [isContractiveBranches, liftBranches] at *
    -- cons case
    · intro head tail hhead htail c k h
      obtain ⟨l, t⟩ := head
      simp [isContractiveBranches, liftBranches, Bool.and_eq_true] at h ⊢
      rcases h with ⟨ht, hrest⟩
      constructor
      · exact hhead c k ht
      · exact htail c k hrest
    -- pair case
    · intro l t ht
      exact ht
  exact hrec c k h

private theorem isContractiveBranches_lift (bs : List (Label × LocalTypeDB)) (c k : Nat) :
    isContractiveBranches bs = true → isContractiveBranches (liftBranches c k bs) = true := by
  intro h
  induction bs with
  | nil => simp [isContractiveBranches, liftBranches] at *
  | cons head rest ih =>
      obtain ⟨l, t⟩ := head
      simp [isContractiveBranches, liftBranches, Bool.and_eq_true] at h ⊢
      rcases h with ⟨ht, hrest⟩
      constructor
      · exact isContractive_lift t c k ht
      · exact ih hrest

/-- Substitution preserves contractiveness. -/
theorem isContractive_subst (body e : LocalTypeDB) (k : Nat) :
    body.isContractive = true → e.isContractive = true →
    (body.subst k e).isContractive = true := by
  intro hbody he
  let P1 : LocalTypeDB → Prop :=
    fun t => ∀ e k, t.isContractive = true → e.isContractive = true →
      (t.subst k e).isContractive = true
  let P2 : List (Label × LocalTypeDB) → Prop :=
    fun bs => ∀ e k, isContractiveBranches bs = true → e.isContractive = true →
      isContractiveBranches (substBranches bs k e) = true
  let P3 : Label × LocalTypeDB → Prop := fun b => P1 b.2
  have hrec : P1 body := by
    refine (LocalTypeDB.rec (motive_1 := P1) (motive_2 := P2) (motive_3 := P3)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ body)
    -- end case
    · intro e k hbody he
      simp [LocalTypeDB.subst, LocalTypeDB.isContractive]
    -- var case
    · intro n e k hbody he
      by_cases hnk : n = k
      · simp [LocalTypeDB.subst, LocalTypeDB.isContractive, hnk, he]
      · by_cases hgt : n > k
        · simp [LocalTypeDB.subst, LocalTypeDB.isContractive, hnk, hgt]
        · simp [LocalTypeDB.subst, LocalTypeDB.isContractive, hnk, hgt]
    -- send case
    · intro p bs hbs e k hbody he
      have hbs' : isContractiveBranches bs = true := by
        simpa [LocalTypeDB.isContractive] using hbody
      have hbs'' := hbs e k hbs' he
      simpa [LocalTypeDB.subst, LocalTypeDB.isContractive] using hbs''
    -- recv case
    · intro p bs hbs e k hbody he
      have hbs' : isContractiveBranches bs = true := by
        simpa [LocalTypeDB.isContractive] using hbody
      have hbs'' := hbs e k hbs' he
      simpa [LocalTypeDB.subst, LocalTypeDB.isContractive] using hbs''
    -- mu case
    · intro body hbody_ih e k hbody he
      have hpair : body.isGuarded 0 = true ∧ body.isContractive = true := by
        simpa [LocalTypeDB.isContractive, Bool.and_eq_true] using hbody
      rcases hpair with ⟨hguard, hcontr⟩
      have he_lift : (e.lift 1 0).isContractive = true := isContractive_lift e 1 0 he
      have hguard_subst : (body.subst (k + 1) (e.lift 1 0)).isGuarded 0 = true := by
        have hlt : 0 < k + 1 := Nat.succ_pos k
        have he_guard : (e.lift 1 0).isGuarded 0 = true := isGuarded_lift_zero e
        exact isGuarded_subst_lt body (e.lift 1 0) 0 (k + 1) hlt hguard he_guard
      have hcontr_subst : (body.subst (k + 1) (e.lift 1 0)).isContractive = true :=
        hbody_ih (e.lift 1 0) (k + 1) hcontr he_lift
      simp [LocalTypeDB.subst, LocalTypeDB.isContractive, hguard_subst, hcontr_subst]
    -- nil case
    · intro e k hbs he
      simp [isContractiveBranches, substBranches] at hbs ⊢
    -- cons case
    · intro head tail hhead htail e k hbs he
      obtain ⟨l, t⟩ := head
      simp [isContractiveBranches, substBranches, Bool.and_eq_true] at hbs ⊢
      rcases hbs with ⟨ht, hrest⟩
      constructor
      · exact hhead e k ht he
      · exact htail e k hrest he
    -- pair case
    · intro l t ht
      exact ht
  exact hrec e k hbody he

theorem isContractive_subst_branches (bs : List (Label × LocalTypeDB)) (e : LocalTypeDB) (k : Nat) :
    isContractiveBranches bs = true → e.isContractive = true →
    isContractiveBranches (substBranches bs k e) = true := by
  intro hbs he
  induction bs with
  | nil => simp [isContractiveBranches, substBranches] at hbs ⊢
  | cons head rest ih =>
      obtain ⟨l, t⟩ := head
      simp [isContractiveBranches, substBranches, Bool.and_eq_true] at hbs ⊢
      rcases hbs with ⟨ht, hrest⟩
      constructor
      · exact isContractive_subst t e k ht he
      · exact ih hrest

/-- Substituting a mu into its body preserves contractiveness (mu-unfolding case). -/
theorem isContractive_subst_mu (body : LocalTypeDB) :
  body.isContractive = true → (LocalTypeDB.mu body).isContractive = true →
  (body.subst 0 (LocalTypeDB.mu body)).isContractive = true := by
  intro hbody hmu
  exact isContractive_subst body (LocalTypeDB.mu body) 0 hbody hmu

/-- Unfolding preserves contractiveness. -/
theorem isContractive_unfold (t : LocalTypeDB) :
  t.isContractive = true → t.unfold.isContractive = true := by
  intro h
  cases t with
  | mu body =>
      have hbody : body.isContractive = true := by
        have hpair : body.isGuarded 0 = true ∧ body.isContractive = true := by
          simpa [LocalTypeDB.isContractive, Bool.and_eq_true] using h
        exact hpair.2
      simpa [LocalTypeDB.unfold] using isContractive_subst body (LocalTypeDB.mu body) 0 hbody h
  | «end» =>
      simpa [LocalTypeDB.unfold] using h
  | var n =>
      simpa [LocalTypeDB.unfold] using h
  | send p bs =>
      simpa [LocalTypeDB.unfold] using h
  | recv p bs =>
      simpa [LocalTypeDB.unfold] using h

/-- Iterated unfolding preserves contractiveness. -/
theorem isContractive_iter_unfold (k : Nat) (t : LocalTypeDB) :
  t.isContractive = true → ((LocalTypeDB.unfold)^[k] t).isContractive = true := by
  induction k generalizing t with
  | zero =>
      intro h
      simpa using h
  | succ k ih =>
      intro h
      have h' : t.unfold.isContractive = true := isContractive_unfold t h
      simpa [Function.iterate_succ] using ih (t := t.unfold) h'

/-- Full unfolding preserves contractiveness. -/
theorem isContractive_fullUnfold (t : LocalTypeDB) :
  t.isContractive = true → t.fullUnfold.isContractive = true := by
  intro h
  simpa [LocalTypeDB.fullUnfold] using
    isContractive_iter_unfold (k := t.muHeight) t h


end RumpsteakV2.Protocol
