import SessionTypes.LocalTypeDB.Core

set_option linter.unusedSimpArgs false

/-
The Problem. Operations on de Bruijn types (lift, subst, unfold) must preserve closedness
and contractiveness invariants. Without these preservation theorems, we cannot ensure that
derived types remain well-formed after transformation.

Solution Structure. Proves `isClosedAt_lift` and `isClosedAt_subst` showing closedness
is preserved. For guardedness, proves `isGuarded_lift_lt/ge` and `isGuarded_subst_lt`
handling index relationships. `isContractive_subst` and `isContractive_unfold` show
contractiveness is preserved, culminating in `isContractive_fullUnfold` for full mu-unfolding.
-/

/-! # LocalTypeDB Preservation

Closedness and contractiveness preservation for lift, subst, unfold on de Bruijn local types.
-/

namespace SessionTypes
open SessionTypes.GlobalType
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


end SessionTypes
