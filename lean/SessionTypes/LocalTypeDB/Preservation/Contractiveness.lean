import SessionTypes.LocalTypeDB.Preservation.Closedness

/-! # SessionTypes.LocalTypeDB.Preservation.Contractiveness

Contractiveness preservation under lift/subst/unfold in de Bruijn local types.
-/

/-
The Problem. Contractiveness invariants must survive structural operations for
sound recursion reasoning.

Solution Structure. Proves contractiveness preservation for lift/substitution,
then derives unfold/full-unfold preservation.
-/

set_option linter.unusedSimpArgs false

namespace SessionTypes
open SessionTypes.GlobalType

/-! ## Contractiveness Preservation -/

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


end SessionTypes
