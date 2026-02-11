import SessionTypes.LocalTypeConvProofs.Roundtrip.General

/-! # SessionTypes.LocalTypeConvProofs.Roundtrip.Contractive

Contractiveness preservation lemmas for the named↔DB roundtrip.
-/

/-
The Problem. Roundtrip adequacy depends on preserving contractiveness in both
conversion directions.

Solution Structure. Isolates contractiveness-preservation proofs, reusing the
general roundtrip context lemmas.
-/

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace SessionTypes.LocalTypeConvProofs
open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
open SessionTypes.LocalTypeDB
open SessionTypes.LocalTypeConv
open SessionTypes.NameOnlyContext

/-! ## Contractiveness preservation for fromDB -/

/-! ## Contractiveness preservation for fromDB -/

lemma isGuarded_fromDB_at (t : LocalTypeDB) (ctx : NameContext) (i : Nat) (v : String)
    (hget : NameContext.get? ctx i = some v)
    (huniq : ∀ j, NameContext.get? ctx j = some v → j = i)
    (hclosed : t.isClosedAt ctx.length = true)
    (hguard : t.isGuarded i = true) :
    (t.fromDB ctx hclosed).isGuarded v = true := by
  let P1 : LocalTypeDB → Prop :=
    fun t =>
      ∀ ctx i v,
        NameContext.get? ctx i = some v →
        (∀ j, NameContext.get? ctx j = some v → j = i) →
        (hclosed : t.isClosedAt ctx.length = true) →
        t.isGuarded i = true →
          (t.fromDB ctx hclosed).isGuarded v = true
  let P2 : List (Label × LocalTypeDB) → Prop := fun _ => True
  let P3 : Label × LocalTypeDB → Prop := fun _ => True
  have hrec : P1 t := by
    refine (LocalTypeDB.rec (motive_1 := P1) (motive_2 := P2) (motive_3 := P3)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ t)
    · intro ctx i v hget huniq hclosed hguard
      simp [LocalTypeDB.fromDB, LocalTypeR.isGuarded]
    · intro n ctx i v hget huniq hclosed hguard
      have hlt : n < ctx.length := by
        simpa [LocalTypeDB.isClosedAt] using hclosed
      obtain ⟨w, hgetn⟩ := get?_some_of_lt (ctx := ctx) (i := n) hlt
      have hne : n ≠ i := by
        intro hni
        simp [LocalTypeDB.isGuarded, hni] at hguard
      have hwne : v ≠ w := by
        intro hvw
        have hidx := huniq n (by simpa [hvw] using hgetn)
        exact hne hidx
      have hfrom : LocalTypeDB.fromDB ctx (.var n) hclosed = LocalTypeR.var w :=
        fromDB_var_of_get ctx n hclosed w hgetn
      simp [hfrom, LocalTypeR.isGuarded, hwne]
    · intro p bs hbs ctx i v hget huniq hclosed hguard
      simp [LocalTypeDB.fromDB, LocalTypeR.isGuarded]
    · intro p bs hbs ctx i v hget huniq hclosed hguard
      simp [LocalTypeDB.fromDB, LocalTypeR.isGuarded]
    · intro body hbody ctx i v hget huniq hclosed hguard
      by_cases hv : v = NameContext.freshName ctx
      · subst hv
        simp [LocalTypeDB.fromDB, LocalTypeR.isGuarded]
      ·
        have hclosed' : body.isClosedAt (ctx.length + 1) = true := by
          simpa [LocalTypeDB.isClosedAt] using hclosed
        have hguard' : body.isGuarded (i + 1) = true := by
          simpa [LocalTypeDB.isGuarded] using hguard
        have hget' : NameContext.get? (NameOnlyContext.cons (NameContext.freshName ctx) ctx) (i + 1) = some v := by
          simpa [NameContext.get?] using hget
        have huniq' :
            ∀ j, NameContext.get? (NameOnlyContext.cons (NameContext.freshName ctx) ctx) j = some v → j = i + 1 := by
          intro j hj
          cases j with
          | zero =>
              simp [NameContext.get?] at hj
              exact (hv hj.symm).elim
          | succ j =>
              have hj' : NameContext.get? ctx j = some v := by
                simpa [NameContext.get?] using hj
              have hidx := huniq j hj'
              simpa using congrArg Nat.succ hidx
        have hbody' :=
          hbody (ctx := NameOnlyContext.cons (NameContext.freshName ctx) ctx) (i := i + 1) (v := v)
            hget' huniq' hclosed' hguard'
        simp [LocalTypeDB.fromDB, LocalTypeR.isGuarded, hv, hbody']
    · exact True.intro
    · intro _ _ _ _
      exact True.intro
    · intro _ _ _
      exact True.intro
  exact hrec ctx i v hget huniq hclosed hguard

lemma isGuarded_fromDB_fresh (t : LocalTypeDB) (ctx : NameContext)
    (hfreshAll : ∀ c, NameContext.freshName c ∉ c)
    (hclosed : t.isClosedAt (ctx.length + 1) = true)
    (hguard : t.isGuarded 0 = true) :
    (t.fromDB (NameOnlyContext.cons (NameContext.freshName ctx) ctx) (by
      simpa [NameOnlyContext.cons_length] using hclosed)).isGuarded
        (NameContext.freshName ctx) = true := by
  let fresh := NameContext.freshName ctx
  let ctx' := NameOnlyContext.cons fresh ctx
  have hget : NameContext.get? ctx' 0 = some fresh := by
    show NameOnlyContext.get? (NameOnlyContext.cons fresh ctx) 0 = some fresh
    simp only [NameOnlyContext.get?_cons_zero]
  have huniq : ∀ j, NameContext.get? ctx' j = some fresh → j = 0 := by
    intro j hj
    cases j with
    | zero => rfl
    | succ j =>
        have hj' : NameContext.get? ctx j = some fresh := by
          simpa only [NameOnlyContext.get?_cons_succ] using hj
        have hmem : fresh ∈ ctx := get?_mem hj'
        exact (hfreshAll ctx hmem).elim
  have hclosed' : t.isClosedAt ctx'.length = true := by
    show t.isClosedAt (NameOnlyContext.cons fresh ctx).length = true
    simp only [NameOnlyContext.cons_length]
    exact hclosed
  exact isGuarded_fromDB_at t ctx' 0 fresh hget huniq hclosed' hguard

theorem isContractive_fromDB (t : LocalTypeDB) (ctx : NameContext)
    (hfreshAll : ∀ c, NameContext.freshName c ∉ c) :
    t.isContractive = true →
    (hclosed : t.isClosedAt (ctx.length) = true) →
    (t.fromDB ctx hclosed).isContractive = true := by
  intro hcontr hclosed
  let P1 : LocalTypeDB → Prop :=
    fun t =>
      ∀ ctx, (∀ c, NameContext.freshName c ∉ c) →
        t.isContractive = true →
        (hclosed : t.isClosedAt ctx.length = true) →
          (t.fromDB ctx hclosed).isContractive = true
  let P2 : List (Label × LocalTypeDB) → Prop :=
    fun bs =>
      ∀ ctx, (∀ c, NameContext.freshName c ∉ c) →
        isContractiveBranches bs = true →
        (hclosed : isClosedAtBranches ctx.length bs = true) →
          LocalTypeR.isContractiveBranches (LocalTypeDB.branchesFromDB ctx bs hclosed) = true
  let P3 : Label × LocalTypeDB → Prop :=
    fun b =>
      ∀ ctx, (∀ c, NameContext.freshName c ∉ c) →
        b.2.isContractive = true →
        (hclosed : b.2.isClosedAt ctx.length = true) →
          (b.2.fromDB ctx hclosed).isContractive = true
  have hrec : P1 t := by
    refine (LocalTypeDB.rec (motive_1 := P1) (motive_2 := P2) (motive_3 := P3)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ t)
    · intro ctx hfreshAll hcontr hclosed
      simp [LocalTypeDB.fromDB, LocalTypeR.isContractive]
    · intro n ctx hfreshAll hcontr hclosed
      simp [LocalTypeDB.fromDB, LocalTypeR.isContractive]
    · intro p bs hbs ctx hfreshAll hcontr hclosed
      have hbs_contr : isContractiveBranches bs = true := by
        simpa [LocalTypeDB.isContractive] using hcontr
      have hbs_closed : isClosedAtBranches ctx.length bs = true := by
        simpa [LocalTypeDB.isClosedAt] using hclosed
      have hbs' := hbs ctx hfreshAll hbs_contr hbs_closed
      simp [LocalTypeDB.fromDB, LocalTypeR.isContractive, hbs']
    · intro p bs hbs ctx hfreshAll hcontr hclosed
      have hbs_contr : isContractiveBranches bs = true := by
        simpa [LocalTypeDB.isContractive] using hcontr
      have hbs_closed : isClosedAtBranches ctx.length bs = true := by
        simpa [LocalTypeDB.isClosedAt] using hclosed
      have hbs' := hbs ctx hfreshAll hbs_contr hbs_closed
      simp [LocalTypeDB.fromDB, LocalTypeR.isContractive, hbs']
    · intro body hbody ctx hfreshAll hcontr hclosed
      simp [LocalTypeDB.isContractive] at hcontr
      rcases hcontr with ⟨hguard, hbody_contr⟩
      have hclosed' : body.isClosedAt (ctx.length + 1) = true := by
        simpa [LocalTypeDB.isClosedAt] using hclosed
      have hguard' := isGuarded_fromDB_fresh body ctx hfreshAll hclosed' hguard
      have hbody' :=
        hbody (ctx := NameOnlyContext.cons (NameContext.freshName ctx) ctx) hfreshAll hbody_contr hclosed'
      simp [LocalTypeDB.fromDB, LocalTypeR.isContractive, hguard', hbody']
    · intro ctx hfreshAll hcontr hclosed
      simp [LocalTypeDB.branchesFromDB, LocalTypeR.isContractiveBranches, isClosedAtBranches] at hcontr hclosed ⊢
    · intro head tail hhead htail ctx hfreshAll hcontr hclosed
      obtain ⟨l, t⟩ := head
      have hpair_contr : t.isContractive = true ∧ isContractiveBranches tail = true := by
        simpa [isContractiveBranches, Bool.and_eq_true] using hcontr
      have hpair_closed : t.isClosedAt ctx.length = true ∧ isClosedAtBranches ctx.length tail = true := by
        simpa [isClosedAtBranches] using hclosed
      have ht := hhead ctx hfreshAll hpair_contr.1 hpair_closed.1
      have htl := htail ctx hfreshAll hpair_contr.2 hpair_closed.2
      simp [LocalTypeDB.branchesFromDB, LocalTypeR.isContractiveBranches, ht, htl]
    · intro fst snd hsnd
      exact hsnd
  exact hrec ctx hfreshAll hcontr hclosed


end SessionTypes.LocalTypeConvProofs
