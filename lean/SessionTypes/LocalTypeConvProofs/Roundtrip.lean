import SessionTypes.LocalTypeConvProofs.ClosedRoundtrip

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-
The Problem. The conversion roundtrip proof for arbitrary contexts (not just empty/closed)
requires showing that guardedness and contractiveness are preserved across conversions.
This is essential for verifying that well-formed named types convert to well-formed de Bruijn
types and vice versa.

Solution Structure. Proves `toDB_fromDB_roundtrip` for arbitrary nodup contexts with fresh
name generation. `isGuarded_toDB` shows that guardedness in named representation implies
guardedness in de Bruijn. `isContractive_toDB` and `isContractive_fromDB` prove that
contractiveness is preserved in both directions, enabling well-formedness preservation.
-/

/-! # SessionTypes.LocalTypeConvProofs.Roundtrip

General roundtrip with adequate context, and guardedness/contractiveness preservation across conversions.
-/

namespace SessionTypes.LocalTypeConvProofs
open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
open SessionTypes.LocalTypeDB
open SessionTypes.LocalTypeConv
open SessionTypes.NameOnlyContext
/-! ## General roundtrip with adequate context -/

theorem toDB_fromDB_roundtrip (t : LocalTypeDB) (ctx : NameContext)
    (hnodup : ctx.Nodup)
    (hfreshAll : ∀ c, NameContext.freshName c ∉ c)
    (hclosed : t.isClosedAt ctx.length = true) :
    (t.fromDB ctx hclosed).toDB? ctx = some t := by
  let P1 : LocalTypeDB → Prop :=
    fun t =>
      ∀ ctx, ctx.Nodup → (∀ c, NameContext.freshName c ∉ c) →
        (hclosed : t.isClosedAt ctx.length = true) →
          (t.fromDB ctx hclosed).toDB? ctx = some t
  let P2 : List (Label × LocalTypeDB) → Prop :=
    fun bs =>
      ∀ ctx, ctx.Nodup → (∀ c, NameContext.freshName c ∉ c) →
        (hclosed : isClosedAtBranches ctx.length bs = true) →
          LocalTypeR.branchesToDB? ctx (LocalTypeDB.branchesFromDB ctx bs hclosed) = some bs
  let P3 : Label × LocalTypeDB → Prop :=
    fun b =>
      ∀ ctx, ctx.Nodup → (∀ c, NameContext.freshName c ∉ c) →
        (hclosed : b.2.isClosedAt ctx.length = true) →
          (b.2.fromDB ctx hclosed).toDB? ctx = some b.2
  have hrec : P1 t := by
    refine (LocalTypeDB.rec (motive_1 := P1) (motive_2 := P2) (motive_3 := P3)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ t)
    · intro ctx hnodup hfreshAll hclosed
      simp [LocalTypeDB.fromDB, LocalTypeR.toDB?]
    · intro n ctx hnodup hfreshAll hclosed
      have hlt : n < ctx.length := by
        simpa [LocalTypeDB.isClosedAt] using hclosed
      obtain ⟨v, hget⟩ := get?_some_of_lt (ctx := ctx) (i := n) hlt
      have hidx : Context.indexOf ctx v = some n := get_indexOf_roundtrip ctx n v hnodup hget
      have hfrom : LocalTypeDB.fromDB ctx (.var n) hclosed = LocalTypeR.var v :=
        fromDB_var_of_get ctx n hclosed v hget
      simp [hfrom, LocalTypeR.toDB?]
      rw [Context.indexOf_eq] at hidx
      simp [hidx]
    · intro p bs hbs ctx hnodup hfreshAll hclosed
      have hclosed' : isClosedAtBranches ctx.length bs = true := by
        simpa [LocalTypeDB.isClosedAt] using hclosed
      have hbs' := hbs ctx hnodup hfreshAll hclosed'
      simp [LocalTypeDB.fromDB, LocalTypeR.toDB?, hbs']
    · intro p bs hbs ctx hnodup hfreshAll hclosed
      have hclosed' : isClosedAtBranches ctx.length bs = true := by
        simpa [LocalTypeDB.isClosedAt] using hclosed
      have hbs' := hbs ctx hnodup hfreshAll hclosed'
      simp [LocalTypeDB.fromDB, LocalTypeR.toDB?, hbs']
    · intro body hbody ctx hnodup hfreshAll hclosed
      have hclosed' : body.isClosedAt (ctx.length + 1) = true := by
        simpa [LocalTypeDB.isClosedAt] using hclosed
      have hnodup' : (NameOnlyContext.cons (NameContext.freshName ctx) ctx).Nodup := by
        apply List.nodup_cons.mpr
        exact ⟨hfreshAll ctx, hnodup⟩
      have hbody' := hbody (ctx := NameOnlyContext.cons (NameContext.freshName ctx) ctx) hnodup' hfreshAll hclosed'
      simp [LocalTypeDB.fromDB, LocalTypeR.toDB?, hbody']
    · intro ctx hnodup hfreshAll hclosed
      simp [LocalTypeDB.branchesFromDB, LocalTypeR.branchesToDB?]
    · intro head tail hhead htail ctx hnodup hfreshAll hclosed
      obtain ⟨l, t⟩ := head
      have hclosed' : t.isClosedAt ctx.length = true ∧ isClosedAtBranches ctx.length tail = true := by
        simpa [isClosedAtBranches] using hclosed
      have ht := hhead ctx hnodup hfreshAll hclosed'.1
      have htl := htail ctx hnodup hfreshAll hclosed'.2
      simp [LocalTypeDB.branchesFromDB, LocalTypeR.branchesToDB?, ht, htl]
    · intro fst snd hsnd ctx hnodup hfreshAll hclosed
      exact hsnd ctx hnodup hfreshAll hclosed
  exact hrec ctx hnodup hfreshAll hclosed

theorem branches_toDB_fromDB_roundtrip (bs : List (Label × LocalTypeDB)) (ctx : NameContext)
    (hnodup : ctx.Nodup)
    (hfreshAll : ∀ c, NameContext.freshName c ∉ c)
    (hclosed : isClosedAtBranches ctx.length bs = true) :
    LocalTypeR.branchesToDB? ctx (LocalTypeDB.branchesFromDB ctx bs hclosed) = some bs := by
  induction bs with
  | nil => simp [LocalTypeDB.branchesFromDB, LocalTypeR.branchesToDB?]
  | cons hd tl ih =>
      obtain ⟨l, t⟩ := hd
      have hclosed' : t.isClosedAt ctx.length = true ∧ isClosedAtBranches ctx.length tl = true := by
        simpa [isClosedAtBranches] using hclosed
      have ht := toDB_fromDB_roundtrip t ctx hnodup hfreshAll hclosed'.1
      have htl := ih hclosed'.2
      simp [LocalTypeDB.branchesFromDB, LocalTypeR.branchesToDB?, ht, htl]

/-! ## Guardedness / contractiveness preservation -/

theorem isGuarded_toDB_shadowed_prefix (t : LocalTypeR) (pref ctx : Context) (x : String) (i : Nat)
    (db : LocalTypeDB) :
    Context.indexOf ctx x = some i →
    t.toDB? (pref ++ x :: ctx) = some db →
    db.isGuarded (i + pref.length + 1) = true := by
  intro hidx hdb
  let P1 : LocalTypeR → Prop :=
    fun t =>
      ∀ pref ctx i db,
        Context.indexOf ctx x = some i →
        t.toDB? (pref ++ x :: ctx) = some db →
          db.isGuarded (i + pref.length + 1) = true
  let P2 : List BranchR → Prop := fun _ => True
  let P3 : BranchR → Prop := fun _ => True
  let P4 : Option ValType × LocalTypeR → Prop := fun _ => True
  have hrec : P1 t := by
    refine (LocalTypeR.LocalTypeR.rec
      (motive_1 := P1) (motive_2 := P2) (motive_3 := P3) (motive_4 := P4)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ t)
    · intro pref ctx i db hidx hdb
      simp [LocalTypeR.toDB?] at hdb
      cases hdb
      simp [LocalTypeDB.isGuarded]
    · intro p bs hbs pref ctx i db hidx hdb
      cases hdbs : LocalTypeR.branchesToDB? (pref ++ NameOnlyContext.cons x ctx) bs with
      | none =>
          simp [LocalTypeR.toDB?, hdbs] at hdb
      | some dbs =>
          simp [LocalTypeR.toDB?, hdbs] at hdb
          subst hdb
          simp [LocalTypeDB.isGuarded]
    · intro p bs hbs pref ctx i db hidx hdb
      simp only [fromList_cons_toList] at hdb
      cases hdbs : LocalTypeR.branchesToDB? (pref ++ NameOnlyContext.cons x ctx) bs with
      | none =>
          simp [LocalTypeR.toDB?, hdbs] at hdb
      | some dbs =>
          simp [LocalTypeR.toDB?, hdbs] at hdb
          subst hdb
          simp [LocalTypeDB.isGuarded]
    · intro y body hbody pref ctx i db hidx hdb
      simp only [fromList_toList, fromList_cons] at hdb
      cases hbody_db : body.toDB? (cons y (pref ++ cons x ctx)) with
      | none =>
          simp [LocalTypeR.toDB?, hbody_db, Option.map] at hdb
      | some db' =>
          simp [LocalTypeR.toDB?, hbody_db, Option.map] at hdb
          have hdb' : db = LocalTypeDB.mu db' := by
            simpa using hdb.symm
          subst hdb'
          have hguard' :
              db'.isGuarded (i + (cons y pref).length + 1) = true := by
            have hbody' : body.toDB? ((cons y pref) ++ fromList (x :: toList ctx)) = some db' := by
              simp only [fromList_cons_toList]
              simpa using hbody_db
            exact hbody (pref := cons y pref) (ctx := ctx) (i := i) (db := db') hidx hbody'
          have hguard'' : db'.isGuarded (i + pref.length + 1 + 1) = true := by
            have : i + (cons y pref).length + 1 = i + pref.length + 1 + 1 := by
              simp [Nat.add_left_comm, Nat.add_comm, cons_length]
            simpa [this] using hguard'
          simpa [LocalTypeDB.isGuarded, Nat.add_left_comm, Nat.add_comm] using hguard''
    · intro v pref ctx i db hidx hdb
      simp only [LocalTypeR.toDB?, fromList_cons_toList] at hdb
      cases hj : NameOnlyContext.indexOf (pref ++ NameOnlyContext.cons x ctx) v with
      | none => simp [hj] at hdb
      | some j =>
          simp only [hj, Option.map, Option.some.injEq] at hdb
          subst hdb
          simp only [LocalTypeDB.isGuarded, bne_iff_ne, ne_eq]
          intro heq
          -- heq: j = i + pref.length + 1
          -- Need to derive contradiction by showing j ≤ pref.length or j = pref.length + 1 + k for some k ≠ i
          -- Use indexOf_append_x_le to show x appears at position ≤ pref.length
          have ⟨k, hk, hkle⟩ := indexOf_append_x_le pref ctx x
          simp only [Context.indexOf] at hk hj
          -- If v = x, then j = k ≤ pref.length < i + pref.length + 1, contradiction
          -- If v ≠ x, then j > pref.length (since x appears first), and j = pref.length + 1 + m
          -- where m is the index of v in ctx. Since indexOf ctx x = i and v ≠ x, m ≠ i.
          by_cases hjle : j ≤ pref.length
          · -- j ≤ pref.length contradicts heq: j = i + pref.length + 1 ≥ pref.length + 1
            omega
          · -- j > pref.length, so v ≠ x (since x appears at position ≤ pref.length)
            push_neg at hjle
            have hvx : v ≠ x := by
              intro hvx
              subst hvx
              have hjk : j = k := Option.some.inj (hj.symm.trans hk)
              omega
            have hctx := indexOf_append_suffix hvx (by simp only [Context.indexOf]; exact hj) hjle
            have heq' : j - pref.length - 1 = i := by omega
            simp only [heq'] at hctx
            have hvx' := indexOf_inj (ctx := ctx) hctx hidx
            exact hvx hvx'
    · exact True.intro
    · intro _ _ _ _
      exact True.intro
    · intro _ _ _
      exact True.intro
    · intro _ _ _
      exact True.intro
  exact hrec pref ctx i db hidx hdb

theorem isGuarded_toDB (t : LocalTypeR) (ctx : Context) (x : String) (i : Nat) (db : LocalTypeDB) :
    t.isGuarded x = true →
    ctx.indexOf x = some i →
    t.toDB? ctx = some db →
    db.isGuarded i = true := by
  intro hguard hidx hdb
  let P1 : LocalTypeR → Prop :=
    fun t =>
      ∀ ctx x i db,
        t.isGuarded x = true →
        ctx.indexOf x = some i →
        t.toDB? ctx = some db →
          db.isGuarded i = true
  let P2 : List BranchR → Prop := fun _ => True
  let P3 : BranchR → Prop := fun _ => True
  let P4 : Option ValType × LocalTypeR → Prop := fun _ => True
  have hrec : P1 t := by
    refine (LocalTypeR.LocalTypeR.rec
      (motive_1 := P1) (motive_2 := P2) (motive_3 := P3) (motive_4 := P4)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ t)
    · intro ctx x i db hguard hidx hdb
      simp [LocalTypeR.toDB?] at hdb
      cases hdb
      simp [LocalTypeDB.isGuarded]
    · intro p bs hbs ctx x i db hguard hidx hdb
      cases hdbs : LocalTypeR.branchesToDB? ctx bs with
      | none =>
          simp [LocalTypeR.toDB?, hdbs] at hdb
      | some dbs =>
          simp [LocalTypeR.toDB?, hdbs] at hdb
          subst hdb
          simp [LocalTypeDB.isGuarded]
    · intro p bs hbs ctx x i db hguard hidx hdb
      cases hdbs : LocalTypeR.branchesToDB? ctx bs with
      | none =>
          simp [LocalTypeR.toDB?, hdbs] at hdb
      | some dbs =>
          simp [LocalTypeR.toDB?, hdbs] at hdb
          subst hdb
          simp [LocalTypeDB.isGuarded]
    · intro y body hbody ctx x i db hguard hidx hdb
      simp only [LocalTypeR.toDB?] at hdb
      cases hbody_db : body.toDB? (NameOnlyContext.cons y ctx) with
      | none => simp [hbody_db, Option.map] at hdb
      | some db' =>
          simp only [hbody_db, Option.map, Option.some.injEq] at hdb
          subst hdb
          simp only [LocalTypeDB.isGuarded]
          by_cases hxy : x = y
          · -- Case x = y: variable is shadowed by the mu binder
            -- Use isGuarded_toDB_shadowed_prefix with empty prefix
            subst hxy
            have hbody' : body.toDB? (TypeContext.empty ++ (x :: (ctx : List String) : Context)) = some db' := by
              simp only [empty_append_eq, fromList_cons_toList]
              exact hbody_db
            have hguard' := isGuarded_toDB_shadowed_prefix body TypeContext.empty ctx x i db' hidx hbody'
            simp only [TypeContext.length_empty, Nat.add_zero] at hguard'
            exact hguard'
          · -- Case x ≠ y: use IH on body
            have hguard_body : body.isGuarded x = true := by
              simp only [LocalTypeR.isGuarded] at hguard
              have hbeq : (x == y) = false := beq_eq_false_iff_ne.mpr hxy
              simp only [hbeq, Bool.false_eq_true, ↓reduceIte] at hguard
              exact hguard
            have hidx' : (NameOnlyContext.cons y ctx).indexOf x = some (i + 1) := by
              show NameOnlyContext.indexOf (NameOnlyContext.cons y ctx) x = some (i + 1)
              rw [NameOnlyContext.indexOf_cons_ne ctx (Ne.symm hxy)]
              show Option.map Nat.succ (NameOnlyContext.indexOf ctx x) = some (i + 1)
              have hidx'' : NameOnlyContext.indexOf ctx x = some i := hidx
              rw [hidx'']
              rfl
            exact hbody (NameOnlyContext.cons y ctx) x (i + 1) db' hguard_body hidx' hbody_db
    · intro v ctx x i db hguard hidx hdb
      simp only [LocalTypeR.toDB?] at hdb
      cases hj : NameOnlyContext.indexOf ctx v with
      | none => simp [hj] at hdb
      | some j =>
          simp only [hj, Option.map, Option.some.injEq] at hdb
          subst hdb
          simp only [LocalTypeDB.isGuarded, bne_iff_ne, ne_eq]
          -- v ≠ x from hguard, indexOf ctx v = some j, indexOf ctx x = some i
          -- By indexOf_inj contrapositive, j ≠ i
          have hvx : v ≠ x := by
            simp only [LocalTypeR.isGuarded, bne_iff_ne, ne_eq] at hguard
            exact Ne.symm hguard
          intro hjei
          have hjei' : Context.indexOf ctx v = some i := by
            simp only [Context.indexOf, hj, hjei]
          have hvx' := indexOf_inj hjei' hidx
          exact hvx hvx'
    · exact True.intro
    · intro _ _ _ _
      exact True.intro
    · intro _ _ _
      exact True.intro
    · intro _ _ _
      exact True.intro
  exact hrec ctx x i db hguard hidx hdb

theorem isContractive_toDB (t : LocalTypeR) (ctx : Context) (db : LocalTypeDB) :
    t.isContractive = true →
    t.toDB? ctx = some db →
    db.isContractive = true := by
  intro hcontr hdb
  let P1 : LocalTypeR → Prop :=
    fun t =>
      ∀ ctx db, t.isContractive = true → t.toDB? ctx = some db → db.isContractive = true
  let P2 : List BranchR → Prop :=
    fun bs =>
      ∀ ctx dbs, LocalTypeR.isContractiveBranches bs = true →
        LocalTypeR.branchesToDB? ctx bs = some dbs →
          isContractiveBranches dbs = true
  let P3 : BranchR → Prop :=
    fun b =>
      ∀ ctx db, b.2.2.isContractive = true → b.2.2.toDB? ctx = some db → db.isContractive = true
  let P4 : Option ValType × LocalTypeR → Prop :=
    fun b =>
      ∀ ctx db, b.2.isContractive = true → b.2.toDB? ctx = some db → db.isContractive = true
  have hrec : P1 t := by
    refine (LocalTypeR.LocalTypeR.rec
      (motive_1 := P1) (motive_2 := P2) (motive_3 := P3) (motive_4 := P4)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ t)
    · intro ctx db hcontr hdb
      simp [LocalTypeR.toDB?] at hdb
      cases hdb
      simp [LocalTypeDB.isContractive]
    · intro p bs hbs ctx db hcontr hdb
      have hbs_contr : LocalTypeR.isContractiveBranches bs = true := by
        simpa [LocalTypeR.isContractive] using hcontr
      cases hdbs : LocalTypeR.branchesToDB? ctx bs with
      | none =>
          simp [LocalTypeR.toDB?, hdbs] at hdb
      | some dbs =>
          simp [LocalTypeR.toDB?, hdbs] at hdb
          subst hdb
          have hdbs_contr := hbs ctx dbs hbs_contr hdbs
          simp [LocalTypeDB.isContractive, hdbs_contr]
    · intro p bs hbs ctx db hcontr hdb
      have hbs_contr : LocalTypeR.isContractiveBranches bs = true := by
        simpa [LocalTypeR.isContractive] using hcontr
      cases hdbs : LocalTypeR.branchesToDB? ctx bs with
      | none =>
          simp [LocalTypeR.toDB?, hdbs] at hdb
      | some dbs =>
          simp [LocalTypeR.toDB?, hdbs] at hdb
          subst hdb
          have hdbs_contr := hbs ctx dbs hbs_contr hdbs
          simp [LocalTypeDB.isContractive, hdbs_contr]
    · intro x body hbody ctx db hcontr hdb
      simp only [LocalTypeR.isContractive, Bool.and_eq_true] at hcontr
      rcases hcontr with ⟨hguard, hbody_contr⟩
      simp only [LocalTypeR.toDB?] at hdb
      cases hbody_db : body.toDB? (NameOnlyContext.cons x ctx) with
      | none => simp [hbody_db, Option.map] at hdb
      | some db' =>
          simp only [hbody_db, Option.map, Option.some.injEq] at hdb
          subst hdb
          simp only [LocalTypeDB.isContractive, Bool.and_eq_true]
          constructor
          · -- Show db'.isGuarded 0 = true
            have hidx : (NameOnlyContext.cons x ctx).indexOf x = some 0 := by
              simp only [NameOnlyContext.indexOf_cons_eq]
            exact isGuarded_toDB body (NameOnlyContext.cons x ctx) x 0 db' hguard hidx hbody_db
          · -- Show db'.isContractive = true using IH
            exact hbody (NameOnlyContext.cons x ctx) db' hbody_contr hbody_db
    · intro v ctx db hcontr hdb
      -- Variables are always contractive in both representations
      simp only [LocalTypeR.toDB?] at hdb
      cases hj : NameOnlyContext.indexOf ctx v with
      | none => simp [hj] at hdb
      | some j =>
          simp only [hj, Option.map, Option.some.injEq] at hdb
          subst hdb
          simp [LocalTypeDB.isContractive]
    · intro ctx dbs hcontr hdbs
      cases dbs with
      | nil =>
          simp [LocalTypeR.branchesToDB?] at hdbs
          simp [isContractiveBranches]
      | cons hd tl =>
          simp [LocalTypeR.branchesToDB?] at hdbs
    · intro head tail hhead htail ctx dbs hcontr hdbs
      obtain ⟨l, _vt, t⟩ := head
      have hpair : t.isContractive = true ∧ LocalTypeR.isContractiveBranches tail = true := by
        simpa [LocalTypeR.isContractiveBranches, Bool.and_eq_true] using hcontr
      cases htdb : t.toDB? ctx with
      | none =>
          simp [LocalTypeR.branchesToDB?, htdb] at hdbs
      | some t' =>
          cases htaildb : LocalTypeR.branchesToDB? ctx tail with
          | none =>
              simp [LocalTypeR.branchesToDB?, htdb, htaildb] at hdbs
          | some tl' =>
              simp [LocalTypeR.branchesToDB?, htdb, htaildb] at hdbs
              subst hdbs
              have ht : t'.isContractive = true := hhead ctx t' hpair.1 htdb
              have htl : isContractiveBranches tl' = true := htail ctx tl' hpair.2 htaildb
              simp [isContractiveBranches, ht, htl]
    · intro fst snd hsnd ctx db hcontr hdb
      exact hsnd ctx db hcontr hdb
    · intro fst snd hsnd
      exact hsnd
  exact hrec ctx db hcontr hdb

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

/-! ## Substitution (Named → DB) -/

/-- If a variable is not free, named substitution is a no-op and conversion is unchanged. -/
theorem toDB?_substitute_not_free
    (t repl : LocalTypeR) (ctx : Context) (x : String) (db : LocalTypeDB)
    (hdb : t.toDB? ctx = some db)
    (hfree : LocalTypeR.isFreeIn x t = false) :
    (t.substitute x repl).toDB? ctx = some db := by
  have hsub : t.substitute x repl = t :=
    LocalTypeR.substitute_not_free t x repl hfree
  simpa [hsub] using hdb

end SessionTypes.LocalTypeConvProofs
