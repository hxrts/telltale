import SessionTypes.LocalTypeConvProofs.Helpers

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-
The Problem. Converting between named and de Bruijn representations must be correct:
fromDB should invert toDB for closed terms. Proving this requires showing that conversion
preserves closedness and that roundtrips produce the original term.

Solution Structure. Proves `fromDB?_eq_fromDB_all_ctx` showing the partial and total fromDB
agree on closed terms. `freeVars_fromDB_subset_ctx` shows closedness is preserved. The
roundtrip theorems `toDB_fromDB_roundtrip_generated` and `toDB_fromDB_roundtrip_closed`
prove that fromDB then toDB recovers the original de Bruijn term.
-/

/-! # SessionTypes.LocalTypeConvProofs.ClosedRoundtrip

fromDB?/fromDB correctness, closedness preservation, toDB? for closed terms, and roundtrip proofs.
-/

namespace SessionTypes.LocalTypeConvProofs
open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
open SessionTypes.LocalTypeDB
open SessionTypes.LocalTypeConv
open SessionTypes.NameOnlyContext
-- fromDB? correctness for closed terms

lemma fromDB_var_of_get (ctx : NameContext) (n : Nat)
    (hclosed : (LocalTypeDB.var n).isClosedAt ctx.length = true)
    (v : String) (hget : ctx.get? n = some v) :
    LocalTypeDB.fromDB ctx (.var n) hclosed = LocalTypeR.var v := by
  classical
  have hlt : n < ctx.length := by
    simpa [LocalTypeDB.isClosedAt] using hclosed
  have hspec :
      SessionTypes.NameOnlyContext.get? ctx n =
        some (Classical.choose (SessionTypes.NameOnlyContext.get?_lt (ctx := ctx) (i := n) hlt)) :=
    Classical.choose_spec (SessionTypes.NameOnlyContext.get?_lt (ctx := ctx) (i := n) hlt)
  have hget' : SessionTypes.NameOnlyContext.get? ctx n = some v := by
    simpa using hget
  have hv :
      Classical.choose (SessionTypes.NameOnlyContext.get?_lt (ctx := ctx) (i := n) hlt) = v := by
    apply Option.some.inj
    exact hspec.symm.trans hget'
  simp [LocalTypeDB.fromDB, hv]

theorem fromDB?_eq_fromDB_all_ctx (t : LocalTypeDB) (ctx : NameContext)
    (hclosed : t.isClosedAt ctx.length = true) :
    t.fromDB? ctx = some (t.fromDB ctx hclosed) := by
  let P1 : LocalTypeDB → Prop :=
    fun t => ∀ ctx, (hclosed : t.isClosedAt ctx.length = true) →
      t.fromDB? ctx = some (t.fromDB ctx hclosed)
  let P2 : List (Label × LocalTypeDB) → Prop :=
    fun bs =>
      ∀ ctx, (hclosed : isClosedAtBranches ctx.length bs = true) →
        branchesFromDB? ctx bs = some (branchesFromDB ctx bs hclosed)
  let P3 : Label × LocalTypeDB → Prop :=
    fun b =>
      ∀ ctx, (hclosed : b.2.isClosedAt ctx.length = true) →
        b.2.fromDB? ctx = some (b.2.fromDB ctx hclosed)

  -- fromDB? = fromDB: Structural Recursion

  have hrec : P1 t := by
    refine (LocalTypeDB.rec (motive_1 := P1) (motive_2 := P2) (motive_3 := P3)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ t)
    · intro ctx hclosed
      simp [LocalTypeDB.fromDB?, LocalTypeDB.fromDB]
    · intro n ctx hclosed
      have hlt : n < ctx.length := by
        simpa [LocalTypeDB.isClosedAt] using hclosed
      obtain ⟨v, hget⟩ := get?_some_of_lt (ctx := ctx) (i := n) hlt
      have hfrom : LocalTypeDB.fromDB ctx (.var n) hclosed = LocalTypeR.var v :=
        fromDB_var_of_get ctx n hclosed v hget
      simp [LocalTypeDB.fromDB?, hget, hfrom]
    · intro p bs hbs ctx hclosed
      have hclosed' : isClosedAtBranches ctx.length bs = true := by
        simpa [LocalTypeDB.isClosedAt] using hclosed
      have hbs' := hbs ctx hclosed'
      simp [LocalTypeDB.fromDB?, LocalTypeDB.fromDB, hbs']
    · intro p bs hbs ctx hclosed
      have hclosed' : isClosedAtBranches ctx.length bs = true := by
        simpa [LocalTypeDB.isClosedAt] using hclosed
      have hbs' := hbs ctx hclosed'
      simp [LocalTypeDB.fromDB?, LocalTypeDB.fromDB, hbs']
    · intro body hbody ctx hclosed
      have hclosed' : body.isClosedAt (ctx.length + 1) = true := by
        simpa [LocalTypeDB.isClosedAt] using hclosed
      have hclosed'' : body.isClosedAt (NameOnlyContext.cons (NameContext.freshName ctx) ctx).length = true := by
        simp only [NameOnlyContext.cons_length]
        exact hclosed'
      have hbody' := hbody (NameOnlyContext.cons (NameContext.freshName ctx) ctx) hclosed''
      simp [LocalTypeDB.fromDB?, LocalTypeDB.fromDB, hbody']
    · intro ctx hclosed
      simp [LocalTypeDB.branchesFromDB?, LocalTypeDB.branchesFromDB]
    · intro head tail hhead htail ctx hclosed
      obtain ⟨l, t⟩ := head
      have hclosed' : t.isClosedAt ctx.length = true ∧
          isClosedAtBranches ctx.length tail = true := by
        simpa [isClosedAtBranches] using hclosed
      have ht := hhead ctx hclosed'.1
      have htl := htail ctx hclosed'.2
      simp [LocalTypeDB.branchesFromDB?, LocalTypeDB.branchesFromDB, ht, htl]
    · intro fst snd hsnd
      exact hsnd
  exact hrec ctx hclosed

-- fromDB? = fromDB for Branch Lists

theorem branchesFromDB?_eq_branchesFromDB (bs : List (Label × LocalTypeDB)) (ctx : NameContext)
    (hclosed : isClosedAtBranches ctx.length bs = true) :
    branchesFromDB? ctx bs = some (branchesFromDB ctx bs hclosed) := by
  induction bs with
  | nil => simp [LocalTypeDB.branchesFromDB?, LocalTypeDB.branchesFromDB]
  | cons hd tl ih =>
      obtain ⟨l, t⟩ := hd
      have hclosed' : t.isClosedAt ctx.length = true ∧
          isClosedAtBranches ctx.length tl = true := by
        simpa [isClosedAtBranches] using hclosed
      have ht := fromDB?_eq_fromDB_all_ctx t ctx hclosed'.1
      have htl := ih hclosed'.2
      simp [LocalTypeDB.branchesFromDB?, LocalTypeDB.branchesFromDB, ht, htl]

-- fromDB? = fromDB at Empty Context

theorem fromDB?_eq_fromDB_closed (t : LocalTypeDB) (_hclosed : t.isClosed = true) :
    ∀ hclosed' : t.isClosedAt (TypeContext.empty : NameContext).length = true,
      t.fromDB? TypeContext.empty = some (t.fromDB TypeContext.empty hclosed') := by
  intro hclosed'
  exact fromDB?_eq_fromDB_all_ctx t TypeContext.empty hclosed'

-- fromDB closedness

lemma freeVars_fromDB_subset_ctx (t : LocalTypeDB) (ctx : NameContext)
    (hclosed : t.isClosedAt ctx.length = true) :
    ∀ v, v ∈ (t.fromDB ctx hclosed).freeVars → v ∈ ctx := by
  let P1 : LocalTypeDB → Prop :=
    fun t =>
      ∀ ctx, (hclosed : t.isClosedAt ctx.length = true) →
        ∀ v, v ∈ (t.fromDB ctx hclosed).freeVars → v ∈ ctx
  let P2 : List (Label × LocalTypeDB) → Prop :=
    fun bs =>
      ∀ ctx, (hclosed : isClosedAtBranches ctx.length bs = true) →
        ∀ v, v ∈ LocalTypeR.freeVarsOfBranches (LocalTypeDB.branchesFromDB ctx bs hclosed) → v ∈ ctx
  let P3 : Label × LocalTypeDB → Prop :=
    fun b =>
      ∀ ctx, (hclosed : b.2.isClosedAt ctx.length = true) →
        ∀ v, v ∈ (b.2.fromDB ctx hclosed).freeVars → v ∈ ctx

  -- fromDB Closedness: Structural Recursion Setup

  have hrec : P1 t := by
    refine (LocalTypeDB.rec (motive_1 := P1) (motive_2 := P2) (motive_3 := P3)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ t)
    · intro ctx hclosed v hv
      simp [LocalTypeDB.fromDB, LocalTypeR.freeVars] at hv
    · intro n ctx hclosed v hv
      have hlt : n < ctx.length := by
        simpa [LocalTypeDB.isClosedAt] using hclosed
      obtain ⟨name, hget⟩ := get?_some_of_lt (ctx := ctx) (i := n) hlt
      have hfrom : LocalTypeDB.fromDB ctx (.var n) hclosed = LocalTypeR.var name :=
        fromDB_var_of_get ctx n hclosed name hget
      have hv' : v ∈ (LocalTypeR.var name).freeVars := by
        simpa [hfrom] using hv
      have hv'' : v = name := by
        simpa [LocalTypeR.freeVars] using hv'
      subst hv''
      exact get?_mem hget

    -- fromDB Closedness: send/recv/mu/branches Cases

    · intro p bs hbs ctx hclosed v hv
      have hclosed' : isClosedAtBranches ctx.length bs = true := by
        simpa [LocalTypeDB.isClosedAt] using hclosed
      have hv' :
          v ∈ LocalTypeR.freeVarsOfBranches (LocalTypeDB.branchesFromDB ctx bs hclosed') := by
        simpa [LocalTypeDB.fromDB, LocalTypeR.freeVars] using hv
      exact hbs ctx hclosed' v hv'
    · intro p bs hbs ctx hclosed v hv
      have hclosed' : isClosedAtBranches ctx.length bs = true := by
        simpa [LocalTypeDB.isClosedAt] using hclosed
      have hv' :
          v ∈ LocalTypeR.freeVarsOfBranches (LocalTypeDB.branchesFromDB ctx bs hclosed') := by
        simpa [LocalTypeDB.fromDB, LocalTypeR.freeVars] using hv
      exact hbs ctx hclosed' v hv'
    · intro body hbody ctx hclosed v hv
      have hclosed' : body.isClosedAt (ctx.length + 1) = true := by
        simpa [LocalTypeDB.isClosedAt] using hclosed
      simp [LocalTypeDB.fromDB, LocalTypeR.freeVars] at hv
      rcases hv with ⟨hv, hne⟩
      have hsub := hbody (NameOnlyContext.cons (NameContext.freshName ctx) ctx) hclosed' v hv
      have : v ∈ ctx := by
        simpa [List.mem_cons, hne] using hsub
      exact this
    · intro ctx hclosed v hv
      simp [LocalTypeDB.branchesFromDB, LocalTypeR.freeVarsOfBranches] at hv
    · intro head tail hhead htail ctx hclosed v hv
      obtain ⟨l, t⟩ := head
      have hclosed' : t.isClosedAt ctx.length = true ∧
          isClosedAtBranches ctx.length tail = true := by
        simpa [isClosedAtBranches] using hclosed
      have hv' : v ∈ (t.fromDB ctx hclosed'.1).freeVars ∨
          v ∈ LocalTypeR.freeVarsOfBranches (LocalTypeDB.branchesFromDB ctx tail hclosed'.2) := by
        simpa [LocalTypeDB.branchesFromDB, LocalTypeR.freeVarsOfBranches, List.mem_append] using hv
      cases hv' with
      | inl hv_head =>
          exact hhead ctx hclosed'.1 v hv_head
      | inr hv_tail =>
          exact htail ctx hclosed'.2 v hv_tail
    · intro fst snd hsnd
      exact hsnd
  exact hrec ctx hclosed

-- fromDB Closedness at Empty Context

theorem fromDB_closed (t : LocalTypeDB) (_hclosed : t.isClosed = true) :
    ∀ hclosed' : t.isClosedAt (TypeContext.empty : NameContext).length = true,
      (t.fromDB TypeContext.empty hclosed').isClosed = true := by
  intro hclosed'
  have hsub := freeVars_fromDB_subset_ctx t TypeContext.empty hclosed'
  have hnil : (t.fromDB TypeContext.empty hclosed').freeVars = [] := by
    apply (List.eq_nil_iff_forall_not_mem).2
    intro v hv
    have hmem : v ∈ (TypeContext.empty : NameContext) := hsub v hv
    simp only [NameOnlyContext.mem_iff_mem_names, TypeContext.names_empty, List.not_mem_nil] at hmem
  simp [LocalTypeR.isClosed, hnil]

-- toDB? succeeds for closed terms

theorem toDB?_some_of_covers (t : LocalTypeR) (ctx : Context)
    (hcov : Context.Covers ctx t) :
    ∃ db, t.toDB? ctx = some db ∧ db.isClosedAt ctx.length = true := by
  let P1 : LocalTypeR → Prop :=
    fun t =>
      ∀ ctx, Context.Covers ctx t → ∃ db, t.toDB? ctx = some db ∧ db.isClosedAt ctx.length = true
  let P2 : List BranchR → Prop :=
    fun bs =>
      ∀ ctx, (∀ l _vt t, (l, _vt, t) ∈ bs → Context.Covers ctx t) →
        ∃ dbs, LocalTypeR.branchesToDB? ctx bs = some dbs ∧
          isClosedAtBranches ctx.length dbs = true
  let P3 : BranchR → Prop :=
    fun b =>
      ∀ ctx, Context.Covers ctx b.2.2 → ∃ db, b.2.2.toDB? ctx = some db ∧ db.isClosedAt ctx.length = true
  let P4 : Option ValType × LocalTypeR → Prop :=
    fun b =>
      ∀ ctx, Context.Covers ctx b.2 → ∃ db, b.2.toDB? ctx = some db ∧ db.isClosedAt ctx.length = true

  -- toDB? Success: Structural Recursion Setup

  have hrec : P1 t := by
    refine (SessionTypes.LocalTypeR.LocalTypeR.rec
      (motive_1 := P1) (motive_2 := P2) (motive_3 := P3) (motive_4 := P4)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ t)
    · intro ctx hcov
      refine ⟨LocalTypeDB.end, ?_, ?_⟩
      · simp [LocalTypeR.toDB?]
      · simp [LocalTypeDB.isClosedAt]

    -- toDB? Success: send/recv/μ Cases

    · intro p bs hbs ctx hcov
      have hcov' : ∀ l _vt t, (l, _vt, t) ∈ bs → Context.Covers ctx t := by
        intro l _vt t hmem v hv
        apply hcov v
        have : v ∈ LocalTypeR.freeVarsOfBranches bs := by
          have : v ∈ bs.flatMap (fun (_, _, t) => t.freeVars) := by
            refine List.mem_flatMap.mpr ?_
            refine ⟨(l, _vt, t), hmem, ?_⟩
            simpa using hv
          simpa [LocalTypeR.freeVarsOfBranches_eq_flatMap] using this
        simpa [LocalTypeR.freeVars] using this
      obtain ⟨dbs, hdbs, hclosed⟩ := hbs ctx hcov'
      refine ⟨LocalTypeDB.send p dbs, ?_, ?_⟩
      · simp [LocalTypeR.toDB?, hdbs]
      · simpa [LocalTypeDB.isClosedAt] using hclosed
    · intro p bs hbs ctx hcov
      have hcov' : ∀ l _vt t, (l, _vt, t) ∈ bs → Context.Covers ctx t := by
        intro l _vt t hmem v hv
        apply hcov v
        have : v ∈ LocalTypeR.freeVarsOfBranches bs := by
          have : v ∈ bs.flatMap (fun (_, _, t) => t.freeVars) := by
            refine List.mem_flatMap.mpr ?_
            refine ⟨(l, _vt, t), hmem, ?_⟩
            simpa using hv
          simpa [LocalTypeR.freeVarsOfBranches_eq_flatMap] using this
        simpa [LocalTypeR.freeVars] using this
      obtain ⟨dbs, hdbs, hclosed⟩ := hbs ctx hcov'
      refine ⟨LocalTypeDB.recv p dbs, ?_, ?_⟩
      · simp [LocalTypeR.toDB?, hdbs]
      · simpa [LocalTypeDB.isClosedAt] using hclosed
    · intro t body hbody ctx hcov
      have hcov' : Context.Covers (NameOnlyContext.cons t ctx) body := by
        intro v hv
        by_cases hvt : v = t
        · simp only [hvt, NameOnlyContext.mem_cons_self]
        · have hmem : v ∈ body.freeVars := hv
          have : v ∈ (LocalTypeR.mu t body).freeVars := by
            simp [LocalTypeR.freeVars, hmem, hvt]
          have hmem_ctx : v ∈ ctx := hcov v this
          exact NameOnlyContext.mem_cons_of_mem v t ctx hmem_ctx
      obtain ⟨db, hdb, hclosed⟩ := hbody (NameOnlyContext.cons t ctx) hcov'
      refine ⟨LocalTypeDB.mu db, ?_, ?_⟩
      · simp [LocalTypeR.toDB?, hdb]
      · simp only [LocalTypeDB.isClosedAt, NameOnlyContext.cons_length] at hclosed ⊢
        exact hclosed

    -- toDB? Success: var and branch-list Cases

    · intro v ctx hcov
      have hv : v ∈ ctx := by
        apply hcov
        simp [LocalTypeR.freeVars]
      obtain ⟨i, hidx⟩ := indexOf_eq_some_of_mem (ctx := ctx) (v := v) hv
      refine ⟨LocalTypeDB.var i, ?_, ?_⟩
      · simp only [LocalTypeR.toDB?]
        rw [Context.indexOf_eq] at hidx
        simp only [hidx, Option.map]
      · have hlt := indexOf_lt_length (ctx := ctx) (v := v) (i := i) hidx
        simp [LocalTypeDB.isClosedAt, hlt]
    · intro ctx hcov
      refine ⟨[], ?_, ?_⟩
      · simp [LocalTypeR.branchesToDB?]
      · simp [isClosedAtBranches]
    · intro head tail hhead htail ctx hcov
      obtain ⟨l, _vt, t⟩ := head
      have hcov_t : Context.Covers ctx t := hcov l _vt t (by simp)
      have hcov_tl : ∀ l _vt t, (l, _vt, t) ∈ tail → Context.Covers ctx t :=
        fun l _vt t hmem => hcov l _vt t (List.mem_cons_of_mem _ hmem)
      obtain ⟨db, hdb, hclosed⟩ := hhead ctx hcov_t
      obtain ⟨dbs, hdbs, hclosedbs⟩ := htail ctx hcov_tl
      refine ⟨(l, db) :: dbs, ?_, ?_⟩
      · simp [LocalTypeR.branchesToDB?, hdb, hdbs]
      · simp [isClosedAtBranches, hclosed, hclosedbs]
    · intro fst snd hsnd
      exact hsnd
    · intro fst snd hsnd
      exact hsnd
  exact hrec ctx hcov

-- toDB? Success for Branch Lists and Empty Context

theorem branchesToDB?_some_of_covers (bs : List BranchR) (ctx : Context)
    (hcov : ∀ l _vt t, (l, _vt, t) ∈ bs → Context.Covers ctx t) :
    ∃ dbs, LocalTypeR.branchesToDB? ctx bs = some dbs ∧
          isClosedAtBranches ctx.length dbs = true := by
  induction bs with
  | nil =>
      refine ⟨[], ?_, ?_⟩
      · simp [LocalTypeR.branchesToDB?]
      · simp [isClosedAtBranches]
  | cons hd tl ih =>
      obtain ⟨l, _vt, t⟩ := hd
      have hcov_t : Context.Covers ctx t := hcov l _vt t (by simp)
      have hcov_tl : ∀ l _vt t, (l, _vt, t) ∈ tl → Context.Covers ctx t :=
        fun l _vt t hmem => hcov l _vt t (List.mem_cons_of_mem _ hmem)
      obtain ⟨db, hdb, hclosed⟩ := toDB?_some_of_covers t ctx hcov_t
      obtain ⟨dbs, hdbs, hclosedbs⟩ := ih hcov_tl
      refine ⟨(l, db) :: dbs, ?_, ?_⟩
      · simp [LocalTypeR.branchesToDB?, hdb, hdbs]
      · simp [isClosedAtBranches, hclosed, hclosedbs]

theorem toDB_closed (t : LocalTypeR) (hclosed : t.isClosed = true) :
    ∃ db, t.toDB? TypeContext.empty = some db ∧ db.isClosed = true := by
  have hcov : Context.Covers TypeContext.empty t := Context.covers_of_closed TypeContext.empty t hclosed
  obtain ⟨db, hdb, hcloseddb⟩ := toDB?_some_of_covers t TypeContext.empty hcov
  refine ⟨db, hdb, ?_⟩
  simp only [LocalTypeDB.isClosed, TypeContext.length_empty] at hcloseddb ⊢
  exact hcloseddb

-- Roundtrip (fromDB then toDB?)

theorem toDB_fromDB_roundtrip_generated (t : LocalTypeDB) (ctx : NameContext)
    (hgen : GeneratedContext ctx) (hclosed : t.isClosedAt ctx.length = true) :
    (t.fromDB ctx hclosed).toDB? ctx = some t := by
  let P1 : LocalTypeDB → Prop :=
    fun t =>
      ∀ ctx, GeneratedContext ctx →
        (hclosed : t.isClosedAt ctx.length = true) →
          (t.fromDB ctx hclosed).toDB? ctx = some t
  let P2 : List (Label × LocalTypeDB) → Prop :=
    fun bs =>
      ∀ ctx, GeneratedContext ctx →
        (hclosed : isClosedAtBranches ctx.length bs = true) →
          LocalTypeR.branchesToDB? ctx (LocalTypeDB.branchesFromDB ctx bs hclosed) = some bs
  let P3 : Label × LocalTypeDB → Prop :=
    fun b =>
      ∀ ctx, GeneratedContext ctx →
        (hclosed : b.2.isClosedAt ctx.length = true) →
          (b.2.fromDB ctx hclosed).toDB? ctx = some b.2

  -- Roundtrip: Structural Recursion Setup

  have hrec : P1 t := by
    refine (LocalTypeDB.rec (motive_1 := P1) (motive_2 := P2) (motive_3 := P3)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ t)
    · intro ctx hgen hclosed
      simp [LocalTypeDB.fromDB, LocalTypeR.toDB?]
    · intro n ctx hgen hclosed
      have hlt : n < ctx.length := by
        simpa [LocalTypeDB.isClosedAt] using hclosed
      obtain ⟨v, hget⟩ := get?_some_of_lt (ctx := ctx) (i := n) hlt
      have hnodup : ctx.Nodup := generated_nodup ctx hgen
      have hidx : Context.indexOf ctx v = some n := get_indexOf_roundtrip ctx n v hnodup hget
      have hfrom : LocalTypeDB.fromDB ctx (.var n) hclosed = LocalTypeR.var v :=
        fromDB_var_of_get ctx n hclosed v hget
      simp [hfrom, LocalTypeR.toDB?]
      rw [Context.indexOf_eq] at hidx
      simp [hidx]

    -- Roundtrip: send/recv/μ Cases

    · intro p bs hbs ctx hgen hclosed
      have hclosed' : isClosedAtBranches ctx.length bs = true := by
        simpa [LocalTypeDB.isClosedAt] using hclosed
      have hbs' := hbs ctx hgen hclosed'
      simp [LocalTypeDB.fromDB, LocalTypeR.toDB?, hbs']
    · intro p bs hbs ctx hgen hclosed
      have hclosed' : isClosedAtBranches ctx.length bs = true := by
        simpa [LocalTypeDB.isClosedAt] using hclosed
      have hbs' := hbs ctx hgen hclosed'
      simp [LocalTypeDB.fromDB, LocalTypeR.toDB?, hbs']
    · intro body hbody ctx hgen hclosed
      have hclosed' : body.isClosedAt (ctx.length + 1) = true := by
        simpa [LocalTypeDB.isClosedAt] using hclosed
      have hgen' : GeneratedContext (NameOnlyContext.cons (NameContext.freshName ctx) ctx) :=
        GeneratedContext.cons hgen
      have hbody' := hbody (ctx := NameOnlyContext.cons (NameContext.freshName ctx) ctx) hgen' hclosed'
      simp [LocalTypeDB.fromDB, LocalTypeR.toDB?, hbody']
    · intro ctx hgen hclosed
      simp [LocalTypeDB.branchesFromDB, LocalTypeR.branchesToDB?]
    · intro head tail hhead htail ctx hgen hclosed
      obtain ⟨l, t⟩ := head
      have hclosed' : t.isClosedAt ctx.length = true ∧ isClosedAtBranches ctx.length tail = true := by
        simpa [isClosedAtBranches] using hclosed
      have ht := hhead ctx hgen hclosed'.1
      have htl := htail ctx hgen hclosed'.2
      simp [LocalTypeDB.branchesFromDB, LocalTypeR.branchesToDB?, ht, htl]
    · intro fst snd hsnd ctx hgen hclosed
      exact hsnd ctx hgen hclosed
  exact hrec ctx hgen hclosed

-- Roundtrip for Branch Lists and Empty Context

theorem branches_toDB_fromDB_roundtrip_generated (bs : List (Label × LocalTypeDB)) (ctx : NameContext)
    (hgen : GeneratedContext ctx)
    (hclosed : isClosedAtBranches ctx.length bs = true) :
    LocalTypeR.branchesToDB? ctx (LocalTypeDB.branchesFromDB ctx bs hclosed) = some bs := by
  induction bs with
  | nil =>
      simp [LocalTypeDB.branchesFromDB, LocalTypeR.branchesToDB?]
  | cons hd tl ih =>
      obtain ⟨l, t⟩ := hd
      have hclosed' : t.isClosedAt ctx.length = true ∧ isClosedAtBranches ctx.length tl = true := by
        simpa [isClosedAtBranches] using hclosed
      have ht := toDB_fromDB_roundtrip_generated t ctx hgen hclosed'.1
      have htl := ih hclosed'.2
      simp [LocalTypeDB.branchesFromDB, LocalTypeR.branchesToDB?, ht, htl]

theorem toDB_fromDB_roundtrip_closed (t : LocalTypeDB) (_hclosed : t.isClosed = true) :
    ∀ hclosed' : t.isClosedAt (TypeContext.empty : NameContext).length = true,
      (t.fromDB TypeContext.empty hclosed').toDB? TypeContext.empty = some t := by
  intro hclosed'
  exact toDB_fromDB_roundtrip_generated t TypeContext.empty GeneratedContext.empty hclosed'

theorem branches_toDB_fromDB_roundtrip_closed (bs : List (Label × LocalTypeDB))
    (_hclosed : isClosedAtBranches 0 bs = true) :
  ∀ hclosed' : isClosedAtBranches (TypeContext.empty : NameContext).length bs = true,
    LocalTypeR.branchesToDB? TypeContext.empty
      (LocalTypeDB.branchesFromDB TypeContext.empty bs hclosed') = some bs := by
  intro hclosed'
  exact branches_toDB_fromDB_roundtrip_generated bs TypeContext.empty GeneratedContext.empty hclosed'

end SessionTypes.LocalTypeConvProofs
