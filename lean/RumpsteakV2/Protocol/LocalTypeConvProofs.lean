/-
# Conversion Proofs: LocalTypeR ↔ LocalTypeDB Roundtrip

This module provides proven theorems for the conversion between named (LocalTypeR)
and de Bruijn indexed (LocalTypeDB) representations of local types.

This file uses the canonical definitions from `RumpsteakV2.Protocol.LocalTypeConv`,
`LocalTypeR`, and `LocalTypeDB`.
-/

import Mathlib
import RumpsteakV2.Protocol.LocalTypeConvDefs

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace RumpsteakV2.Protocol.LocalTypeConvProofs

open RumpsteakV2.Protocol.GlobalType
open RumpsteakV2.Protocol.LocalTypeR
open RumpsteakV2.Protocol.LocalTypeDB
open RumpsteakV2.Protocol.LocalTypeConv

/-! ## Basic list helpers -/

lemma get?_mem {ctx : NameContext} {i : Nat} {v : String}
    (h : NameContext.get? ctx i = some v) : v ∈ ctx := by
  induction ctx generalizing i with
  | nil => cases h
  | cons a ctx ih =>
      cases i with
      | zero =>
          simp [NameContext.get?] at h
          simp [h]
      | succ i =>
          simp [NameContext.get?] at h
          exact Or.inr (ih h)

lemma get?_some_of_lt {ctx : NameContext} {i : Nat} (h : i < ctx.length) :
    ∃ v, NameContext.get? ctx i = some v := by
  induction ctx generalizing i with
  | nil => cases h
  | cons a ctx ih =>
      cases i with
      | zero => exact ⟨a, by simp [NameContext.get?]⟩
      | succ i =>
          have h' : i < ctx.length := by simpa using h
          obtain ⟨v, hv⟩ := ih h'
          exact ⟨v, by simp [NameContext.get?, hv]⟩

/-! ## IndexOf helpers -/

lemma indexOf_cons (a : String) (ctx : Context) (v : String) :
    Context.indexOf (a :: ctx) v =
      (if a = v then some 0 else Option.map Nat.succ (Context.indexOf ctx v)) := by
  by_cases h : a = v
  · subst h
    simp [Context.indexOf]
  · simp [Context.indexOf, h, List.findIdx?.go]

lemma indexOf_eq_none_iff_not_mem (ctx : Context) (v : String) :
    Context.indexOf ctx v = none ↔ v ∉ ctx := by
  induction ctx with
  | nil => simp [Context.indexOf]
  | cons a ctx ih =>
      by_cases h : a = v
      · subst h
        simp [indexOf_cons]
      · simp [indexOf_cons, h, ih, List.mem_cons, not_or]

lemma indexOf_lt_length {ctx : Context} {v : String} {i : Nat}
    (h : Context.indexOf ctx v = some i) : i < ctx.length := by
  induction ctx generalizing i with
  | nil => simp [Context.indexOf] at h
  | cons a ctx ih =>
      by_cases h' : a = v
      · subst h'
        simp [indexOf_cons] at h
        cases h
        simp
      · simp [indexOf_cons, h'] at h
        rcases h with ⟨i, rfl⟩
        have hlt := ih rfl
        simpa using Nat.succ_lt_succ hlt

lemma indexOf_get? {ctx : Context} {v : String} {i : Nat}
    (h : Context.indexOf ctx v = some i) : NameContext.get? ctx i = some v := by
  induction ctx generalizing i with
  | nil => simp [Context.indexOf] at h
  | cons a ctx ih =>
      by_cases h' : a = v
      · subst h'
        simp [indexOf_cons] at h
        cases h
        simp [NameContext.get?]
      · simp [indexOf_cons, h'] at h
        rcases h with ⟨i, rfl⟩
        simp [NameContext.get?, ih rfl]

lemma indexOf_eq_some_of_mem {ctx : Context} {v : String} (hmem : v ∈ ctx) :
    ∃ i, Context.indexOf ctx v = some i := by
  by_cases hnone : Context.indexOf ctx v = none
  · have : v ∉ ctx := (indexOf_eq_none_iff_not_mem _ _).1 hnone
    contradiction
  · cases hidx : Context.indexOf ctx v with
    | none => cases hnone (by simpa [hidx])
    | some i => exact ⟨i, hidx⟩


lemma get?_inj_of_nodup {ctx : NameContext} (hnd : ctx.Nodup) {i j : Nat} {v : String}
    (hi : NameContext.get? ctx i = some v) (hj : NameContext.get? ctx j = some v) : i = j := by
  induction ctx generalizing i j with
  | nil => cases hi
  | cons a ctx ih =>
      cases i <;> cases j <;> simp [NameContext.get?] at hi hj
      · rfl
      · have : v ∈ ctx := by
          exact get?_mem hj
        exact (hnd.not_mem this).elim
      · have : v ∈ ctx := by
          exact get?_mem hi
        exact (hnd.not_mem this).elim
      · have hnd' : ctx.Nodup := hnd.tail
        exact congrArg Nat.succ (ih hnd' hi hj)

lemma get_indexOf_roundtrip (ctx : NameContext) (i : Nat) (v : String)
    (h_nodup : ctx.Nodup) (h_get : NameContext.get? ctx i = some v) :
    Context.indexOf ctx v = some i := by
  have hmem : v ∈ ctx := get?_mem h_get
  obtain ⟨j, hidx⟩ := indexOf_eq_some_of_mem (ctx := ctx) (v := v) hmem
  have hget_j := indexOf_get? (ctx := ctx) (v := v) (i := j) hidx
  have hij := get?_inj_of_nodup h_nodup h_get hget_j
  subst hij
  exact hidx

lemma indexOf_inj {ctx : Context} {x y : String} {i : Nat}
    (hx : Context.indexOf ctx x = some i) (hy : Context.indexOf ctx y = some i) : x = y := by
  have hx' := indexOf_get? (ctx := ctx) (v := x) (i := i) hx
  have hy' := indexOf_get? (ctx := ctx) (v := y) (i := i) hy
  simpa [hx'] using hy'


lemma get?_append_right (xs ys : NameContext) (n : Nat) :
    NameContext.get? (xs ++ ys) (xs.length + n) = NameContext.get? ys n := by
  induction xs generalizing n with
  | nil => simp [NameContext.get?]
  | cons a xs ih =>
      simp [NameContext.get?, ih, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

lemma indexOf_append_x_le (pref ctx : Context) (x : String) :
    ∃ k, Context.indexOf (pref ++ x :: ctx) x = some k ∧ k ≤ pref.length := by
  induction pref with
  | nil =>
      refine ⟨0, ?_, by simp⟩
      simp [Context.indexOf]
  | cons a pref ih =>
      by_cases hax : a = x
      · subst hax
        refine ⟨0, ?_, by simp⟩
        simp [Context.indexOf]
      · obtain ⟨k, hk, hkle⟩ := ih
        refine ⟨k + 1, ?_, ?_⟩
        · simp [indexOf_cons, hax, hk]
        · exact Nat.succ_le_succ hkle

/-! ## fromDB? correctness for closed terms -/

mutual
  theorem fromDB?_eq_fromDB_all_ctx (t : LocalTypeDB) (ctx : NameContext)
      (hclosed : t.isClosedAt ctx.length = true) :
      t.fromDB? ctx = some (t.fromDB ctx) := by
    cases t with
    | end => rfl
    | var n =>
        have hlt : n < ctx.length := by
          simpa [LocalTypeDB.isClosedAt] using hclosed
        obtain ⟨v, hget⟩ := get?_some_of_lt (ctx := ctx) (i := n) hlt
        simp [LocalTypeDB.fromDB?, LocalTypeDB.fromDB, hget]
    | send p bs =>
        have hclosed' : LocalTypeDB.isClosedAtBranches ctx.length bs = true := by
          simpa [LocalTypeDB.isClosedAt] using hclosed
        have hbs : branchesFromDB? ctx bs = some (branchesFromDB ctx bs) :=
          branchesFromDB?_eq_branchesFromDB bs ctx hclosed'
        simp [LocalTypeDB.fromDB?, LocalTypeDB.fromDB, hbs]
    | recv p bs =>
        have hclosed' : LocalTypeDB.isClosedAtBranches ctx.length bs = true := by
          simpa [LocalTypeDB.isClosedAt] using hclosed
        have hbs : branchesFromDB? ctx bs = some (branchesFromDB ctx bs) :=
          branchesFromDB?_eq_branchesFromDB bs ctx hclosed'
        simp [LocalTypeDB.fromDB?, LocalTypeDB.fromDB, hbs]
    | mu body =>
        have hclosed' : body.isClosedAt (ctx.length + 1) = true := by
          simpa [LocalTypeDB.isClosedAt] using hclosed
        have hbody := fromDB?_eq_fromDB_all_ctx body (NameContext.freshName ctx :: ctx) hclosed'
        simp [LocalTypeDB.fromDB?, LocalTypeDB.fromDB, hbody]

  theorem branchesFromDB?_eq_branchesFromDB (bs : List (Label × LocalTypeDB)) (ctx : NameContext)
      (hclosed : LocalTypeDB.isClosedAtBranches ctx.length bs = true) :
      branchesFromDB? ctx bs = some (branchesFromDB ctx bs) := by
    induction bs with
    | nil => rfl
    | cons hd tl ih =>
        obtain ⟨l, t⟩ := hd
        have h_t_closed : t.isClosedAt ctx.length = true := by
          simpa [LocalTypeDB.isClosedAtBranches] using hclosed
        have h_tl_closed : LocalTypeDB.isClosedAtBranches ctx.length tl = true := by
          simpa [LocalTypeDB.isClosedAtBranches] using hclosed
        have ht := fromDB?_eq_fromDB_all_ctx t ctx h_t_closed
        have htl := ih h_tl_closed
        simp [LocalTypeDB.branchesFromDB?, LocalTypeDB.branchesFromDB, ht, htl]
end

theorem fromDB?_eq_fromDB_closed (t : LocalTypeDB) (hclosed : t.isClosed = true) :
    t.fromDB? [] = some (t.fromDB []) := by
  have hclosed' : t.isClosedAt 0 = true := by
    simpa [LocalTypeDB.isClosed] using hclosed
  simpa using (fromDB?_eq_fromDB_all_ctx t [] hclosed')

/-! ## fromDB closedness -/

lemma freeVars_fromDB_subset_ctx (t : LocalTypeDB) (ctx : NameContext)
    (hclosed : t.isClosedAt ctx.length = true) :
    ∀ v, v ∈ (t.fromDB ctx).freeVars → v ∈ ctx := by
  intro v hv
  induction t generalizing ctx with
  | end => simp [LocalTypeR.freeVars] at hv
  | var n =>
      have hlt : n < ctx.length := by
        simpa [LocalTypeDB.isClosedAt] using hclosed
      obtain ⟨name, hget⟩ := get?_some_of_lt (ctx := ctx) (i := n) hlt
      simp [LocalTypeDB.fromDB, NameContext.get?, hget, LocalTypeR.freeVars] at hv
      subst hv
      exact get?_mem hget
  | send p bs ih =>
      have hclosed' : LocalTypeDB.isClosedAtBranches ctx.length bs = true := by
        simpa [LocalTypeDB.isClosedAt] using hclosed
      -- analyze membership in concatenated freeVarsOfBranches
      induction bs generalizing hv with
      | nil => cases hv
      | cons hd tl ihb =>
          obtain ⟨l, t⟩ := hd
          simp [LocalTypeDB.fromDB, LocalTypeR.freeVars, LocalTypeR.freeVarsOfBranches] at hv
          rcases hv with hv | hv
          · -- from head branch
            have h_t_closed : t.isClosedAt ctx.length = true := by
              simpa [LocalTypeDB.isClosedAtBranches] using hclosed'
            exact ih t ctx h_t_closed _ hv
          · -- from tail branches
            have h_tl_closed : LocalTypeDB.isClosedAtBranches ctx.length tl = true := by
              simpa [LocalTypeDB.isClosedAtBranches] using hclosed'
            exact ihb h_tl_closed hv
  | recv p bs ih =>
      have hclosed' : LocalTypeDB.isClosedAtBranches ctx.length bs = true := by
        simpa [LocalTypeDB.isClosedAt] using hclosed
      induction bs generalizing hv with
      | nil => cases hv
      | cons hd tl ihb =>
          obtain ⟨l, t⟩ := hd
          simp [LocalTypeDB.fromDB, LocalTypeR.freeVars, LocalTypeR.freeVarsOfBranches] at hv
          rcases hv with hv | hv
          · have h_t_closed : t.isClosedAt ctx.length = true := by
              simpa [LocalTypeDB.isClosedAtBranches] using hclosed'
            exact ih t ctx h_t_closed _ hv
          · have h_tl_closed : LocalTypeDB.isClosedAtBranches ctx.length tl = true := by
              simpa [LocalTypeDB.isClosedAtBranches] using hclosed'
            exact ihb h_tl_closed hv
  | mu body ih =>
      have hclosed' : body.isClosedAt (ctx.length + 1) = true := by
        simpa [LocalTypeDB.isClosedAt] using hclosed
      -- freeVars of mu filters out the binder
      simp [LocalTypeDB.fromDB, LocalTypeR.freeVars] at hv
      rcases hv with ⟨hv, hne⟩
      have hsub := ih body (NameContext.freshName ctx :: ctx) hclosed' v hv
      cases hsub with
      | head =>
          contradiction
      | tail hmem =>
          exact hmem

theorem fromDB_closed (t : LocalTypeDB) (hclosed : t.isClosed = true) :
    (t.fromDB []).isClosed = true := by
  have hclosed' : t.isClosedAt 0 = true := by
    simpa [LocalTypeDB.isClosed] using hclosed
  have hsub := freeVars_fromDB_subset_ctx t [] hclosed'
  apply (List.isEmpty_eq_true _).2
  intro v hv
  have : v ∈ ([] : List String) := hsub v hv
  simpa using this

/-! ## toDB? succeeds for closed terms -/

mutual
  theorem toDB?_some_of_covers (t : LocalTypeR) (ctx : Context)
      (hcov : Context.Covers ctx t) :
      ∃ db, t.toDB? ctx = some db ∧ db.isClosedAt ctx.length = true := by
    cases t with
    | end =>
        exact ⟨LocalTypeDB.end, rfl, by simp [LocalTypeDB.isClosedAt]⟩
    | var v =>
        have hv : v ∈ ctx := by
          apply hcov
          simp [LocalTypeR.freeVars]
        obtain ⟨i, hidx⟩ := indexOf_eq_some_of_mem (ctx := ctx) (v := v) hv
        refine ⟨LocalTypeDB.var i, ?_, ?_⟩
        · simp [LocalTypeR.toDB?, hidx]
        · have hlt := indexOf_lt_length (ctx := ctx) (v := v) (i := i) hidx
          simp [LocalTypeDB.isClosedAt, hlt]
    | send p bs =>
        have hcov' : ∀ l t, (l, t) ∈ bs → Context.Covers ctx t := by
          intro l t hmem v hv
          apply hcov v
          -- freeVars of branch are in freeVarsOfBranches
          have : v ∈ LocalTypeR.freeVarsOfBranches bs := by
            -- membership from branch
            induction bs with
            | nil => cases hmem
            | cons hd tl ih =>
                cases hmem with
                | head =>
                    simp [LocalTypeR.freeVarsOfBranches, hv]
                | tail hmem' =>
                    have h' := ih hmem'
                    simp [LocalTypeR.freeVarsOfBranches, h', hv]
          simpa [LocalTypeR.freeVars] using this
        obtain ⟨dbs, hdbs, hclosed⟩ :=
          branchesToDB?_some_of_covers bs ctx hcov'
        refine ⟨LocalTypeDB.send p dbs, ?_, ?_⟩
        · simp [LocalTypeR.toDB?, hdbs]
        · simpa [LocalTypeDB.isClosedAt]
    | recv p bs =>
        have hcov' : ∀ l t, (l, t) ∈ bs → Context.Covers ctx t := by
          intro l t hmem v hv
          apply hcov v
          have : v ∈ LocalTypeR.freeVarsOfBranches bs := by
            induction bs with
            | nil => cases hmem
            | cons hd tl ih =>
                cases hmem with
                | head =>
                    simp [LocalTypeR.freeVarsOfBranches, hv]
                | tail hmem' =>
                    have h' := ih hmem'
                    simp [LocalTypeR.freeVarsOfBranches, h', hv]
          simpa [LocalTypeR.freeVars] using this
        obtain ⟨dbs, hdbs, hclosed⟩ :=
          branchesToDB?_some_of_covers bs ctx hcov'
        refine ⟨LocalTypeDB.recv p dbs, ?_, ?_⟩
        · simp [LocalTypeR.toDB?, hdbs]
        · simpa [LocalTypeDB.isClosedAt]
    | mu t body =>
        have hcov' : Context.Covers (t :: ctx) body := by
          intro v hv
          by_cases hvt : v = t
          · simp [hvt]
          · -- free vars of mu body are filtered, so v in body.freeVars implies v in ctx
            have hmem : v ∈ body.freeVars := hv
            have : v ∈ ctx := by
              -- v is free in mu, so must be free in body and not equal t; use hcov
              have : v ∈ (LocalTypeR.mu t body).freeVars := by
                simp [LocalTypeR.freeVars, hmem, hvt]
              exact hcov v this
            simp [hvt, this]
        obtain ⟨db, hdb, hclosed⟩ := toDB?_some_of_covers body (t :: ctx) hcov'
        refine ⟨LocalTypeDB.mu db, ?_, ?_⟩
        · simp [LocalTypeR.toDB?, hdb]
        · simpa [LocalTypeDB.isClosedAt] using hclosed

  theorem branchesToDB?_some_of_covers (bs : List (Label × LocalTypeR)) (ctx : Context)
      (hcov : ∀ l t, (l, t) ∈ bs → Context.Covers ctx t) :
      ∃ dbs, LocalTypeR.branchesToDB? ctx bs = some dbs ∧
            LocalTypeDB.isClosedAtBranches ctx.length dbs = true := by
    induction bs with
    | nil => exact ⟨[], rfl, rfl⟩
    | cons hd tl ih =>
        obtain ⟨l, t⟩ := hd
        have hcov_t : Context.Covers ctx t := hcov l t (List.mem_cons_self _ _)
        have hcov_tl : ∀ l t, (l, t) ∈ tl → Context.Covers ctx t :=
          fun l t hmem => hcov l t (List.mem_cons_of_mem _ hmem)
        obtain ⟨db, hdb, hclosed⟩ := toDB?_some_of_covers t ctx hcov_t
        obtain ⟨dbs, hdbs, hclosedbs⟩ := ih hcov_tl
        refine ⟨(l, db) :: dbs, ?_, ?_⟩
        · simp [LocalTypeR.branchesToDB?, hdb, hdbs]
        · simp [LocalTypeDB.isClosedAtBranches, hclosed, hclosedbs]
end

theorem toDB_closed (t : LocalTypeR) (hclosed : t.isClosed = true) :
    ∃ db, t.toDB? [] = some db ∧ db.isClosed = true := by
  have hcov : Context.Covers [] t := Context.covers_of_closed [] t hclosed
  obtain ⟨db, hdb, hcloseddb⟩ := toDB?_some_of_covers t [] hcov
  refine ⟨db, hdb, ?_⟩
  simpa [LocalTypeDB.isClosed] using hcloseddb

/-! ## Roundtrip (fromDB then toDB?) -/

lemma branches_toDB_fromDB_roundtrip_closed (bs : List (Label × LocalTypeDB))
    (hclosed : LocalTypeDB.isClosedAtBranches 0 bs = true) :
    LocalTypeR.branchesToDB? [] (LocalTypeDB.branchesFromDB [] bs) = some bs := by
  induction bs with
  | nil => rfl
  | cons hd tl ih =>
      obtain ⟨l, t⟩ := hd
      have h_t_closed : t.isClosedAt 0 = true := by
        simpa [LocalTypeDB.isClosedAtBranches] using hclosed
      have h_tl_closed : LocalTypeDB.isClosedAtBranches 0 tl = true := by
        simpa [LocalTypeDB.isClosedAtBranches] using hclosed
      have ht := toDB_fromDB_roundtrip_closed t (by simpa [LocalTypeDB.isClosed] using h_t_closed)
      have htl := ih h_tl_closed
      simp [LocalTypeDB.branchesFromDB, LocalTypeR.branchesToDB?, ht, htl]


theorem toDB_fromDB_roundtrip_closed (t : LocalTypeDB) (hclosed : t.isClosed = true) :
    (t.fromDB []).toDB? [] = some t := by
  -- direct induction on closed DB terms
  have hclosed' : t.isClosedAt 0 = true := by
    simpa [LocalTypeDB.isClosed] using hclosed
  revert hclosed'
  induction t with
  | end => simp [LocalTypeDB.fromDB, LocalTypeR.toDB?]
  | var n =>
      -- impossible for closed terms at depth 0
      simp [LocalTypeDB.isClosedAt] at hclosed'
  | send p bs ih =>
      have hclosed' : LocalTypeDB.isClosedAtBranches 0 bs = true := by
        simpa [LocalTypeDB.isClosedAt] using hclosed'
      have hbs := branches_toDB_fromDB_roundtrip_closed bs hclosed'
      simp [LocalTypeDB.fromDB, LocalTypeR.toDB?, hbs]
  | recv p bs ih =>
      have hclosed' : LocalTypeDB.isClosedAtBranches 0 bs = true := by
        simpa [LocalTypeDB.isClosedAt] using hclosed'
      have hbs := branches_toDB_fromDB_roundtrip_closed bs hclosed'
      simp [LocalTypeDB.fromDB, LocalTypeR.toDB?, hbs]
  | mu body ih =>
      have hclosed' : body.isClosedAt 1 = true := by
        simpa [LocalTypeDB.isClosedAt] using hclosed'
      have hbody := ih hclosed'
      simp [LocalTypeDB.fromDB, LocalTypeR.toDB?, hbody]

/-! ## General roundtrip with adequate context -/

theorem toDB_fromDB_roundtrip (t : LocalTypeDB) (ctx : NameContext)
    (hnodup : ctx.Nodup)
    (hfreshAll : ∀ c, NameContext.freshName c ∉ c)
    (hclosed : t.isClosedAt ctx.length = true) :
    (t.fromDB ctx).toDB? ctx = some t := by
  -- mutual recursion on t and branches
  induction t generalizing ctx with
  | end => simp [LocalTypeDB.fromDB, LocalTypeR.toDB?]
  | var n =>
      have hlt : n < ctx.length := by
        simpa [LocalTypeDB.isClosedAt] using hclosed
      obtain ⟨v, hget⟩ := get?_some_of_lt (ctx := ctx) (i := n) hlt
      have hidx : Context.indexOf ctx v = some n := by
        have hnodup := hnodup
        exact get_indexOf_roundtrip ctx n v hnodup hget
      simp [LocalTypeDB.fromDB, LocalTypeR.toDB?, hget, hidx]
  | send p bs ih =>
      have hclosed' : LocalTypeDB.isClosedAtBranches ctx.length bs = true := by
        simpa [LocalTypeDB.isClosedAt] using hclosed
      have hbs := branches_toDB_fromDB_roundtrip bs ctx hnodup hfreshAll hclosed'
      simp [LocalTypeDB.fromDB, LocalTypeR.toDB?, hbs]
  | recv p bs ih =>
      have hclosed' : LocalTypeDB.isClosedAtBranches ctx.length bs = true := by
        simpa [LocalTypeDB.isClosedAt] using hclosed
      have hbs := branches_toDB_fromDB_roundtrip bs ctx hnodup hfreshAll hclosed'
      simp [LocalTypeDB.fromDB, LocalTypeR.toDB?, hbs]
  | mu body ih =>
      have hclosed' : body.isClosedAt (ctx.length + 1) = true := by
        simpa [LocalTypeDB.isClosedAt] using hclosed
      have hnodup' : (NameContext.freshName ctx :: ctx).Nodup := by
        apply List.nodup_cons.mpr
        exact ⟨hfreshAll ctx, hnodup⟩
      have hbody := ih (ctx := NameContext.freshName ctx :: ctx) hnodup' hfreshAll hclosed'
      simp [LocalTypeDB.fromDB, LocalTypeR.toDB?, hbody]

and branches_toDB_fromDB_roundtrip (bs : List (Label × LocalTypeDB)) (ctx : NameContext)
    (hnodup : ctx.Nodup)
    (hfreshAll : ∀ c, NameContext.freshName c ∉ c)
    (hclosed : LocalTypeDB.isClosedAtBranches ctx.length bs = true) :
    LocalTypeR.branchesToDB? ctx (LocalTypeDB.branchesFromDB ctx bs) = some bs := by
  induction bs with
  | nil => rfl
  | cons hd tl ih =>
      obtain ⟨l, t⟩ := hd
      have h_t_closed : t.isClosedAt ctx.length = true := by
        simpa [LocalTypeDB.isClosedAtBranches] using hclosed
      have h_tl_closed : LocalTypeDB.isClosedAtBranches ctx.length tl = true := by
        simpa [LocalTypeDB.isClosedAtBranches] using hclosed
      have ht := toDB_fromDB_roundtrip t ctx hnodup hfreshAll h_t_closed
      have htl := ih hnodup hfreshAll h_tl_closed
      simp [LocalTypeDB.branchesFromDB, LocalTypeR.branchesToDB?, ht, htl]

/-! ## Guardedness / contractiveness preservation -/

theorem isGuarded_toDB_shadowed_prefix (t : LocalTypeR) (pref ctx : Context) (x : String) (i : Nat)
    (db : LocalTypeDB) :
    Context.indexOf ctx x = some i →
    t.toDB? (pref ++ x :: ctx) = some db →
    db.isGuarded (i + pref.length + 1) = true := by
  intro hidx hdb
  induction t generalizing pref ctx i db with
  | end =>
      simp [LocalTypeR.toDB?, LocalTypeDB.isGuarded] at hdb
      simpa [hdb]
  | var v =>
      cases hvar : Context.indexOf (pref ++ x :: ctx) v with
      | none =>
          simp [LocalTypeR.toDB?, hvar] at hdb
      | some j =>
          simp [LocalTypeR.toDB?, hvar] at hdb
          subst hdb
          have hne : j ≠ i + pref.length + 1 := by
            intro hj
            have hidx_v : Context.indexOf (pref ++ x :: ctx) v = some (i + pref.length + 1) := by
              simpa [hj] using hvar
            have hget_v :=
              indexOf_get? (ctx := pref ++ x :: ctx) (v := v) (i := i + pref.length + 1) hidx_v
            have hget_x : NameContext.get? (pref ++ x :: ctx) (i + pref.length + 1) = some x := by
              have hidx' : i + pref.length + 1 = pref.length + (i + 1) := by
                simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
              calc
                NameContext.get? (pref ++ x :: ctx) (i + pref.length + 1)
                    = NameContext.get? (pref ++ x :: ctx) (pref.length + (i + 1)) := by
                        simp [hidx']
                _ = NameContext.get? (x :: ctx) (i + 1) := by
                      simpa using
                        (get?_append_right (xs := pref) (ys := x :: ctx) (n := i + 1))
                _ = NameContext.get? ctx i := by
                      simp [NameContext.get?]
                _ = some x := by
                      simpa using (indexOf_get? (ctx := ctx) (v := x) (i := i) hidx)
            have hvx : v = x := by
              have : (some v : Option String) = some x := by
                simpa [hget_x] using hget_v
              exact Option.some.inj this
            obtain ⟨k, hk, hkle⟩ := indexOf_append_x_le (pref := pref) (ctx := ctx) (x := x)
            have hk' : k = i + pref.length + 1 := by
              have : (some k : Option Nat) = some (i + pref.length + 1) := by
                simpa [hvx, hk] using hidx_v
              exact Option.some.inj this
            have hle : i + pref.length + 1 ≤ pref.length := by
              have hkle' : i + pref.length + 1 ≤ pref.length := by
                simpa [hk'] using hkle
              exact hkle'
            have hgt : pref.length < i + pref.length + 1 := by
              have : pref.length < pref.length + (i + 1) := by
                exact Nat.lt_add_of_pos_right _ (Nat.succ_pos _)
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this
            exact (Nat.not_le_of_gt hgt) hle
          simp [LocalTypeDB.isGuarded, hne]
  | send p bs ih =>
      simp [LocalTypeR.toDB?, LocalTypeDB.isGuarded] at hdb
      simpa [hdb]
  | recv p bs ih =>
      simp [LocalTypeR.toDB?, LocalTypeDB.isGuarded] at hdb
      simpa [hdb]
  | mu y body ih =>
      cases hbody : body.toDB? (y :: pref ++ x :: ctx) with
      | none =>
          simp [LocalTypeR.toDB?, hbody] at hdb
      | some db' =>
          simp [LocalTypeR.toDB?, hbody] at hdb
          subst hdb
          have hguard' :
              db'.isGuarded (i + (y :: pref).length + 1) = true := by
            have hbody' : body.toDB? ((y :: pref) ++ x :: ctx) = some db' := by
              simpa using hbody
            exact ih (pref := y :: pref) (ctx := ctx) (i := i) (db := db') hidx hbody'
          have hguard'' : db'.isGuarded (i + pref.length + 1 + 1) = true := by
            have : i + (y :: pref).length + 1 = i + pref.length + 1 + 1 := by
              simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
            simpa [this] using hguard'
          simpa [LocalTypeDB.isGuarded, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hguard''

theorem isGuarded_toDB (t : LocalTypeR) (ctx : Context) (x : String) (i : Nat) (db : LocalTypeDB) :
    t.isGuarded x = true →
    ctx.indexOf x = some i →
    t.toDB? ctx = some db →
    db.isGuarded i = true := by
  intro hguard hidx hdb
  induction t generalizing ctx i db with
  | end =>
      simp [LocalTypeR.toDB?, LocalTypeDB.isGuarded] at hdb
      simpa [hdb]
  | var v =>
      simp [LocalTypeR.isGuarded] at hguard
      cases hvar : Context.indexOf ctx v with
      | none => simp [LocalTypeR.toDB?, hvar] at hdb
      | some j =>
          simp [LocalTypeR.toDB?, hvar] at hdb
          subst hdb
          have hne : j ≠ i := by
            intro hij
            have hx := indexOf_get? (ctx := ctx) (v := x) (i := i) hidx
            have hv := indexOf_get? (ctx := ctx) (v := v) (i := i) (by simpa [hij] using hvar)
            have : x = v := by simpa [hx] using hv
            exact hguard (this.symm)
          simp [LocalTypeDB.isGuarded, hne]
  | send p bs ih =>
      simp [LocalTypeR.toDB?, LocalTypeDB.isGuarded] at hdb
      simpa [hdb]
  | recv p bs ih =>
      simp [LocalTypeR.toDB?, LocalTypeDB.isGuarded] at hdb
      simpa [hdb]
  | mu y body ih =>
      by_cases hxy : x = y
      · subst hxy
        cases hbody : body.toDB? (x :: ctx) with
        | none =>
            simp [LocalTypeR.toDB?, hbody] at hdb
        | some db' =>
            have hdb' : db = LocalTypeDB.mu db' := by
              simp [LocalTypeR.toDB?, hbody] at hdb
              exact hdb
            subst hdb'
            have hguard' : db'.isGuarded (i + 1) = true := by
              exact isGuarded_toDB_shadowed_prefix (t := body) (pref := []) (ctx := ctx)
                (x := x) (i := i) (db := db') hidx (by simpa [hbody])
            simpa [LocalTypeDB.isGuarded] using hguard'
      · have hguard_body : body.isGuarded x = true := by
          simp [LocalTypeR.isGuarded, hxy] at hguard
          exact hguard
        have hidx' : Context.indexOf (y :: ctx) x = some (i + 1) := by
          have hne : y ≠ x := by exact hxy
          simp [indexOf_cons, hne, hidx]
        cases hbody : body.toDB? (y :: ctx) with
        | none =>
            simp [LocalTypeR.toDB?, hbody] at hdb
        | some db' =>
            have hdb' : db = LocalTypeDB.mu db' := by
              simp [LocalTypeR.toDB?, hbody] at hdb
              exact hdb
            subst hdb'
            have hguard' := ih (ctx := y :: ctx) (i := i + 1) (db := db') hguard_body hidx' (by simpa [hbody])
            simpa [LocalTypeDB.isGuarded] using hguard'


theorem isContractive_toDB (t : LocalTypeR) (ctx : Context) (db : LocalTypeDB) :
    t.isContractive = true →
    t.toDB? ctx = some db →
    db.isContractive = true := by
  intro hcontr hdb
  induction t generalizing ctx db with
  | end =>
      simp [LocalTypeR.toDB?, LocalTypeDB.isContractive] at hdb
      simpa [hdb]
  | var v =>
      simp [LocalTypeR.toDB?, LocalTypeDB.isContractive] at hdb
      simpa [hdb]
  | send p bs ih =>
      have hbs : isContractiveBranches bs = true := by
        simpa [LocalTypeR.isContractive] using hcontr
      cases hdbs : LocalTypeR.branchesToDB? ctx bs with
      | none => simp [LocalTypeR.toDB?, hdbs] at hdb
      | some dbs =>
          simp [LocalTypeR.toDB?, hdbs] at hdb
          subst hdb
          -- show branches contractive
          induction bs generalizing dbs with
          | nil => simp [LocalTypeDB.isContractive]
          | cons hd tl ih' =>
              obtain ⟨l, t⟩ := hd
              cases dbs with
              | nil => simp at hdbs
              | cons hd' tl' =>
                  obtain ⟨l', t'⟩ := hd'
                  simp [LocalTypeR.branchesToDB?, hdbs] at hdbs
                  have htcontr : t.isContractive = true := by
                    simpa [LocalTypeR.isContractive] using hbs
                  have htdb : t.toDB? ctx = some t' := by
                    simpa [LocalTypeR.branchesToDB?] using hdbs.1
                  have ht := ih (ctx := ctx) (db := t') htcontr htdb
                  have htl : isContractiveBranches tl = true := by
                    simpa [LocalTypeR.isContractive] using hbs
                  have htl' := ih' htl hdbs.2
                  simp [LocalTypeDB.isContractive, ht, htl']
  | recv p bs ih =>
      have hbs : isContractiveBranches bs = true := by
        simpa [LocalTypeR.isContractive] using hcontr
      cases hdbs : LocalTypeR.branchesToDB? ctx bs with
      | none => simp [LocalTypeR.toDB?, hdbs] at hdb
      | some dbs =>
          simp [LocalTypeR.toDB?, hdbs] at hdb
          subst hdb
          induction bs generalizing dbs with
          | nil => simp [LocalTypeDB.isContractive]
          | cons hd tl ih' =>
              obtain ⟨l, t⟩ := hd
              cases dbs with
              | nil => simp at hdbs
              | cons hd' tl' =>
                  obtain ⟨l', t'⟩ := hd'
                  simp [LocalTypeR.branchesToDB?, hdbs] at hdbs
                  have htcontr : t.isContractive = true := by
                    simpa [LocalTypeR.isContractive] using hbs
                  have htdb : t.toDB? ctx = some t' := by
                    simpa [LocalTypeR.branchesToDB?] using hdbs.1
                  have ht := ih (ctx := ctx) (db := t') htcontr htdb
                  have htl : isContractiveBranches tl = true := by
                    simpa [LocalTypeR.isContractive] using hbs
                  have htl' := ih' htl hdbs.2
                  simp [LocalTypeDB.isContractive, ht, htl']
  | mu x body ih =>
      simp [LocalTypeR.isContractive] at hcontr
      rcases hcontr with ⟨hguard, hbody⟩
      cases hbody' : body.toDB? (x :: ctx) with
      | none => simp [LocalTypeR.toDB?, hbody'] at hdb
      | some db' =>
          simp [LocalTypeR.toDB?, hbody'] at hdb
          subst hdb
          have hguard' : db'.isGuarded 0 = true := by
            have hidx : Context.indexOf (x :: ctx) x = some 0 := by
              simp [Context.indexOf]
            exact isGuarded_toDB (t := body) (ctx := x :: ctx) (x := x) (i := 0) (db := db') hguard hidx (by simpa [hbody'])
          have hbody' := ih (ctx := x :: ctx) (db := db') hbody (by simpa [hbody'])
          simp [LocalTypeDB.isContractive, hguard', hbody']


/-! ## Contractiveness preservation for fromDB -/

lemma isGuarded_fromDB_fresh (t : LocalTypeDB) (ctx : NameContext)
    (hfreshAll : ∀ c, NameContext.freshName c ∉ c)
    (hclosed : t.isClosedAt (ctx.length + 1) = true)
    (hguard : t.isGuarded 0 = true) :
    (t.fromDB (NameContext.freshName ctx :: ctx)).isGuarded (NameContext.freshName ctx) = true := by
  -- proof by induction on DB structure
  induction t generalizing ctx with
  | end => simp [LocalTypeDB.fromDB, LocalTypeR.isGuarded]
  | var n =>
      have hne : n ≠ 0 := by
        simpa [LocalTypeDB.isGuarded] using hguard
      cases n with
      | zero => cases hne rfl
      | succ n =>
          have hlt : n.succ < ctx.length + 1 := by
            simpa [LocalTypeDB.isClosedAt] using hclosed
          obtain ⟨v, hget⟩ := get?_some_of_lt (ctx := NameContext.freshName ctx :: ctx) (i := n.succ) hlt
          have hmem : v ∈ ctx := by
            -- index >= 1, so v comes from tail
            simpa [NameContext.get?, hget] using get?_mem hget
          have hneq : v ≠ NameContext.freshName ctx := by
            intro h_eq
            have : NameContext.freshName ctx ∈ ctx := by
              simpa [h_eq] using hmem
            exact (hfreshAll ctx) this
          simp [LocalTypeDB.fromDB, NameContext.get?, hget, LocalTypeR.isGuarded, hneq]
  | send p bs ih =>
      simp [LocalTypeDB.fromDB, LocalTypeR.isGuarded]
  | recv p bs ih =>
      simp [LocalTypeDB.fromDB, LocalTypeR.isGuarded]
  | mu body ih =>
      have hclosed' : body.isClosedAt (ctx.length + 2) = true := by
        simpa [LocalTypeDB.isClosedAt] using hclosed
      have hguard' : body.isGuarded 1 = true := by
        simpa [LocalTypeDB.isGuarded] using hguard
      -- binder is freshName ctx, shift guardness
      have ih' := ih (ctx := NameContext.freshName ctx :: ctx) hfreshAll hclosed' hguard'
      simp [LocalTypeDB.fromDB, LocalTypeR.isGuarded, ih']


theorem isContractive_fromDB (t : LocalTypeDB) (ctx : NameContext)
    (hfreshAll : ∀ c, NameContext.freshName c ∉ c) :
    t.isContractive = true →
    t.isClosedAt (ctx.length) = true →
    (t.fromDB ctx).isContractive = true := by
  intro hcontr hclosed
  induction t generalizing ctx with
  | end => simp [LocalTypeDB.fromDB, LocalTypeR.isContractive]
  | var n => simp [LocalTypeDB.fromDB, LocalTypeR.isContractive]
  | send p bs ih =>
      simp [LocalTypeDB.isContractive] at hcontr
      -- branches
      induction bs generalizing ctx with
      | nil => simp [LocalTypeDB.fromDB, LocalTypeR.isContractive]
      | cons hd tl ih' =>
          obtain ⟨l, t⟩ := hd
          have h_t_contr : t.isContractive = true := by
            simpa [LocalTypeDB.isContractive] using hcontr
          have h_t_closed : t.isClosedAt ctx.length = true := by
            simpa [LocalTypeDB.isClosedAtBranches] using hclosed
          have h_t := ih (ctx := ctx) hfreshAll h_t_contr h_t_closed
          have h_tl_contr : LocalTypeDB.isContractiveBranches tl = true := by
            simpa [LocalTypeDB.isContractive] using hcontr
          have h_tl_closed : LocalTypeDB.isClosedAtBranches ctx.length tl = true := by
            simpa [LocalTypeDB.isClosedAtBranches] using hclosed
          have h_tl := ih' (ctx := ctx) hfreshAll h_tl_contr h_tl_closed
          simp [LocalTypeDB.fromDB, LocalTypeR.isContractive, h_t, h_tl]
  | recv p bs ih =>
      simp [LocalTypeDB.isContractive] at hcontr
      induction bs generalizing ctx with
      | nil => simp [LocalTypeDB.fromDB, LocalTypeR.isContractive]
      | cons hd tl ih' =>
          obtain ⟨l, t⟩ := hd
          have h_t_contr : t.isContractive = true := by
            simpa [LocalTypeDB.isContractive] using hcontr
          have h_t_closed : t.isClosedAt ctx.length = true := by
            simpa [LocalTypeDB.isClosedAtBranches] using hclosed
          have h_t := ih (ctx := ctx) hfreshAll h_t_contr h_t_closed
          have h_tl_contr : LocalTypeDB.isContractiveBranches tl = true := by
            simpa [LocalTypeDB.isContractive] using hcontr
          have h_tl_closed : LocalTypeDB.isClosedAtBranches ctx.length tl = true := by
            simpa [LocalTypeDB.isClosedAtBranches] using hclosed
          have h_tl := ih' (ctx := ctx) hfreshAll h_tl_contr h_tl_closed
          simp [LocalTypeDB.fromDB, LocalTypeR.isContractive, h_t, h_tl]
  | mu body ih =>
      simp [LocalTypeDB.isContractive] at hcontr
      rcases hcontr with ⟨hguard, hbody⟩
      have hclosed' : body.isClosedAt (ctx.length + 1) = true := by
        simpa [LocalTypeDB.isClosedAt] using hclosed
      have hguard' := isGuarded_fromDB_fresh body ctx hfreshAll hclosed' hguard
      have hbody' := ih (ctx := NameContext.freshName ctx :: ctx) hfreshAll hbody hclosed'
      simp [LocalTypeDB.fromDB, LocalTypeR.isContractive, hguard', hbody']

end RumpsteakV2.Protocol.LocalTypeConvProofs
