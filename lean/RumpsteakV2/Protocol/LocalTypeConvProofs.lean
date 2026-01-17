import Mathlib
import Batteries.Data.Nat.Digits
import RumpsteakV2.Protocol.LocalTypeConvDefs

set_option linter.mathlibStandardSet false

/-! # RumpsteakV2.Protocol.LocalTypeConvProofs

Conversion Proofs: LocalTypeR ↔ LocalTypeDB Roundtrip.

This module provides proven theorems for the conversion between named (LocalTypeR)
and de Bruijn indexed (LocalTypeDB) representations of local types.

This file uses the canonical definitions from `RumpsteakV2.Protocol.LocalTypeConv`,
`LocalTypeR`, and `LocalTypeDB`.
-/

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
open RumpsteakV2.Protocol.NameOnlyContext

/-! ## Basic list helpers -/

lemma get?_mem {ctx : NameContext} {i : Nat} {v : String}
    (h : NameContext.get? ctx i = some v) : v ∈ ctx :=
  RumpsteakV2.Protocol.NameOnlyContext.get?_mem h

lemma get?_some_of_lt {ctx : NameContext} {i : Nat} (h : i < ctx.length) :
    ∃ v, NameContext.get? ctx i = some v :=
  RumpsteakV2.Protocol.NameOnlyContext.get?_lt h

lemma findIdx?_go_succ {α : Type} (p : α → Bool) (l : List α) (i : Nat) :
    List.findIdx?.go p l (i + 1) = Option.map Nat.succ (List.findIdx?.go p l i) := by
  induction l generalizing i with
  | nil => simp [List.findIdx?.go]
  | cons a l ih =>
      by_cases hpa : p a = true
      · simp [List.findIdx?.go, hpa]
      · have ih' := ih (i := i + 1)
        simpa [List.findIdx?.go, hpa, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih'

/-! ## IndexOf helpers -/


lemma indexOf_cons (a : String) (ctx : Context) (v : String) :
    Context.indexOf (NameOnlyContext.cons a ctx) v =
      (if a == v then some 0 else Option.map Nat.succ (Context.indexOf ctx v)) := by
  by_cases h : a = v
  · subst h
    simp only [beq_self_eq_true, ↓reduceIte, Context.indexOf, NameOnlyContext.indexOf_cons_eq]
  · have hne : (a == v) = false := beq_eq_false_iff_ne.mpr h
    simp only [hne, ↓reduceIte, Context.indexOf]
    exact NameOnlyContext.indexOf_cons_ne ctx h

lemma indexOf_eq_none_iff_not_mem (ctx : Context) (v : String) :
    Context.indexOf ctx v = none ↔ v ∉ ctx := by
  simp only [Context.indexOf, NameOnlyContext.mem_iff_mem_names]
  exact NameOnlyContext.indexOf_eq_none_iff

lemma indexOf_lt_length {ctx : Context} {v : String} {i : Nat}
    (h : Context.indexOf ctx v = some i) : i < ctx.length := by
  simp only [Context.indexOf] at h
  exact NameOnlyContext.indexOf_lt h

lemma indexOf_get? {ctx : Context} {v : String} {i : Nat}
    (h : Context.indexOf ctx v = some i) : NameContext.get? ctx i = some v := by
  simp only [Context.indexOf, NameContext.get?] at h ⊢
  exact NameOnlyContext.indexOf_get? h

lemma indexOf_eq_some_of_mem {ctx : Context} {v : String} (hmem : v ∈ ctx) :
    ∃ i, Context.indexOf ctx v = some i := by
  by_cases hnone : Context.indexOf ctx v = none
  · have : v ∉ ctx := (indexOf_eq_none_iff_not_mem _ _).1 hnone
    contradiction
  · cases hidx : Context.indexOf ctx v with
    | none => exact (hnone hidx).elim
    | some i => exact ⟨i, rfl⟩


lemma get?_inj_of_nodup {ctx : NameContext} (hnd : ctx.Nodup) {i j : Nat} {v : String}
    (hi : NameContext.get? ctx i = some v) (hj : NameContext.get? ctx j = some v) : i = j := by
  induction ctx using NameOnlyContext.induction generalizing i j with
  | h_empty => simp [NameContext.get?, NameOnlyContext.get?, TypeContext.getName?] at hi
  | h_cons a ctx ih =>
      cases i <;> cases j
      · rfl
      · simp only [NameContext.get?, NameOnlyContext.get?_cons_zero] at hi
        have hv : a = v := Option.some.inj hi
        subst hv
        simp only [NameContext.get?, NameOnlyContext.get?_cons_succ] at hj
        have : a ∈ ctx := get?_mem hj
        have hnotmem := NameOnlyContext.notMem_of_Nodup_cons hnd
        exact (hnotmem this).elim
      · simp only [NameContext.get?, NameOnlyContext.get?_cons_zero] at hj
        have hv : a = v := Option.some.inj hj
        subst hv
        simp only [NameContext.get?, NameOnlyContext.get?_cons_succ] at hi
        have : a ∈ ctx := get?_mem hi
        have hnotmem := NameOnlyContext.notMem_of_Nodup_cons hnd
        exact (hnotmem this).elim
      · simp only [NameContext.get?, NameOnlyContext.get?_cons_succ] at hi hj
        have hnd' : ctx.Nodup := NameOnlyContext.Nodup_tail hnd
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
  have heq : some x = some y := hx'.symm.trans hy'
  exact Option.some.inj heq


lemma get?_append_right (xs ys : NameContext) (n : Nat) :
    NameContext.get? (xs ++ ys) (xs.length + n) = NameContext.get? ys n := by
  induction xs using NameOnlyContext.induction generalizing n with
  | h_empty =>
      simp only [TypeContext.length_empty, Nat.zero_add]
      rfl
  | h_cons a xs ih =>
      simp only [NameOnlyContext.cons_length, Nat.add_succ, Nat.succ_add]
      have heq : NameOnlyContext.cons a xs ++ ys = NameOnlyContext.cons a (xs ++ ys) := by
        show TypeContext.mk _ = TypeContext.mk _
        congr 1
      rw [heq]
      simp only [NameContext.get?, NameOnlyContext.get?_cons_succ]
      exact ih n

private lemma cons_append_eq_cons (a : String) (pref suffix : NameOnlyContext) :
    NameOnlyContext.cons a pref ++ suffix = NameOnlyContext.cons a (pref ++ suffix) := by
  show TypeContext.mk _ = TypeContext.mk _
  congr 1

private lemma empty_append_eq (suffix : NameOnlyContext) :
    (TypeContext.empty : NameOnlyContext) ++ suffix = suffix := by
  show TypeContext.mk _ = TypeContext.mk _
  congr 1

lemma indexOf_append_x_le (pref ctx : Context) (x : String) :
    ∃ k, Context.indexOf (pref ++ NameOnlyContext.cons x ctx) x = some k ∧ k ≤ pref.length := by
  induction pref using NameOnlyContext.induction with
  | h_empty =>
      refine ⟨0, ?_, by simp⟩
      simp only [Context.indexOf]
      rw [empty_append_eq]
      exact NameOnlyContext.indexOf_cons_eq x ctx
  | h_cons a pref ih =>
      by_cases hax : a = x
      · subst hax
        refine ⟨0, ?_, by simp⟩
        simp only [Context.indexOf]
        rw [cons_append_eq_cons]
        exact NameOnlyContext.indexOf_cons_eq a (pref ++ NameOnlyContext.cons a ctx)
      · obtain ⟨k, hk, hkle⟩ := ih
        refine ⟨k + 1, ?_, ?_⟩
        · simp only [Context.indexOf] at hk ⊢
          rw [cons_append_eq_cons]
          rw [NameOnlyContext.indexOf_cons_ne _ hax, hk]
          rfl
        · exact Nat.succ_le_succ hkle

/-- If v ≠ x and j > pref.length, then v was found in ctx and we can extract its index -/
lemma indexOf_append_suffix {pref ctx : Context} {x v : String} {j : Nat}
    (hvx : v ≠ x)
    (hj : Context.indexOf (pref ++ NameOnlyContext.cons x ctx) v = some j)
    (hjgt : j > pref.length) :
    Context.indexOf ctx v = some (j - pref.length - 1) := by
  induction pref using NameOnlyContext.induction generalizing j with
  | h_empty =>
      simp only [TypeContext.length_empty] at hjgt
      simp only [Context.indexOf] at hj ⊢
      rw [empty_append_eq] at hj
      -- hj : (cons x ctx).indexOf v = some j, hjgt : j > 0
      -- Since v ≠ x, v must be found in ctx at position j - 1
      -- indexOf_cons_ne requires x ≠ v (the element at cons position ≠ the lookup key)
      rw [NameOnlyContext.indexOf_cons_ne ctx (Ne.symm hvx)] at hj
      -- hj : Option.map Nat.succ (ctx.indexOf v) = some j
      cases hctx : NameOnlyContext.indexOf ctx v with
      | none => simp [hctx] at hj
      | some k =>
          simp only [hctx, Option.map, Option.some.injEq] at hj
          -- hj : k + 1 = j, goal is indexOf ctx v = some (j - 0 - 1) = some (j - 1)
          -- Since k + 1 = j, we have k = j - 1
          simp only [TypeContext.length_empty, Nat.add_zero, hctx]
          congr 1
          omega
  | h_cons a pref ih =>
      simp only [Context.indexOf] at hj ⊢
      rw [cons_append_eq_cons] at hj
      by_cases hav : a = v
      · subst hav
        simp only [NameOnlyContext.indexOf_cons_eq] at hj
        cases hj
        simp only [NameOnlyContext.cons_length] at hjgt
        omega
      · rw [NameOnlyContext.indexOf_cons_ne _ hav] at hj
        cases hpref : NameOnlyContext.indexOf (pref ++ NameOnlyContext.cons x ctx) v with
        | none => simp [hpref] at hj
        | some k =>
            simp only [hpref, Option.map, Option.some.injEq] at hj
            -- hj : k + 1 = j
            have hjgt' : k > pref.length := by
              simp only [NameOnlyContext.cons_length] at hjgt
              omega
            have hpref' : Context.indexOf (pref ++ NameOnlyContext.cons x ctx) v = some k := by
              simp only [Context.indexOf]
              exact hpref
            have ih' := ih hpref' hjgt'
            have heq : j - (pref.length + 1) - 1 = k - pref.length - 1 := by omega
            simp only [NameOnlyContext.cons_length, heq]
            exact ih'

/-! ## String / Nat helpers for fresh-name proofs -/

lemma String_data_append (s1 s2 : String) : (s1 ++ s2).toList = s1.toList ++ s2.toList := by
  simp [String.toList_append]

theorem String_append_left_cancel (p s1 s2 : String) : p ++ s1 = p ++ s2 → s1 = s2 := by
  intro h
  have h_list : p.toList ++ s1.toList = p.toList ++ s2.toList := by
    simpa [String.toList_append] using (congrArg String.toList h)
  have h_cancel : s1.toList = s2.toList :=
    List.append_cancel_left h_list
  exact String.toList_injective h_cancel

lemma digitChar_inj_of_lt_10 {n m : Nat} (hn : n < 10) (hm : m < 10) :
  Nat.digitChar n = Nat.digitChar m → n = m := by
  intro h
  revert h
  interval_cases n <;> interval_cases m <;> trivial

lemma toDigits_eq_reverse_digits_map (n : Nat) (h : n > 0) :
  Nat.toDigits 10 n = (Nat.digits 10 n).reverse.map Nat.digitChar := by
  -- strong recursion on n to align toDigits with little-endian digits
  revert h
  refine Nat.strongRecOn n ?_
  intro n ih hn_pos
  by_cases hlt : n < 10
  · have hto : Nat.toDigits 10 n = [Nat.digitChar n] :=
      Nat.toDigits_of_lt_base hlt
    have hdigits : Nat.digits 10 n = [n] :=
      Nat.digits_of_lt 10 n (Nat.ne_of_gt hn_pos) hlt
    simp [hto, hdigits]
  · have hge : 10 ≤ n := Nat.le_of_not_lt hlt
    let q := n / 10
    let d := n % 10
    have hqpos : 0 < q := Nat.div_pos hge (by decide : 0 < (10 : Nat))
    have hq_lt : q < n := Nat.div_lt_self hn_pos (by decide : 1 < (10 : Nat))
    have hlt_d : d < 10 := Nat.mod_lt _ (by decide : 0 < (10 : Nat))
    have hdecomp : 10 * q + d = n := by
      have := Nat.mod_add_div n 10
      simpa [q, d, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm] using this
    have htd : Nat.toDigits 10 n = Nat.toDigits 10 q ++ Nat.toDigits 10 d := by
      have htd' :
          Nat.toDigits 10 (10 * q + d) = Nat.toDigits 10 q ++ Nat.toDigits 10 d := by
        simpa using
          (Nat.toDigits_append_toDigits (b := 10) (n := q) (d := d) (hb := by decide)
            (hn := hqpos) (hd := hlt_d)).symm
      simpa [hdecomp] using htd'
    have hdigits : Nat.digits 10 n = d :: Nat.digits 10 q := by
      have hxy : d ≠ 0 ∨ q ≠ 0 := Or.inr (ne_of_gt hqpos)
      have hdigits' : Nat.digits 10 (d + 10 * q) = d :: Nat.digits 10 q := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm] using
          (Nat.digits_add 10 (by decide : 1 < (10 : Nat)) d q hlt_d hxy)
      have hdecomp' : d + 10 * q = n := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm] using hdecomp
      simpa [hdecomp'] using hdigits'
    have ihq := ih q hq_lt hqpos
    have htd_d : Nat.toDigits 10 d = [Nat.digitChar d] :=
      Nat.toDigits_of_lt_base hlt_d
    -- rewrite and simplify
    simp [htd, ihq, htd_d, hdigits, List.map_append, List.reverse_cons, List.map_reverse]

lemma digits_10_map_digitChar_inj {l1 l2 : List Nat}
  (h1 : ∀ d ∈ l1, d < 10) (h2 : ∀ d ∈ l2, d < 10)
  (h_eq : l1.map Nat.digitChar = l2.map Nat.digitChar) :
  l1 = l2 := by
  induction l1 generalizing l2
  case nil =>
    cases l2
    case nil => rfl
    case cons => contradiction
  case cons head tail ih =>
    cases l2
    case nil => contradiction
    case cons head2 tail2 =>
      simp at h_eq
      have h_head : head = head2 := by
        apply digitChar_inj_of_lt_10
        · apply h1; simp
        · apply h2; simp
        · exact h_eq.1
      subst h_head
      congr
      apply ih
      · intros d hd; apply h1; simp [hd]
      · intros d hd; apply h2; simp [hd]
      · exact h_eq.2

lemma toDigits_eq_singleton_zero_iff (n : Nat) : Nat.toDigits 10 n = ['0'] ↔ n = 0 := by
  constructor
  · intro h
    by_cases hn : n = 0
    · exact hn
    · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
      have hrev :
          (Nat.digits 10 n).reverse.map Nat.digitChar = ['0'] := by
        simpa [toDigits_eq_reverse_digits_map n hn_pos] using h
      have hrev' : (Nat.digits 10 n).reverse = [0] := by
        apply digits_10_map_digitChar_inj
        · intro d hd
          exact Nat.digits_lt_base (b := 10) (m := n) (hb := by decide) (List.mem_reverse.mp hd)
        · intro d hd
          simp at hd
          subst hd
          decide
        · simpa using hrev
      have hdigits : Nat.digits 10 n = [0] := by
        simpa using congrArg List.reverse hrev'
      have : n = 0 := by
        simpa [hdigits] using (Nat.ofDigits_digits 10 n).symm
      exact (hn this).elim
  · intro h
    subst h
    simp [Nat.toDigits_zero]

lemma toDigits_ne_zero_of_pos (n : Nat) (h : n > 0) : Nat.toDigits 10 n ≠ ['0'] := by
  intro h_eq
  have hzero : n = 0 := (toDigits_eq_singleton_zero_iff n).1 h_eq
  exact (Nat.ne_of_gt h) hzero

theorem Nat_toString_inj (n m : Nat) : toString n = toString m → n = m := by
  intro h
  have hdigits : Nat.toDigits 10 n = Nat.toDigits 10 m := by
    have h' : String.ofList (Nat.toDigits 10 n) = String.ofList (Nat.toDigits 10 m) := by
      simpa [Nat.repr] using h
    exact String.ofList_injective h'
  by_cases hn : n = 0
  · subst hn
    have hm : m = 0 := by
      have : Nat.toDigits 10 m = ['0'] := by
        simpa [Nat.toDigits_zero] using hdigits.symm
      exact (toDigits_eq_singleton_zero_iff m).1 this
    simp [hm]
  · by_cases hm : m = 0
    · subst hm
      have : Nat.toDigits 10 n = ['0'] := by
        have : Nat.toDigits 10 n = Nat.toDigits 10 0 := by simpa using hdigits
        simpa [Nat.toDigits_zero] using this
      exact (hn ((toDigits_eq_singleton_zero_iff n).1 this)).elim
    · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
      have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
      have hrev :
          (Nat.digits 10 n).reverse.map Nat.digitChar =
            (Nat.digits 10 m).reverse.map Nat.digitChar := by
        simpa [toDigits_eq_reverse_digits_map n hn_pos, toDigits_eq_reverse_digits_map m hm_pos] using hdigits
      have hrev' : (Nat.digits 10 n).reverse = (Nat.digits 10 m).reverse := by
        apply digits_10_map_digitChar_inj
        · intro d hd
          exact Nat.digits_lt_base (b := 10) (m := n) (hb := by decide) (List.mem_reverse.mp hd)
        · intro d hd
          exact Nat.digits_lt_base (b := 10) (m := m) (hb := by decide) (List.mem_reverse.mp hd)
        · exact hrev
      have hdigits' : Nat.digits 10 n = Nat.digits 10 m := by
        simpa using congrArg List.reverse hrev'
      exact (Nat.digits_inj_iff (b := 10) (n := n) (m := m)).1 hdigits'

inductive GeneratedContext : NameContext → Prop where
  | empty : GeneratedContext TypeContext.empty
  | cons {ctx} : GeneratedContext ctx → GeneratedContext (NameOnlyContext.cons (NameContext.freshName ctx) ctx)

theorem generated_elements (ctx : NameContext) (h : GeneratedContext ctx) :
    ∀ s, s ∈ ctx → ∃ n < ctx.length, s = "_db" ++ toString n := by
  induction h with
  | empty =>
      intro s hs
      simp [NameOnlyContext.mem_iff_mem_names, TypeContext.names_empty] at hs
  | @cons inner_ctx h_ctx ih =>
      intro s hs
      simp only [NameOnlyContext.mem_cons_iff] at hs
      cases hs with
      | inl heq =>
          subst heq
          simp only [NameContext.freshName, NameOnlyContext.freshName, NameOnlyContext.cons_length]
          exact ⟨inner_ctx.length, Nat.lt_succ_self _, rfl⟩
      | inr hmem =>
          obtain ⟨n, hn, hs_eq⟩ := ih s hmem
          simp only [NameOnlyContext.cons_length]
          exact ⟨n, Nat.lt_succ_of_lt hn, hs_eq⟩

theorem fresh_not_in_generated (ctx : NameContext) (h : GeneratedContext ctx) :
    NameContext.freshName ctx ∉ ctx := by
  intro h_in
  obtain ⟨n, hn_lt, hn_eq⟩ := generated_elements ctx h _ h_in
  simp only [NameContext.freshName, NameOnlyContext.freshName] at hn_eq
  have h_len_eq : toString ctx.length = toString n := by
    apply String_append_left_cancel "_db" _ _ hn_eq
  have h_n_eq : ctx.length = n := Nat_toString_inj _ _ h_len_eq
  omega

theorem generated_nodup (ctx : NameContext) (h : GeneratedContext ctx) :
    ctx.Nodup := by
  induction h with
  | empty => exact NameOnlyContext.Nodup_empty
  | @cons inner_ctx h_ctx ih =>
      apply NameOnlyContext.Nodup_cons
      · exact fresh_not_in_generated _ h_ctx
      · exact ih

/-! ## fromDB? correctness for closed terms -/

theorem fromDB?_eq_fromDB_all_ctx (t : LocalTypeDB) (ctx : NameContext)
    (hclosed : t.isClosedAt ctx.length = true) :
    t.fromDB? ctx = some (t.fromDB ctx) := by
  let P1 : LocalTypeDB → Prop :=
    fun t => ∀ ctx, t.isClosedAt ctx.length = true → t.fromDB? ctx = some (t.fromDB ctx)
  let P2 : List (Label × LocalTypeDB) → Prop :=
    fun bs =>
      ∀ ctx, isClosedAtBranches ctx.length bs = true →
        branchesFromDB? ctx bs = some (branchesFromDB ctx bs)
  let P3 : Label × LocalTypeDB → Prop :=
    fun b =>
      ∀ ctx, b.2.isClosedAt ctx.length = true → b.2.fromDB? ctx = some (b.2.fromDB ctx)
  have hrec : P1 t := by
    refine (LocalTypeDB.rec (motive_1 := P1) (motive_2 := P2) (motive_3 := P3)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ t)
    · intro ctx hclosed
      simp [LocalTypeDB.fromDB?, LocalTypeDB.fromDB]
    · intro n ctx hclosed
      have hlt : n < ctx.length := by
        simpa [LocalTypeDB.isClosedAt] using hclosed
      obtain ⟨v, hget⟩ := get?_some_of_lt (ctx := ctx) (i := n) hlt
      simp [LocalTypeDB.fromDB?, LocalTypeDB.fromDB, hget]
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

theorem branchesFromDB?_eq_branchesFromDB (bs : List (Label × LocalTypeDB)) (ctx : NameContext)
    (hclosed : isClosedAtBranches ctx.length bs = true) :
    branchesFromDB? ctx bs = some (branchesFromDB ctx bs) := by
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

theorem fromDB?_eq_fromDB_closed (t : LocalTypeDB) (hclosed : t.isClosed = true) :
    t.fromDB? TypeContext.empty = some (t.fromDB TypeContext.empty) := by
  have hclosed' : t.isClosedAt 0 = true := by
    simpa [LocalTypeDB.isClosed] using hclosed
  have hclosed'' : t.isClosedAt (TypeContext.empty : NameContext).length = true := by
    simp only [TypeContext.length_empty]
    exact hclosed'
  exact fromDB?_eq_fromDB_all_ctx t TypeContext.empty hclosed''

/-! ## fromDB closedness -/

lemma freeVars_fromDB_subset_ctx (t : LocalTypeDB) (ctx : NameContext)
    (hclosed : t.isClosedAt ctx.length = true) :
    ∀ v, v ∈ (t.fromDB ctx).freeVars → v ∈ ctx := by
  let P1 : LocalTypeDB → Prop :=
    fun t =>
      ∀ ctx, t.isClosedAt ctx.length = true →
        ∀ v, v ∈ (t.fromDB ctx).freeVars → v ∈ ctx
  let P2 : List (Label × LocalTypeDB) → Prop :=
    fun bs =>
      ∀ ctx, isClosedAtBranches ctx.length bs = true →
        ∀ v, v ∈ LocalTypeR.freeVarsOfBranches (LocalTypeDB.branchesFromDB ctx bs) → v ∈ ctx
  let P3 : Label × LocalTypeDB → Prop :=
    fun b =>
      ∀ ctx, b.2.isClosedAt ctx.length = true →
        ∀ v, v ∈ (b.2.fromDB ctx).freeVars → v ∈ ctx
  have hrec : P1 t := by
    refine (LocalTypeDB.rec (motive_1 := P1) (motive_2 := P2) (motive_3 := P3)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ t)
    · intro ctx hclosed v hv
      simp [LocalTypeDB.fromDB, LocalTypeR.freeVars] at hv
    · intro n ctx hclosed v hv
      have hlt : n < ctx.length := by
        simpa [LocalTypeDB.isClosedAt] using hclosed
      obtain ⟨name, hget⟩ := get?_some_of_lt (ctx := ctx) (i := n) hlt
      simp [LocalTypeDB.fromDB, hget, LocalTypeR.freeVars] at hv
      subst hv
      exact get?_mem hget
    · intro p bs hbs ctx hclosed v hv
      have hclosed' : isClosedAtBranches ctx.length bs = true := by
        simpa [LocalTypeDB.isClosedAt] using hclosed
      have hv' : v ∈ LocalTypeR.freeVarsOfBranches (LocalTypeDB.branchesFromDB ctx bs) := by
        simpa [LocalTypeDB.fromDB, LocalTypeR.freeVars] using hv
      exact hbs ctx hclosed' v hv'
    · intro p bs hbs ctx hclosed v hv
      have hclosed' : isClosedAtBranches ctx.length bs = true := by
        simpa [LocalTypeDB.isClosedAt] using hclosed
      have hv' : v ∈ LocalTypeR.freeVarsOfBranches (LocalTypeDB.branchesFromDB ctx bs) := by
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
      have hv' : v ∈ (t.fromDB ctx).freeVars ∨
          v ∈ LocalTypeR.freeVarsOfBranches (LocalTypeDB.branchesFromDB ctx tail) := by
        simpa [LocalTypeDB.branchesFromDB, LocalTypeR.freeVarsOfBranches, List.mem_append] using hv
      cases hv' with
      | inl hv_head =>
          exact hhead ctx hclosed'.1 v hv_head
      | inr hv_tail =>
          exact htail ctx hclosed'.2 v hv_tail
    · intro fst snd hsnd
      exact hsnd
  exact hrec ctx hclosed

theorem fromDB_closed (t : LocalTypeDB) (hclosed : t.isClosed = true) :
    (t.fromDB TypeContext.empty).isClosed = true := by
  have hclosed' : t.isClosedAt 0 = true := by
    simpa [LocalTypeDB.isClosed] using hclosed
  have hclosed'' : t.isClosedAt (TypeContext.empty : NameContext).length = true := by
    simp only [TypeContext.length_empty]; exact hclosed'
  have hsub := freeVars_fromDB_subset_ctx t TypeContext.empty hclosed''
  have hnil : (t.fromDB TypeContext.empty).freeVars = [] := by
    apply (List.eq_nil_iff_forall_not_mem).2
    intro v hv
    have hmem : v ∈ (TypeContext.empty : NameContext) := hsub v hv
    simp only [NameOnlyContext.mem_iff_mem_names, TypeContext.names_empty, List.not_mem_nil] at hmem
  simp [LocalTypeR.isClosed, hnil]

/-! ## toDB? succeeds for closed terms -/

theorem toDB?_some_of_covers (t : LocalTypeR) (ctx : Context)
    (hcov : Context.Covers ctx t) :
    ∃ db, t.toDB? ctx = some db ∧ db.isClosedAt ctx.length = true := by
  let P1 : LocalTypeR → Prop :=
    fun t =>
      ∀ ctx, Context.Covers ctx t → ∃ db, t.toDB? ctx = some db ∧ db.isClosedAt ctx.length = true
  let P2 : List (Label × LocalTypeR) → Prop :=
    fun bs =>
      ∀ ctx, (∀ l t, (l, t) ∈ bs → Context.Covers ctx t) →
        ∃ dbs, LocalTypeR.branchesToDB? ctx bs = some dbs ∧
          isClosedAtBranches ctx.length dbs = true
  let P3 : Label × LocalTypeR → Prop :=
    fun b =>
      ∀ ctx, Context.Covers ctx b.2 → ∃ db, b.2.toDB? ctx = some db ∧ db.isClosedAt ctx.length = true
  have hrec : P1 t := by
    refine (RumpsteakV2.Protocol.LocalTypeR.LocalTypeR.rec
      (motive_1 := P1) (motive_2 := P2) (motive_3 := P3)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ t)
    · intro ctx hcov
      refine ⟨LocalTypeDB.end, ?_, ?_⟩
      · simp [LocalTypeR.toDB?]
      · simp [LocalTypeDB.isClosedAt]
    · intro p bs hbs ctx hcov
      have hcov' : ∀ l t, (l, t) ∈ bs → Context.Covers ctx t := by
        intro l t hmem v hv
        apply hcov v
        have : v ∈ LocalTypeR.freeVarsOfBranches bs := by
          have : v ∈ bs.flatMap (fun (_, t) => t.freeVars) := by
            refine List.mem_flatMap.mpr ?_
            refine ⟨(l, t), hmem, ?_⟩
            simpa using hv
          simpa [LocalTypeR.freeVarsOfBranches_eq_flatMap] using this
        simpa [LocalTypeR.freeVars] using this
      obtain ⟨dbs, hdbs, hclosed⟩ := hbs ctx hcov'
      refine ⟨LocalTypeDB.send p dbs, ?_, ?_⟩
      · simp [LocalTypeR.toDB?, hdbs]
      · simpa [LocalTypeDB.isClosedAt] using hclosed
    · intro p bs hbs ctx hcov
      have hcov' : ∀ l t, (l, t) ∈ bs → Context.Covers ctx t := by
        intro l t hmem v hv
        apply hcov v
        have : v ∈ LocalTypeR.freeVarsOfBranches bs := by
          have : v ∈ bs.flatMap (fun (_, t) => t.freeVars) := by
            refine List.mem_flatMap.mpr ?_
            refine ⟨(l, t), hmem, ?_⟩
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
      obtain ⟨l, t⟩ := head
      have hcov_t : Context.Covers ctx t := hcov l t (by simp)
      have hcov_tl : ∀ l t, (l, t) ∈ tail → Context.Covers ctx t :=
        fun l t hmem => hcov l t (List.mem_cons_of_mem _ hmem)
      obtain ⟨db, hdb, hclosed⟩ := hhead ctx hcov_t
      obtain ⟨dbs, hdbs, hclosedbs⟩ := htail ctx hcov_tl
      refine ⟨(l, db) :: dbs, ?_, ?_⟩
      · simp [LocalTypeR.branchesToDB?, hdb, hdbs]
      · simp [isClosedAtBranches, hclosed, hclosedbs]
    · intro fst snd hsnd
      exact hsnd
  exact hrec ctx hcov

theorem branchesToDB?_some_of_covers (bs : List (Label × LocalTypeR)) (ctx : Context)
    (hcov : ∀ l t, (l, t) ∈ bs → Context.Covers ctx t) :
    ∃ dbs, LocalTypeR.branchesToDB? ctx bs = some dbs ∧
          isClosedAtBranches ctx.length dbs = true := by
  induction bs with
  | nil =>
      refine ⟨[], ?_, ?_⟩
      · simp [LocalTypeR.branchesToDB?]
      · simp [isClosedAtBranches]
  | cons hd tl ih =>
      obtain ⟨l, t⟩ := hd
      have hcov_t : Context.Covers ctx t := hcov l t (by simp)
      have hcov_tl : ∀ l t, (l, t) ∈ tl → Context.Covers ctx t :=
        fun l t hmem => hcov l t (List.mem_cons_of_mem _ hmem)
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

/-! ## Roundtrip (fromDB then toDB?) -/

theorem toDB_fromDB_roundtrip_generated (t : LocalTypeDB) (ctx : NameContext)
    (hgen : GeneratedContext ctx) (hclosed : t.isClosedAt ctx.length = true) :
    (t.fromDB ctx).toDB? ctx = some t := by
  let P1 : LocalTypeDB → Prop :=
    fun t =>
      ∀ ctx, GeneratedContext ctx →
        t.isClosedAt ctx.length = true →
          (t.fromDB ctx).toDB? ctx = some t
  let P2 : List (Label × LocalTypeDB) → Prop :=
    fun bs =>
      ∀ ctx, GeneratedContext ctx →
        isClosedAtBranches ctx.length bs = true →
          LocalTypeR.branchesToDB? ctx (LocalTypeDB.branchesFromDB ctx bs) = some bs
  let P3 : Label × LocalTypeDB → Prop :=
    fun b =>
      ∀ ctx, GeneratedContext ctx →
        b.2.isClosedAt ctx.length = true →
          (b.2.fromDB ctx).toDB? ctx = some b.2
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
      simp only [LocalTypeDB.fromDB, LocalTypeR.toDB?, hget]
      rw [Context.indexOf_eq] at hidx
      simp only [hidx, Option.map]
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

theorem branches_toDB_fromDB_roundtrip_generated (bs : List (Label × LocalTypeDB)) (ctx : NameContext)
    (hgen : GeneratedContext ctx)
    (hclosed : isClosedAtBranches ctx.length bs = true) :
    LocalTypeR.branchesToDB? ctx (LocalTypeDB.branchesFromDB ctx bs) = some bs := by
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

theorem toDB_fromDB_roundtrip_closed (t : LocalTypeDB) (hclosed : t.isClosed = true) :
  (t.fromDB TypeContext.empty).toDB? TypeContext.empty = some t := by
  have hclosed' : t.isClosedAt 0 = true := by
    simpa [LocalTypeDB.isClosed] using hclosed
  have hclosed'' : t.isClosedAt (TypeContext.empty : NameContext).length = true := by
    simp only [TypeContext.length_empty]; exact hclosed'
  exact toDB_fromDB_roundtrip_generated t TypeContext.empty GeneratedContext.empty hclosed''

theorem branches_toDB_fromDB_roundtrip_closed (bs : List (Label × LocalTypeDB))
    (hclosed : isClosedAtBranches 0 bs = true) :
  LocalTypeR.branchesToDB? TypeContext.empty (LocalTypeDB.branchesFromDB TypeContext.empty bs) = some bs := by
  have hclosed' : isClosedAtBranches (TypeContext.empty : NameContext).length bs = true := by
    simp only [TypeContext.length_empty]; exact hclosed
  exact branches_toDB_fromDB_roundtrip_generated bs TypeContext.empty GeneratedContext.empty hclosed'

/-! ## General roundtrip with adequate context -/

theorem toDB_fromDB_roundtrip (t : LocalTypeDB) (ctx : NameContext)
    (hnodup : ctx.Nodup)
    (hfreshAll : ∀ c, NameContext.freshName c ∉ c)
    (hclosed : t.isClosedAt ctx.length = true) :
    (t.fromDB ctx).toDB? ctx = some t := by
  let P1 : LocalTypeDB → Prop :=
    fun t =>
      ∀ ctx, ctx.Nodup → (∀ c, NameContext.freshName c ∉ c) →
        t.isClosedAt ctx.length = true → (t.fromDB ctx).toDB? ctx = some t
  let P2 : List (Label × LocalTypeDB) → Prop :=
    fun bs =>
      ∀ ctx, ctx.Nodup → (∀ c, NameContext.freshName c ∉ c) →
        isClosedAtBranches ctx.length bs = true →
          LocalTypeR.branchesToDB? ctx (LocalTypeDB.branchesFromDB ctx bs) = some bs
  let P3 : Label × LocalTypeDB → Prop :=
    fun b =>
      ∀ ctx, ctx.Nodup → (∀ c, NameContext.freshName c ∉ c) →
        b.2.isClosedAt ctx.length = true → (b.2.fromDB ctx).toDB? ctx = some b.2
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
      simp only [LocalTypeDB.fromDB, LocalTypeR.toDB?, hget]
      rw [Context.indexOf_eq] at hidx
      simp only [hidx, Option.map]
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
    LocalTypeR.branchesToDB? ctx (LocalTypeDB.branchesFromDB ctx bs) = some bs := by
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
  let P2 : List (Label × LocalTypeR) → Prop := fun _ => True
  let P3 : Label × LocalTypeR → Prop := fun _ => True
  have hrec : P1 t := by
    refine (LocalTypeR.LocalTypeR.rec (motive_1 := P1) (motive_2 := P2) (motive_3 := P3)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ t)
    · intro pref ctx i db hidx hdb
      simp [LocalTypeR.toDB?] at hdb
      cases hdb
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
      simp only [fromList_cons_toList, fromList_toList, fromList_cons, fromList_append] at hdb
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
              simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, cons_length]
            simpa [this] using hguard'
          simpa [LocalTypeDB.isGuarded, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hguard''
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
  let P2 : List (Label × LocalTypeR) → Prop := fun _ => True
  let P3 : Label × LocalTypeR → Prop := fun _ => True
  have hrec : P1 t := by
    refine (LocalTypeR.LocalTypeR.rec (motive_1 := P1) (motive_2 := P2) (motive_3 := P3)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ t)
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
  exact hrec ctx x i db hguard hidx hdb

theorem isContractive_toDB (t : LocalTypeR) (ctx : Context) (db : LocalTypeDB) :
    t.isContractive = true →
    t.toDB? ctx = some db →
    db.isContractive = true := by
  intro hcontr hdb
  let P1 : LocalTypeR → Prop :=
    fun t =>
      ∀ ctx db, t.isContractive = true → t.toDB? ctx = some db → db.isContractive = true
  let P2 : List (Label × LocalTypeR) → Prop :=
    fun bs =>
      ∀ ctx dbs, LocalTypeR.isContractiveBranches bs = true →
        LocalTypeR.branchesToDB? ctx bs = some dbs →
          isContractiveBranches dbs = true
  let P3 : Label × LocalTypeR → Prop :=
    fun b =>
      ∀ ctx db, b.2.isContractive = true → b.2.toDB? ctx = some db → db.isContractive = true
  have hrec : P1 t := by
    refine (LocalTypeR.LocalTypeR.rec (motive_1 := P1) (motive_2 := P2) (motive_3 := P3)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ t)
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
              simp only [Context.indexOf, NameOnlyContext.indexOf_cons_eq]
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
      obtain ⟨l, t⟩ := head
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
  exact hrec ctx db hcontr hdb

/-! ## Contractiveness preservation for fromDB -/

lemma isGuarded_fromDB_at (t : LocalTypeDB) (ctx : NameContext) (i : Nat) (v : String)
    (hget : NameContext.get? ctx i = some v)
    (huniq : ∀ j, NameContext.get? ctx j = some v → j = i)
    (hclosed : t.isClosedAt ctx.length = true)
    (hguard : t.isGuarded i = true) :
    (t.fromDB ctx).isGuarded v = true := by
  let P1 : LocalTypeDB → Prop :=
    fun t =>
      ∀ ctx i v,
        NameContext.get? ctx i = some v →
        (∀ j, NameContext.get? ctx j = some v → j = i) →
        t.isClosedAt ctx.length = true →
        t.isGuarded i = true →
          (t.fromDB ctx).isGuarded v = true
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
      simp [LocalTypeDB.fromDB, hgetn, LocalTypeR.isGuarded, hwne]
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
    (t.fromDB (NameOnlyContext.cons (NameContext.freshName ctx) ctx)).isGuarded (NameContext.freshName ctx) = true := by
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
    t.isClosedAt (ctx.length) = true →
    (t.fromDB ctx).isContractive = true := by
  intro hcontr hclosed
  let P1 : LocalTypeDB → Prop :=
    fun t =>
      ∀ ctx, (∀ c, NameContext.freshName c ∉ c) →
        t.isContractive = true →
        t.isClosedAt ctx.length = true →
          (t.fromDB ctx).isContractive = true
  let P2 : List (Label × LocalTypeDB) → Prop :=
    fun bs =>
      ∀ ctx, (∀ c, NameContext.freshName c ∉ c) →
        isContractiveBranches bs = true →
        isClosedAtBranches ctx.length bs = true →
          LocalTypeR.isContractiveBranches (LocalTypeDB.branchesFromDB ctx bs) = true
  let P3 : Label × LocalTypeDB → Prop :=
    fun b =>
      ∀ ctx, (∀ c, NameContext.freshName c ∉ c) →
        b.2.isContractive = true →
        b.2.isClosedAt ctx.length = true →
          (b.2.fromDB ctx).isContractive = true
  have hrec : P1 t := by
    refine (LocalTypeDB.rec (motive_1 := P1) (motive_2 := P2) (motive_3 := P3)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ t)
    · intro ctx hfreshAll hcontr hclosed
      simp [LocalTypeDB.fromDB, LocalTypeR.isContractive]
    · intro n ctx hfreshAll hcontr hclosed
      cases hget : NameContext.get? ctx n <;>
        simp [LocalTypeDB.fromDB, LocalTypeR.isContractive, hget]
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

end RumpsteakV2.Protocol.LocalTypeConvProofs
