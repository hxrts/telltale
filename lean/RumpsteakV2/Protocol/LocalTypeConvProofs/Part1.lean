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

end RumpsteakV2.Protocol.LocalTypeConvProofs
