import Protocol.Environments.Core.VarsAndBuffers

/-! # Protocol.Environments.Core.DEnv

DEnv representation and core DEnv operations.
-/

/-
The Problem. Delayed type traces require a canonical finite-map model with
stable lookup/update behavior.

Solution Structure. Defines DEnv internals and proves core lookup/update lemmas.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical
open Batteries

section

/-! ## DEnv: Directed Edge → Type Trace -/

/-- A trace stored in DEnv. Empty traces are treated as missing. -/
abbrev Trace := List ValType

/-! ## Ordering and RBMap Infrastructure -/
def edgeCmpLT : (Edge × Trace) → (Edge × Trace) → Prop :=
  RBNode.cmpLT (compare ·.1 ·.1)

private instance : Std.TransCmp (fun a b : Edge × Trace => compare a.1 b.1) where
  eq_swap := by
    intro a b
    simpa using (Std.OrientedCmp.eq_swap (cmp := compare) (a := a.1) (b := b.1))
  isLE_trans := by
    intro a b c hab hbc
    simpa using (Std.TransOrd.isLE_trans (a := a.1) (b := b.1) (c := c.1) hab hbc)

lemma edgeCmpLT_eq_lt {x y : Edge × Trace} (h : edgeCmpLT x y) :
    compare x.1 y.1 = .lt := by
  simpa using
    (RBNode.cmpLT_iff (cmp := fun a b : Edge × Trace => compare a.1 b.1) (x := x) (y := y)).1 h

def rbmapOfList (l : List (Edge × Trace)) : RBMap Edge Trace compare :=
  l.foldl (fun r p => r.insert p.1 p.2) (∅ : RBMap Edge Trace compare)

/-- DEnv maps directed edges to non-empty in-flight type traces (RBMap-backed).
    Stored with a canonical list representation for extensional reasoning. -/
structure DEnv where
  list : List (Edge × Trace)
  map : RBMap Edge Trace compare
  map_eq : map = rbmapOfList list
  sorted : list.Pairwise edgeCmpLT

instance : Coe DEnv (RBMap Edge Trace compare) := ⟨DEnv.map⟩

def DEnv.ofMap (m : RBMap Edge Trace compare) : DEnv :=
  { list := m.toList
    map := rbmapOfList m.toList
    map_eq := rfl
    sorted := by
      simpa [edgeCmpLT] using (RBMap.toList_sorted (t := m)) }

instance : EmptyCollection DEnv := ⟨DEnv.ofMap (∅ : RBMap Edge Trace compare)⟩

@[simp] theorem rbmap_find?_empty (e : Edge) :
    (∅ : RBMap Edge Trace compare).find? e = none := by
  rfl

@[simp] theorem DEnv_map_find?_empty (e : Edge) :
    (∅ : DEnv).map.find? e = none := by
  rfl

def normalizeTrace (ot : Option Trace) : Option Trace :=
  match ot with
  | some [] => none
  | other => other

/-- Lookup helper (dot notation). Empty traces are erased to `none`. -/
def DEnv.find? (env : DEnv) (e : Edge) : Option (List ValType) :=
  env.map.find? e

/-! ## Canonical List Lookup Lemmas -/
lemma lookup_mem {l : List (Edge × Trace)} {e : Edge} {ts : Trace}
    (h : l.lookup e = some ts) : (e, ts) ∈ l := by
  induction l with
  | nil =>
      simp [List.lookup] at h
  | cons hd tl ih =>
      by_cases hEq : e = hd.1
      · have hts : ts = hd.2 := by
          have : some hd.2 = some ts := by
            simpa [List.lookup, hEq] using h
          exact Option.some.inj this.symm
        have hpair : (e, ts) = hd := by
          cases hd with
          | mk hd1 hd2 =>
              cases hEq
              cases hts
              rfl
        exact List.mem_cons.mpr (Or.inl hpair)
      · have hne : (e == hd.1) = false := beq_eq_false_iff_ne.mpr hEq
        have h' : tl.lookup e = some ts := by
          simpa [List.lookup, hne] using h
        have : (e, ts) ∈ tl := ih h'
        exact List.mem_cons.mpr (Or.inr this)

lemma lookup_eq_none_of_forall_ne {l : List (Edge × Trace)} {e : Edge}
    (h : ∀ p ∈ l, p.1 ≠ e) : l.lookup e = none := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
      have hne : hd.1 ≠ e := h hd (List.mem_cons.mpr (Or.inl rfl))
      have hne' : (e == hd.1) = false := by
        exact beq_eq_false_iff_ne.mpr (Ne.symm hne)
      simp [List.lookup, hne', ih (by
        intro p hp
        exact h p (List.mem_cons.mpr (Or.inr hp)))]

/-! ## Pairwise Lookup Coherence -/
theorem lookup_eq_some_of_mem_pairwise {l : List (Edge × Trace)} (h : l.Pairwise edgeCmpLT)
    {p : Edge × Trace} (hp : p ∈ l) : l.lookup p.1 = some p.2 := by
  induction l with
  | nil => cases hp
  | cons hd tl ih =>
      simp only [List.mem_cons] at hp
      simp only [List.pairwise_cons] at h
      cases hp with
      | inl hEq =>
          subst hEq
          simp [List.lookup]
      | inr hMem =>
          have hne : p.1 ≠ hd.1 := by
            have hlt : edgeCmpLT hd p := h.1 _ hMem
            -- edgeCmpLT implies key inequality
            intro hEq
            have hEq' : compare hd.1 p.1 = .eq :=
              (Edge.compare_eq_iff_eq hd.1 p.1).2 hEq.symm
            have hlt' : compare hd.1 p.1 = .lt := edgeCmpLT_eq_lt hlt
            have : (.eq : Ordering) = .lt := by
              exact hEq'.symm.trans hlt'
            cases this
          have hne' : (p.1 == hd.1) = false := by
            exact beq_eq_false_iff_ne.mpr hne
          simp [List.lookup, hne', ih h.2 hMem]

/-! ## RBMap/List Lookup Equivalence -/
theorem find?_foldl_insert_of_pairwise
    (l : List (Edge × Trace)) (m : RBMap Edge Trace compare)
    (h : l.Pairwise edgeCmpLT) (k : Edge) :
    (l.foldl (fun r p => r.insert p.1 p.2) m).find? k =
      match l.lookup k with
      | some v => some v
      | none => m.find? k := by
  induction l generalizing m with
  | nil => simp
  | cons hd tl ih =>
      simp only [List.pairwise_cons] at h
      by_cases hk : k = hd.1
      · subst hk
        -- No key in tl matches hd.1 (pairwise)
        have hnone : tl.lookup hd.1 = none := by
          apply lookup_eq_none_of_forall_ne
          intro p hp
          have hlt : edgeCmpLT hd p := h.1 _ hp
          -- edgeCmpLT implies key inequality
          intro hEq
          have hEq' : compare hd.1 p.1 = .eq :=
            (Edge.compare_eq_iff_eq hd.1 p.1).2 hEq.symm
          have hlt' : compare hd.1 p.1 = .lt := edgeCmpLT_eq_lt hlt
          have : (.eq : Ordering) = .lt := by
            exact hEq'.symm.trans hlt'
          cases this
        have hfind : (m.insert hd.1 hd.2).find? hd.1 = some hd.2 := by
          have hEq : compare hd.1 hd.1 = .eq := by
            simp
          simpa using (RBMap.find?_insert_of_eq (t := m) (k := hd.1) (v := hd.2) (k' := hd.1) hEq)
        simpa [List.lookup, hnone, hfind] using
          (ih (m := m.insert hd.1 hd.2) (h := h.2))
      · have hne : compare k hd.1 ≠ .eq := by
          intro hEq
          exact hk (Edge.compare_eq_iff_eq _ _ |>.1 hEq)
        have hne' : (k == hd.1) = false := by
          exact beq_eq_false_iff_ne.mpr hk
        have hfind : (m.insert hd.1 hd.2).find? k = m.find? k := by
          simpa using (RBMap.find?_insert_of_ne (t := m) (k := hd.1) (v := hd.2) (k' := k) hne)
        simpa [List.lookup, hne', hfind] using
          (ih (m := m.insert hd.1 hd.2) (h := h.2))

/-! ## Canonical RBMap Construction Correctness -/
theorem rbmap_find?_ofList_eq_lookup
    (l : List (Edge × Trace)) (h : l.Pairwise edgeCmpLT) (k : Edge) :
    (rbmapOfList l).find? k = l.lookup k := by
  have h' := find?_foldl_insert_of_pairwise (l := l) (m := (∅ : RBMap Edge Trace compare)) h k
  cases hLookup : l.lookup k <;>
    simpa [rbmapOfList, rbmap_find?_empty, hLookup] using h'

theorem DEnv_find?_eq_lookup (env : DEnv) (e : Edge) :
    env.find? e = env.list.lookup e := by
  have h := rbmap_find?_ofList_eq_lookup (l := env.list) (h := env.sorted) (k := e)
  simp [DEnv.find?, env.map_eq, h]

/-! ## toList/find? Agreement -/
theorem lookup_toList_eq_find? (m : RBMap Edge Trace compare) (e : Edge) :
    m.toList.lookup e = m.find? e := by
  cases h : m.find? e with
  | none =>
      by_contra hLookup
      cases hLookup' : m.toList.lookup e with
      | none =>
          exact hLookup (by simp [hLookup'])
      | some v =>
          have hMem : (e, v) ∈ m.toList := lookup_mem hLookup'
          have hFind : m.find? e = some v :=
            (RBMap.find?_some (t := m) (x := e) (v := v)).2 ⟨e, hMem, by simp⟩
          cases (hFind.symm.trans h)
  | some v =>
      have hMem : (e, v) ∈ m.toList := by
        have hSome := (RBMap.find?_some (t := m) (x := e) (v := v)).1 h
        rcases hSome with ⟨y, hy, hEq⟩
        have hy' : y = e := (Edge.compare_eq_iff_eq e y).1 hEq |>.symm
        simpa [hy'] using hy
      have hSorted : m.toList.Pairwise edgeCmpLT := by
        simpa [edgeCmpLT] using (RBMap.toList_sorted (t := m))
      have hLookup : m.toList.lookup e = some v :=
        lookup_eq_some_of_mem_pairwise hSorted hMem
      simpa [h] using hLookup

/-! ## DEnv.ofMap Lookup Characterization -/
theorem rbmapOfList_toList_find? (m : RBMap Edge Trace compare) (e : Edge) :
    (rbmapOfList m.toList).find? e = m.find? e := by
  have hSorted : m.toList.Pairwise edgeCmpLT := by
    simpa [edgeCmpLT] using (RBMap.toList_sorted (t := m))
  have hLookup := rbmap_find?_ofList_eq_lookup (l := m.toList) (h := hSorted) (k := e)
  have hToList := lookup_toList_eq_find? (m := m) (e := e)
  exact hLookup.trans hToList

@[simp] theorem DEnv_find?_ofMap (m : RBMap Edge Trace compare) (e : Edge) :
    (DEnv.ofMap m).find? e = m.find? e := by
  have hSorted : m.toList.Pairwise edgeCmpLT := by
    simpa [edgeCmpLT] using (RBMap.toList_sorted (t := m))
  have hLookup := rbmap_find?_ofList_eq_lookup (l := m.toList) (h := hSorted) (k := e)
  have hToList := lookup_toList_eq_find? (m := m) (e := e)
  simp [DEnv.find?, DEnv.ofMap, hLookup, hToList]

/-! ## Pairwise Asymmetry Helper -/
lemma edgeCmpLT_asymm {x y : Edge × Trace} (h : edgeCmpLT x y) : ¬ edgeCmpLT y x := by
  have hlt : compare x.1 y.1 = .lt := edgeCmpLT_eq_lt h
  have hgt : compare y.1 x.1 = .gt :=
    (Std.OrientedCmp.gt_iff_lt).2 hlt
  intro h'
  have hlt' : compare y.1 x.1 = .lt := edgeCmpLT_eq_lt h'
  have : (.gt : Ordering) = .lt := by
    exact hgt.symm.trans hlt'
  cases this

/-! ## Canonical List Extensionality -/
theorem list_eq_of_subset_pairwise {l₁ l₂ : List (Edge × Trace)}
    (h₁ : l₁.Pairwise edgeCmpLT) (h₂ : l₂.Pairwise edgeCmpLT)
    (h₁₂ : l₁ ⊆ l₂) (h₂₁ : l₂ ⊆ l₁) : l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
      cases l₂ with
      | nil => rfl
      | cons b bs =>
          have : b ∈ ([] : List (Edge × Trace)) := h₂₁ (List.mem_cons.mpr (Or.inl rfl))
          cases this
  | cons a l₁ ih =>
      have ha : a ∈ l₂ := h₁₂ (List.mem_cons.mpr (Or.inl rfl))
      cases l₂ with
      | nil => cases ha
      | cons b l₂ =>
          have h₁' := h₁
          have h₂' := h₂
          simp only [List.pairwise_cons] at h₁' h₂'
          -- a must be the head of l₂.
          have hab : a = b := by
            have ha' : a = b ∨ a ∈ l₂ := by
              simpa [List.mem_cons] using ha
            cases ha' with
            | inl hEq =>
                exact hEq
            | inr haTail =>
                have hb_lt_a : edgeCmpLT b a := h₂'.1 _ haTail
                have hba : b ≠ a := by
                  intro hEq
                  have hlt : edgeCmpLT a a := by
                    simpa [hEq] using hb_lt_a
                  exact (edgeCmpLT_asymm hlt) hlt
                have hb_mem_all : b ∈ a :: l₁ := h₂₁ (List.mem_cons.mpr (Or.inl rfl))
                have hb_mem : b ∈ l₁ := by
                  simpa [List.mem_cons, hba] using hb_mem_all
                have ha_lt_b : edgeCmpLT a b := h₁'.1 _ hb_mem
                exact False.elim ((edgeCmpLT_asymm ha_lt_b) hb_lt_a)
          subst hab

          /-! ## Canonical List Extensionality: Tail Subset Transfer -/
          -- Tails are mutually subset.
          have h₁₂' : l₁ ⊆ l₂ := by
            intro x hx
            have hx' : x ∈ a :: l₂ := h₁₂ (List.mem_cons.mpr (Or.inr hx))
            have hneq : x ≠ a := by
              have hlt : edgeCmpLT a x := h₁'.1 _ hx
              intro hEq
              have hEq' : compare a.1 x.1 = .eq :=
                (Edge.compare_eq_iff_eq a.1 x.1).2 (by simp [hEq])
              have hlt' : compare a.1 x.1 = .lt := edgeCmpLT_eq_lt hlt
              have : (.eq : Ordering) = .lt := by
                exact hEq'.symm.trans hlt'
              cases this
            simpa [List.mem_cons, hneq] using hx'
          -- Tail subset transfer for pairwise extensionality.
          have h₂₁' : l₂ ⊆ l₁ := by
            intro x hx
            have hx' : x ∈ a :: l₁ := h₂₁ (List.mem_cons.mpr (Or.inr hx))
            have hneq : x ≠ a := by
              have hlt : edgeCmpLT a x := h₂'.1 _ hx
              intro hEq
              have hEq' : compare a.1 x.1 = .eq :=
                (Edge.compare_eq_iff_eq a.1 x.1).2 (by simp [hEq])
              have hlt' : compare a.1 x.1 = .lt := edgeCmpLT_eq_lt hlt
              have : (.eq : Ordering) = .lt := by
                exact hEq'.symm.trans hlt'
              cases this
            simpa [List.mem_cons, hneq] using hx'
          have htl : l₁ = l₂ := ih (h₁ := h₁'.2) (h₂ := h₂'.2) h₁₂' h₂₁'
          simpa [htl]

/-! ## DEnv Extensional Equality -/
/-- Two DEnvs with identical find? are equal. -/
theorem DEnv_eq_of_find?_eq {D₁ D₂ : DEnv}
    (h : ∀ e, D₁.find? e = D₂.find? e) : D₁ = D₂ := by
  have hlist : D₁.list = D₂.list := by
    apply list_eq_of_subset_pairwise (h₁:=D₁.sorted) (h₂:=D₂.sorted)
    · intro p hp
      have hlookup : D₁.list.lookup p.1 = some p.2 :=
        lookup_eq_some_of_mem_pairwise (h:=D₁.sorted) hp
      have hfind : D₁.find? p.1 = some p.2 := by
        have hEq := DEnv_find?_eq_lookup (env:=D₁) (e:=p.1)
        simpa [hEq] using hlookup
      have hfind' : D₂.find? p.1 = some p.2 := by
        simpa [h p.1] using hfind
      have hlookup' : D₂.list.lookup p.1 = some p.2 := by
        have hEq := DEnv_find?_eq_lookup (env:=D₂) (e:=p.1)
        simpa [hEq] using hfind'
      exact lookup_mem hlookup'
    · intro p hp
      have hlookup : D₂.list.lookup p.1 = some p.2 :=
        lookup_eq_some_of_mem_pairwise (h:=D₂.sorted) hp
      have hfind : D₂.find? p.1 = some p.2 := by
        have hEq := DEnv_find?_eq_lookup (env:=D₂) (e:=p.1)
        simpa [hEq] using hlookup
      have hfind' : D₁.find? p.1 = some p.2 := by
        have hEq := h p.1
        simpa [hEq] using hfind
      have hlookup' : D₁.list.lookup p.1 = some p.2 := by
        have hEq := DEnv_find?_eq_lookup (env:=D₁) (e:=p.1)
        simpa [hEq] using hfind'
      exact lookup_mem hlookup'
  cases D₁ with
  | mk l₁ m₁ h₁ s₁ =>
      cases D₂ with
      | mk l₂ m₂ h₂ s₂ =>
          cases hlist
          have hmap : m₁ = m₂ := by rw [h₁, h₂]
          cases hmap
          rfl

/-! ## DEnv Union and Append Instance -/
/-- Union of DEnvs (left-biased on key collisions). -/
def DEnvUnion (D₁ D₂ : DEnv) : DEnv :=
  DEnv.ofMap <|
    RBMap.foldl (fun acc k v =>
      match acc.find? k with
      | some _ => acc
      | none => acc.insert k v) D₁.map D₂.map

instance : Append DEnv := ⟨DEnvUnion⟩

/-! ## Public Lookup and Update Operations -/
/-- Lookup a type trace for a directed edge. -/
def lookupD (env : DEnv) (e : Edge) : List ValType :=
  match env.find? e with
  | some ts => ts
  | none => []

/-- Update or insert a type trace for a directed edge.
    Empty traces are erased to preserve non-emptiness invariants. -/
def updateD (env : DEnv) (e : Edge) (ts : List ValType) : DEnv :=
  DEnv.ofMap <| env.map.insert e ts

/-! ## Lookup Preservation under Updates -/
/-- Lookup after update on the same edge. -/
theorem lookupD_update_eq (env : DEnv) (e : Edge) (ts : List ValType) :
    lookupD (updateD env e ts) e = ts := by
  cases ts with
  | nil =>
      have hEq : compare e e = .eq := by
        simp
      let m := env.map.insert e []
      have hmap : (DEnv.ofMap m).map.find? e = m.find? e := by
        simpa [DEnv.ofMap, m] using (rbmapOfList_toList_find? (m := m) (e := e))
      have hfind : m.find? e = some [] := by
        simpa [m] using
          (RBMap.find?_insert_of_eq (t := env.map) (k := e) (v := []) (k' := e) hEq)
      simp [lookupD, updateD, DEnv.find?, hmap, hfind, m]
  | cons t ts' =>
      have hEq : compare e e = .eq := by
        simp
      let m := env.map.insert e (t :: ts')
      have hmap : (DEnv.ofMap m).map.find? e = m.find? e := by
        simpa [DEnv.ofMap, m] using (rbmapOfList_toList_find? (m := m) (e := e))
      have hfind : m.find? e = some (t :: ts') := by
        simpa [m] using
          (RBMap.find?_insert_of_eq (t := env.map) (k := e) (v := t :: ts') (k' := e) hEq)
      simp [lookupD, updateD, DEnv.find?, hmap, hfind, m]

/-! ## Lookup Preservation on Distinct Edges -/
/-- Lookup after update on a different edge. -/
theorem lookupD_update_neq (env : DEnv) (e e' : Edge) (ts : List ValType) (hne : e ≠ e') :
    lookupD (updateD env e ts) e' = lookupD env e' := by
  cases ts with
  | nil =>
      have hne' : compare e' e ≠ .eq := by
        intro hEq
        exact hne ((Edge.compare_eq_iff_eq e' e).1 hEq).symm
      let m := env.map.insert e []
      have hmap : (DEnv.ofMap m).map.find? e' = m.find? e' := by
        simpa [DEnv.ofMap, m] using (rbmapOfList_toList_find? (m := m) (e := e'))
      have hfind : m.find? e' = env.map.find? e' := by
        simpa [m] using
          (RBMap.find?_insert_of_ne (t := env.map) (k := e) (v := []) (k' := e') hne')
      simp [lookupD, updateD, DEnv.find?, hmap, hfind, m]
  | cons t ts' =>
      have hne' : compare e' e ≠ .eq := by
        intro hEq
        exact hne ((Edge.compare_eq_iff_eq e' e).1 hEq).symm
      let m := env.map.insert e (t :: ts')
      have hmap : (DEnv.ofMap m).map.find? e' = m.find? e' := by
        simpa [DEnv.ofMap, m] using (rbmapOfList_toList_find? (m := m) (e := e'))
      have hfind : m.find? e' = env.map.find? e' := by
        simpa [m] using
          (RBMap.find?_insert_of_ne (t := env.map) (k := e) (v := t :: ts') (k' := e') hne')
      simp [lookupD, updateD, DEnv.find?, hmap, hfind, m]

@[simp] theorem lookupD_empty (e : Edge) : lookupD (∅ : DEnv) e = [] := by
  simp [lookupD, DEnv.find?, DEnv_map_find?_empty]

/-! ## find? Preservation under Updates -/
/-- find? after update on the same edge. -/
theorem find?_updateD_eq (env : DEnv) (e : Edge) (ts : List ValType) :
    (updateD env e ts).find? e = some ts := by
  have hEq : compare e e = .eq := by simp
  let m := env.map.insert e ts
  have hmap : (DEnv.ofMap m).map.find? e = m.find? e := by
    simpa [DEnv.ofMap, m] using (rbmapOfList_toList_find? (m := m) (e := e))
  have hfind : m.find? e = some ts := by
    simpa [m] using (RBMap.find?_insert_of_eq (t := env.map) (k := e) (v := ts) (k' := e) hEq)
  simp only [updateD, DEnv.find?, hmap, hfind, m]

/-- find? after update on a different edge. -/
theorem find?_updateD_neq (env : DEnv) (e e' : Edge) (ts : List ValType) (hne : e ≠ e') :
    (updateD env e ts).find? e' = env.find? e' := by
  have hne' : compare e' e ≠ .eq := by
    intro hEq
    exact hne ((Edge.compare_eq_iff_eq e' e).1 hEq).symm
  let m := env.map.insert e ts
  have hmap : (DEnv.ofMap m).map.find? e' = m.find? e' := by
    simpa [DEnv.ofMap, m] using (rbmapOfList_toList_find? (m := m) (e := e'))
  have hfind : m.find? e' = env.map.find? e' := by
    simpa [m] using (RBMap.find?_insert_of_ne (t := env.map) (k := e) (v := ts) (k' := e') hne')
  simp only [updateD, DEnv.find?, hmap, hfind, m]

/-! ## Queue-Style DEnv Helpers -/
/-- Append a type to the in-flight trace. -/
def appendD (env : DEnv) (e : Edge) (T : ValType) : DEnv :=
  updateD env e (lookupD env e ++ [T])

/-- Pop a type from the in-flight trace. -/
def popD (env : DEnv) (e : Edge) : Option (DEnv × ValType) :=
  match lookupD env e with
  | [] => none
  | T :: ts => some (updateD env e ts, T)


end
