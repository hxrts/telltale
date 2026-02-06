import Protocol.LocalType
import Protocol.Values
import Batteries.Data.RBMap
import Batteries.Data.RBMap.Lemmas

/-!
# MPST Environments

This module defines the runtime environments for multiparty session types:

- `Store`: Variable store mapping variables to runtime values
- `SEnv`: Type environment mapping variables to value types
- `GEnv`: Session environment mapping endpoints to local types
- `DEnv`: Delayed type environment for in-flight message traces per directed edge
- `Buffers`: Per-edge FIFO message buffers keyed by (sid, from, to)

The key difference from binary session types is that buffers and type traces
are keyed by **directed edges** `(sid, from, to)` rather than endpoints.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

noncomputable section

/-! ## Variables -/

/-- Variables are strings. -/
abbrev Var := String

/-! ## VarStore: Variable → Value -/

/-- VarStore maps variables to runtime values.
    Named VarStore to avoid collision with Iris.Std.Heap.Store. -/
abbrev VarStore := List (Var × Value)

/-- Lookup a value in the store. -/
def lookupStr (store : VarStore) (x : Var) : Option Value :=
  store.lookup x

/-- Update or insert a variable in the store. -/
def updateStr (store : VarStore) (x : Var) (v : Value) : VarStore :=
  match store with
  | [] => [(x, v)]
  | (y, w) :: rest =>
    if x = y then (x, v) :: rest
    else (y, w) :: updateStr rest x v

/-! ## SEnv: Variable → ValType -/

open Batteries

/-- SEnv maps variables to their value types (list-backed). -/
abbrev SEnv := List (Var × ValType)

/-- Lookup a type in SEnv. -/
def lookupSEnv (env : SEnv) (x : Var) : Option ValType :=
  env.lookup x

/-- Update or insert in SEnv. -/
def updateSEnv (env : SEnv) (x : Var) (T : ValType) : SEnv :=
  match env with
  | [] => [(x, T)]
  | (y, U) :: rest =>
    if x = y then (x, T) :: rest
    else (y, U) :: updateSEnv rest x T

@[simp] theorem lookupSEnv_empty (x : Var) : lookupSEnv (∅ : SEnv) x = none := by
  rfl

/-- Union of SEnvs (list append, left-biased on lookup). -/
def SEnvUnion (S₁ S₂ : SEnv) : SEnv :=
  S₁ ++ S₂

/-! ## OwnedEnv: Explicit Right/Left Boundary -/

/-- OwnedEnv splits owned variables into a right (framed) prefix and a left (local) suffix. -/
structure OwnedEnv where
  right : SEnv
  left : SEnv

@[simp] theorem OwnedEnv.eta (o : OwnedEnv) :
    OwnedEnv.mk o.right o.left = o := by cases o; rfl

instance : Inhabited OwnedEnv where
  default := { right := [], left := [] }

instance : Coe SEnv OwnedEnv where
  coe s := { right := [], left := s }

instance : EmptyCollection OwnedEnv := ⟨{ right := (∅ : SEnv), left := (∅ : SEnv) }⟩

namespace OwnedEnv

/-- Full owned environment as a single SEnv. -/
def all (S : OwnedEnv) : SEnv :=
  S.right ++ S.left

instance : Coe OwnedEnv SEnv := ⟨OwnedEnv.all⟩

/-- Lookup in the full owned environment. -/
def lookup (S : OwnedEnv) (x : Var) : Option ValType :=
  lookupSEnv (all S) x

/-- Lookup only in the right (framed) portion. -/
def lookupRight (S : OwnedEnv) (x : Var) : Option ValType :=
  lookupSEnv S.right x

/-- Lookup only in the left (local) portion. -/
def lookupLeft (S : OwnedEnv) (x : Var) : Option ValType :=
  lookupSEnv S.left x

/-- Update only the left (local) portion. -/
def updateLeft (S : OwnedEnv) (x : Var) (T : ValType) : OwnedEnv :=
  { right := S.right, left := updateSEnv S.left x T }

/-- Add a frame to the right portion (low priority within right). -/
def frameRight (Sframe : SEnv) (S : OwnedEnv) : OwnedEnv :=
  { right := S.right ++ Sframe, left := S.left }

/-- Add a frame to the left (local) portion (low priority within left). -/
def frameLeft (Sframe : SEnv) (S : OwnedEnv) : OwnedEnv :=
  { right := S.right, left := S.left ++ Sframe }

instance : HAppend OwnedEnv SEnv OwnedEnv where
  hAppend := fun S Sframe => OwnedEnv.frameLeft Sframe S

/-- Treat a plain SEnv as an owned env with empty right frame. -/
def ofLeft (S : SEnv) : OwnedEnv :=
  { right := [], left := S }

@[simp] theorem toSEnv_coe (S : OwnedEnv) : (S : SEnv) = S.right ++ S.left := by
  rfl

@[simp] theorem frameLeft_left (S : OwnedEnv) (Sframe : SEnv) :
    (S ++ Sframe).left = S.left ++ Sframe := by
  rfl

@[simp] theorem frameLeft_right (S : OwnedEnv) (Sframe : SEnv) :
    (S ++ Sframe).right = S.right := by
  rfl

@[simp] theorem toSEnv_frameLeft (S : OwnedEnv) (Sframe : SEnv) :
    ((S ++ Sframe : OwnedEnv) : SEnv) = (S : SEnv) ++ Sframe := by
  simp [OwnedEnv.all, List.append_assoc]

end OwnedEnv

/-! ## GEnv: Endpoint → LocalType -/

/-- GEnv maps session endpoints to their current local session types. -/
abbrev GEnv := List (Endpoint × LocalType)

/-- Lookup a local type in GEnv. -/
def lookupG (env : GEnv) (e : Endpoint) : Option LocalType :=
  env.lookup e

/-- Update or insert in GEnv. -/
def updateG (env : GEnv) (e : Endpoint) (L : LocalType) : GEnv :=
  match env with
  | [] => [(e, L)]
  | (e', L') :: rest =>
    if e = e' then (e, L) :: rest
    else (e', L') :: updateG rest e L

/-! ## Directed Edge Buffers -/

/-- A buffer is a FIFO queue of values. -/
abbrev Buffer := List Value

/-- Buffers maps directed edges to their message queues.
    Each buffer holds messages from `e.sender` to `e.receiver`. -/
abbrev Buffers := List (Edge × Buffer)

/-- Lookup a buffer for a directed edge. -/
def lookupBuf (bufs : Buffers) (e : Edge) : Buffer :=
  bufs.lookup e |>.getD []

/-- Update a buffer for a directed edge. -/
def updateBuf (bufs : Buffers) (e : Edge) (buf : Buffer) : Buffers :=
  match bufs with
  | [] => [(e, buf)]
  | (e', buf') :: rest =>
    if e = e' then (e, buf) :: rest
    else (e', buf') :: updateBuf rest e buf

/-- Enqueue a value at a directed edge buffer. -/
def enqueueBuf (bufs : Buffers) (e : Edge) (v : Value) : Buffers :=
  updateBuf bufs e (lookupBuf bufs e ++ [v])

/-- Dequeue from a directed edge buffer (returns updated buffers and value). -/
def dequeueBuf (bufs : Buffers) (e : Edge) : Option (Buffers × Value) :=
  match lookupBuf bufs e with
  | [] => none
  | v :: vs => some (updateBuf bufs e vs, v)

/-! ## DEnv: Directed Edge → Type Trace -/
/-! ## DEnv: Directed Edge → Type Trace -/

/-- A trace stored in DEnv. Empty traces are treated as missing. -/
abbrev Trace := List ValType

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

private def rbmapOfList (l : List (Edge × Trace)) : RBMap Edge Trace compare :=
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

private theorem find?_foldl_insert_of_pairwise
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

private theorem rbmap_find?_ofList_eq_lookup
    (l : List (Edge × Trace)) (h : l.Pairwise edgeCmpLT) (k : Edge) :
    (rbmapOfList l).find? k = l.lookup k := by
  have h' := find?_foldl_insert_of_pairwise (l := l) (m := (∅ : RBMap Edge Trace compare)) h k
  cases hLookup : l.lookup k <;>
    simpa [rbmapOfList, rbmap_find?_empty, hLookup] using h'

theorem DEnv_find?_eq_lookup (env : DEnv) (e : Edge) :
    env.find? e = env.list.lookup e := by
  have h := rbmap_find?_ofList_eq_lookup (l := env.list) (h := env.sorted) (k := e)
  simp [DEnv.find?, env.map_eq, h]

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

private theorem rbmapOfList_toList_find? (m : RBMap Edge Trace compare) (e : Edge) :
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

private lemma edgeCmpLT_asymm {x y : Edge × Trace} (h : edgeCmpLT x y) : ¬ edgeCmpLT y x := by
  have hlt : compare x.1 y.1 = .lt := edgeCmpLT_eq_lt h
  have hgt : compare y.1 x.1 = .gt :=
    (Std.OrientedCmp.gt_iff_lt).2 hlt
  intro h'
  have hlt' : compare y.1 x.1 = .lt := edgeCmpLT_eq_lt h'
  have : (.gt : Ordering) = .lt := by
    exact hgt.symm.trans hlt'
  cases this

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
          -- a must be the head of l₂
          have hab : a = b := by
            have ha' : a = b ∨ a ∈ l₂ := by
              simpa [List.mem_cons] using ha
            cases ha' with
            | inl hEq => exact hEq
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
                exact (edgeCmpLT_asymm ha_lt_b hb_lt_a).elim
          subst hab
          -- tails are mutually subset
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
          simp [htl]

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

/-- Union of DEnvs (left-biased on key collisions). -/
def DEnvUnion (D₁ D₂ : DEnv) : DEnv :=
  DEnv.ofMap <|
    RBMap.foldl (fun acc k v =>
      match acc.find? k with
      | some _ => acc
      | none => acc.insert k v) D₁.map D₂.map

instance : Append DEnv := ⟨DEnvUnion⟩

/-- Lookup a type trace for a directed edge. -/
def lookupD (env : DEnv) (e : Edge) : List ValType :=
  match env.find? e with
  | some ts => ts
  | none => []

/-- Update or insert a type trace for a directed edge.
    Empty traces are erased to preserve non-emptiness invariants. -/
def updateD (env : DEnv) (e : Edge) (ts : List ValType) : DEnv :=
  DEnv.ofMap <| env.map.insert e ts

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

/-- Append a type to the in-flight trace. -/
def appendD (env : DEnv) (e : Edge) (T : ValType) : DEnv :=
  updateD env e (lookupD env e ++ [T])

/-- Pop a type from the in-flight trace. -/
def popD (env : DEnv) (e : Edge) : Option (DEnv × ValType) :=
  match lookupD env e with
  | [] => none
  | T :: ts => some (updateD env e ts, T)

/-! ## Session Management -/

/-- Initialize empty buffers for all directed edges between roles. -/
def initBuffers (sid : SessionId) (roles : RoleSet) : Buffers :=
  (RoleSet.allEdges sid roles).map fun e => (e, [])

/-- Initialize empty type traces for all directed edges. -/
def initDEnv (_sid : SessionId) (_roles : RoleSet) : DEnv :=
  ∅

/-- Empty DEnv lookup via `find?` always returns none. -/
@[simp] theorem DEnv_find?_empty (e : Edge) :
    (∅ : DEnv).find? e = none := by
  simp [DEnv.find?, DEnv_map_find?_empty]

theorem DEnvUnion_empty_right (D : DEnv) : DEnvUnion D (∅ : DEnv) = D := by
  apply DEnv_eq_of_find?_eq
  intro e
  simp only [DEnvUnion, DEnv_find?_ofMap]
  rw [Batteries.RBMap.foldl_eq_foldl_toList]
  have : (∅ : DEnv).map.toList = [] := rfl
  rw [this, List.foldl_nil]
  simp [DEnv.find?]

theorem DEnvUnion_empty_left (D : DEnv) : DEnvUnion (∅ : DEnv) D = D := by
  apply DEnv_eq_of_find?_eq
  intro e
  -- (DEnvUnion ∅ D).find? e = D.find? e
  -- DEnvUnion folds D.map into (∅).map with conditional insert.
  -- Starting from empty, every key is new, so all inserts happen.
  -- The result has the same find? as D.map.
  simp only [DEnvUnion, DEnv_find?_ofMap]
  rw [Batteries.RBMap.foldl_eq_foldl_toList]
  -- Goal: (DEnv.ofMap (D.map.toList.foldl f (∅).map)).find? e = D.find? e
  -- where f is the conditional insert.
  -- Suffices to show the foldl equals rbmapOfList D.map.toList
  suffices hFold :
    D.map.toList.foldl (fun acc (p : Edge × Trace) =>
      match acc.find? p.1 with
      | some _ => acc
      | none => acc.insert p.1 p.2) (∅ : DEnv).map =
    rbmapOfList D.map.toList by
    rw [hFold]
    exact rbmapOfList_toList_find? D.map e
  -- Since we start from empty, acc.find? is always none for unseen keys.
  -- With unique keys (from sorted), every key is unseen.
  have hSorted : D.map.toList.Pairwise edgeCmpLT := by
    simpa [edgeCmpLT] using RBMap.toList_sorted (t := D.map)
  unfold rbmapOfList
  generalize D.map.toList = pairs at hSorted
  suffices h : ∀ (acc : RBMap Edge Trace compare) (ps : List (Edge × Trace)),
    ps.Pairwise edgeCmpLT →
    (∀ p ∈ ps, acc.find? p.1 = none) →
    ps.foldl (fun acc (p : Edge × Trace) =>
      match acc.find? p.1 with
      | some _ => acc
      | none => acc.insert p.1 p.2) acc =
    ps.foldl (fun r (p : Edge × Trace) => r.insert p.1 p.2) acc from
    h _ pairs hSorted (fun p _ => rbmap_find?_empty p.1)
  intro acc ps hPW
  induction ps generalizing acc with
  | nil => intro _; rfl
  | cons p ps ih =>
    intro hNone
    simp only [List.foldl_cons]
    have hNoneP := hNone p (by simp)
    rw [hNoneP]
    have hPW' := (List.pairwise_cons.1 hPW)
    refine ih (acc := acc.insert p.1 p.2) hPW'.2 ?_
    intro q hq
    have hNoneQ := hNone q (List.mem_cons_of_mem p hq)
    have hLT := hPW'.1 q hq
    have hCmpLT := edgeCmpLT_eq_lt hLT
    have hNe : compare q.1 p.1 ≠ .eq := by
      intro heq
      have := Std.OrientedCmp.eq_swap (cmp := compare) (a := q.1) (b := p.1)
      simp [heq, hCmpLT] at this
    have := RBMap.find?_insert_of_ne (t := acc) (k := p.1) (v := p.2) (k' := q.1) hNe
    simpa [this] using hNoneQ

/-- Looking up an edge in initBuffers returns empty if edge is in allEdges. -/
theorem initBuffers_lookup_mem (sid : SessionId) (roles : RoleSet) (e : Edge)
    (hMem : e ∈ RoleSet.allEdges sid roles) :
    (initBuffers sid roles).lookup e = some [] := by
  simp only [initBuffers]
  generalize hEdges : RoleSet.allEdges sid roles = edges at hMem
  clear hEdges
  induction edges with
  | nil => simp only [List.mem_nil_iff] at hMem
  | cons hd tl ih =>
    simp only [List.map, List.lookup]
    simp only [List.mem_cons] at hMem
    cases hMem with
    | inl heq =>
      subst heq
      simp only [beq_self_eq_true]
    | inr hTl =>
      by_cases heq : e = hd
      · subst heq; simp only [beq_self_eq_true]
      · have hNeq : (e == hd) = false := beq_eq_false_iff_ne.mpr heq
        simp only [hNeq]
        exact ih hTl

/-- Looking up an edge in initDEnv returns empty if edge is in allEdges. -/
theorem initDEnv_lookup_mem (sid : SessionId) (roles : RoleSet) (e : Edge)
    (_hMem : e ∈ RoleSet.allEdges sid roles) :
    lookupD (initDEnv sid roles) e = [] := by
  simp [initDEnv, lookupD]

/-- Looking up an edge with a different sid in initDEnv returns none. -/
theorem initDEnv_lookup_none (sid : SessionId) (roles : RoleSet) (e : Edge)
    (_hne : e.sid ≠ sid) :
    lookupD (initDEnv sid roles) e = [] := by
  simp [initDEnv, lookupD]

/-- If initBuffers returns none, the edge is not in the role edges. -/
theorem initBuffers_not_mem_of_lookup_none (sid : SessionId) (roles : RoleSet) (e : Edge)
    (h : (initBuffers sid roles).lookup e = none) :
    e ∉ RoleSet.allEdges sid roles := by
  -- Any edge in allEdges would be found with an empty buffer.
  intro hMem
  have hSome := initBuffers_lookup_mem sid roles e hMem
  exact Option.noConfusion (hSome.symm.trans h)

/-- initBuffers returns none for edges not in allEdges. -/
theorem initBuffers_lookup_none_of_notin (sid : SessionId) (roles : RoleSet) (e : Edge)
    (hNot : e ∉ RoleSet.allEdges sid roles) :
    (initBuffers sid roles).lookup e = none := by
  simp only [initBuffers]
  generalize hEdges : RoleSet.allEdges sid roles = edges at hNot
  clear hEdges
  induction edges with
  | nil =>
      simp
  | cons hd tl ih =>
      simp only [List.mem_cons, not_or] at hNot
      simp only [List.map, List.lookup]
      have hne : (e == hd) = false := beq_eq_false_iff_ne.mpr hNot.1
      simp only [hne]
      exact ih hNot.2

/-- Looking up an edge with a different sid in initBuffers returns none. -/
theorem initBuffers_lookup_none (sid : SessionId) (roles : RoleSet) (e : Edge)
    (hne : e.sid ≠ sid) :
    (initBuffers sid roles).lookup e = none := by
  simp only [initBuffers]
  -- Every edge in allEdges has .sid = sid, so e cannot be in the list
  have hNotIn : e ∉ RoleSet.allEdges sid roles := by
    intro hmem
    exact hne (RoleSet.allEdges_sid sid roles e hmem)
  -- Use induction with the membership constraint carried through
  generalize hlist : RoleSet.allEdges sid roles = edges at hNotIn
  clear hlist
  induction edges with
  | nil => simp only [List.map, List.lookup]
  | cons hd tl ih =>
    simp only [List.mem_cons, not_or] at hNotIn
    simp only [List.map, List.lookup]
    have hNeEdge : e ≠ hd := hNotIn.1
    have hBeqFalse : (e == hd) = false := beq_eq_false_iff_ne.mpr hNeEdge
    simp only [hBeqFalse]
    exact ih hNotIn.2

/-- initDEnv has no entry for edges outside allEdges. -/
theorem initDEnv_find?_none_of_notin (sid : SessionId) (roles : RoleSet) (e : Edge)
    (_hNot : e ∉ RoleSet.allEdges sid roles) :
    (initDEnv sid roles).find? e = none := by
  simp [initDEnv, DEnv.find?, DEnv_map_find?_empty]

/-! ## Environment Lemmas -/

theorem lookupStr_update_eq (store : VarStore) (x : Var) (v : Value) :
    lookupStr (updateStr store x v) x = some v := by
  induction store with
  | nil =>
    simp only [updateStr, lookupStr, List.lookup, beq_self_eq_true]
  | cons hd tl ih =>
    simp only [updateStr]
    split_ifs with h
    · simp only [lookupStr, List.lookup, beq_self_eq_true]
    · simp only [lookupStr, List.lookup]
      have hne : (x == hd.1) = false := beq_eq_false_iff_ne.mpr h
      simp only [hne]
      exact ih

theorem lookupStr_update_neq (store : VarStore) (x y : Var) (v : Value) (hne : x ≠ y) :
    lookupStr (updateStr store x v) y = lookupStr store y := by
  induction store with
  | nil =>
    simp only [updateStr, lookupStr, List.lookup]
    have h : (y == x) = false := beq_eq_false_iff_ne.mpr (Ne.symm hne)
    simp only [h]
  | cons hd tl ih =>
    simp only [updateStr]
    split_ifs with h
    · -- h : x = hd.1, so y ≠ x implies y ≠ hd.1
      simp only [lookupStr, List.lookup]
      have hyx : (y == x) = false := beq_eq_false_iff_ne.mpr (Ne.symm hne)
      have hyh : (y == hd.1) = false := beq_eq_false_iff_ne.mpr (h ▸ Ne.symm hne)
      simp only [hyx, hyh]
    · simp only [lookupStr, List.lookup]
      by_cases hy : y = hd.1
      · simp only [hy, beq_self_eq_true]
      · have hne' : (y == hd.1) = false := beq_eq_false_iff_ne.mpr hy
        simp only [hne']
        exact ih

theorem lookupSEnv_update_eq (env : SEnv) (x : Var) (T : ValType) :
    lookupSEnv (updateSEnv env x T) x = some T := by
  induction env with
  | nil =>
      simp [lookupSEnv, updateSEnv]
  | cons hd tl ih =>
      simp only [updateSEnv]
      split_ifs with h
      · simp [lookupSEnv, h, List.lookup]
      · simp [lookupSEnv, List.lookup, beq_eq_false_iff_ne.mpr h] at *
        exact ih

theorem lookupSEnv_update_neq (env : SEnv) (x y : Var) (T : ValType) (hne : x ≠ y) :
    lookupSEnv (updateSEnv env x T) y = lookupSEnv env y := by
  induction env with
  | nil =>
      by_cases hy : y = x
      · exact (hne hy.symm).elim
      · have hbeq : (y == x) = false := beq_eq_false_iff_ne.mpr hy
        simp [lookupSEnv, updateSEnv, List.lookup, hbeq]
  | cons hd tl ih =>
      by_cases h : x = hd.1
      · have hy : y ≠ hd.1 := by
          intro hy
          exact hne (h.trans hy.symm)
        have hy' : (y == hd.1) = false := beq_eq_false_iff_ne.mpr hy
        simp [updateSEnv, lookupSEnv, List.lookup, h, hy']
      · simp [updateSEnv, lookupSEnv, List.lookup, h] at *
        by_cases hy : y = hd.1
        · simp [hy]
        · have hy' : (y == hd.1) = false := beq_eq_false_iff_ne.mpr hy
          simp [hy', ih]

theorem lookupG_update_eq (env : GEnv) (e : Endpoint) (L : LocalType) :
    lookupG (updateG env e L) e = some L := by
  induction env with
  | nil =>
    simp only [updateG, lookupG, List.lookup, beq_self_eq_true]
  | cons hd tl ih =>
    simp only [updateG]
    split_ifs with h
    · simp only [lookupG, List.lookup, beq_self_eq_true]
    · simp only [lookupG, List.lookup]
      have hne : (e == hd.1) = false := beq_eq_false_iff_ne.mpr h
      simp only [hne]
      exact ih

theorem lookupG_update_neq (env : GEnv) (e e' : Endpoint) (L : LocalType) (hne : e ≠ e') :
    lookupG (updateG env e L) e' = lookupG env e' := by
  induction env with
  | nil =>
    simp only [updateG, lookupG, List.lookup]
    have h : (e' == e) = false := beq_eq_false_iff_ne.mpr (Ne.symm hne)
    simp only [h]
  | cons hd tl ih =>
    simp only [updateG]
    split_ifs with h
    · -- h : e = hd.1, so e' ≠ e implies e' ≠ hd.1
      simp only [lookupG, List.lookup]
      have h1 : (e' == e) = false := beq_eq_false_iff_ne.mpr (Ne.symm hne)
      have h2 : (e' == hd.1) = false := beq_eq_false_iff_ne.mpr (h ▸ Ne.symm hne)
      simp only [h1, h2]
    · simp only [lookupG, List.lookup]
      by_cases hy : e' = hd.1
      · simp only [hy, beq_self_eq_true]
      · have hne' : (e' == hd.1) = false := beq_eq_false_iff_ne.mpr hy
        simp only [hne']
        exact ih

/-- If (e', S') ∈ updateG env e L, then either (e' = e and S' = L), or (e', S') was in env. -/
theorem updateG_mem_of (env : GEnv) (e : Endpoint) (L : LocalType) (e' : Endpoint) (S' : LocalType)
    (h : (e', S') ∈ updateG env e L) :
    (e' = e ∧ S' = L) ∨ (e', S') ∈ env := by
  induction env with
  | nil =>
    simp only [updateG, List.mem_singleton] at h
    exact Or.inl (Prod.mk.inj h)
  | cons hd tl ih =>
    simp only [updateG] at h
    split_ifs at h with heq
    · -- e = hd.1: replaced the head
      simp only [List.mem_cons] at h
      cases h with
      | inl hhead =>
        exact Or.inl (Prod.mk.inj hhead)
      | inr htl =>
        exact Or.inr (List.mem_cons_of_mem _ htl)
    · -- e ≠ hd.1: head preserved, recurse
      simp only [List.mem_cons] at h
      cases h with
      | inl hhead =>
        exact Or.inr (List.mem_cons.mpr (Or.inl hhead))
      | inr htl =>
        cases ih htl with
        | inl heq' => exact Or.inl heq'
        | inr hmem => exact Or.inr (List.mem_cons.mpr (Or.inr hmem))

/-- updateG preserves supply_fresh: if all endpoints in env have sid < supply,
    and e.sid < supply, then all endpoints in (updateG env e L) have sid < supply. -/
theorem updateG_preserves_supply_fresh (env : GEnv) (e : Endpoint) (L : LocalType)
    (supply : SessionId)
    (hFresh : ∀ e' S', (e', S') ∈ env → e'.sid < supply)
    (heFresh : e.sid < supply) :
    ∀ e' S', (e', S') ∈ updateG env e L → e'.sid < supply := by
  intro e' S' hMem
  cases updateG_mem_of env e L e' S' hMem with
  | inl heq =>
    rw [heq.1]
    exact heFresh
  | inr hmem =>
    exact hFresh e' S' hmem

/-- If lookupG returns some L, then (e, L) is in the list. -/
theorem lookupG_mem (env : GEnv) (e : Endpoint) (L : LocalType)
    (h : lookupG env e = some L) :
    (e, L) ∈ env := by
  simp only [lookupG] at h
  induction env with
  | nil =>
    simp only [List.lookup] at h
    exact Option.noConfusion h
  | cons hd tl ih =>
    simp only [List.lookup] at h
    split at h
    · simp only [Option.some.injEq] at h
      rename_i heq
      simp only [beq_iff_eq] at heq
      simp only [List.mem_cons]
      left
      exact Prod.ext heq h.symm
    · simp only [List.mem_cons]
      right
      exact ih h

/-- If lookupG returns some L, then e.sid < supply (using supply_fresh_G). -/
theorem lookupG_supply_fresh (env : GEnv) (e : Endpoint) (L : LocalType)
    (supply : SessionId)
    (hFresh : ∀ e' S', (e', S') ∈ env → e'.sid < supply)
    (h : lookupG env e = some L) :
    e.sid < supply := by
  have hMem := lookupG_mem env e L h
  exact hFresh e L hMem

theorem lookupBuf_update_eq (bufs : Buffers) (e : Edge) (buf : Buffer) :
    lookupBuf (updateBuf bufs e buf) e = buf := by
  induction bufs with
  | nil =>
    simp only [updateBuf, lookupBuf, List.lookup, beq_self_eq_true, Option.getD]
  | cons hd tl ih =>
    simp only [updateBuf]
    split_ifs with h
    · simp only [lookupBuf, List.lookup, beq_self_eq_true, Option.getD]
    · simp only [lookupBuf, List.lookup]
      have hne : (e == hd.1) = false := beq_eq_false_iff_ne.mpr h
      simp only [hne, Option.getD]
      have ih' := ih
      simp only [lookupBuf, Option.getD] at ih'
      exact ih'

theorem lookupBuf_update_neq (bufs : Buffers) (e e' : Edge) (buf : Buffer) (hne : e ≠ e') :
    lookupBuf (updateBuf bufs e buf) e' = lookupBuf bufs e' := by
  induction bufs with
  | nil =>
    simp only [updateBuf, lookupBuf, List.lookup]
    have h : (e' == e) = false := beq_eq_false_iff_ne.mpr (Ne.symm hne)
    simp only [h, Option.getD]
  | cons hd tl ih =>
    simp only [updateBuf]
    split_ifs with h
    · -- h : e = hd.1, so e' ≠ e implies e' ≠ hd.1
      simp only [lookupBuf, List.lookup]
      have h1 : (e' == e) = false := beq_eq_false_iff_ne.mpr (Ne.symm hne)
      have h2 : (e' == hd.1) = false := beq_eq_false_iff_ne.mpr (h ▸ Ne.symm hne)
      simp only [h1, h2, Option.getD]
    · simp only [lookupBuf, List.lookup]
      by_cases hy : e' = hd.1
      · simp only [hy, beq_self_eq_true, Option.getD]
      · have hne' : (e' == hd.1) = false := beq_eq_false_iff_ne.mpr hy
        simp only [hne', Option.getD]
        have ih' := ih
        simp only [lookupBuf, Option.getD] at ih'
        exact ih'

-- lookupD lemmas are defined above near DEnv.


end
