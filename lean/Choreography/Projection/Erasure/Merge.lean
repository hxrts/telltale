import Choreography.Projection.Erasure.Core

/-! # Choreography.Projection.Erasure.Merge

Label predicates and merge algorithm for erasure.
-/
namespace Choreography.Projection.Erasure
open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
section
open Classical
/-! ## Label Predicates -/

/-- Boolean label-in predicate for branch lists. -/
def labelInb (lbl : Label) (branches : List BranchR) : Bool :=
  match lookupBranch lbl branches with
  | some _ => true
  | none => false
/-- Label subset as a boolean check. -/
def labelsSubsetb (bs1 bs2 : List BranchR) : Bool :=
  bs1.all (fun p => labelInb p.1 bs2)
/-- Branches from bs2 whose labels are missing in bs1. -/
def appendMissing (bs2 bs1 : List BranchR) : List BranchR :=
  match bs2 with
  | [] => []
  | (lbl, t) :: rest =>
      if labelInb lbl bs1 then
        appendMissing rest bs1
      else
        (lbl, t) :: appendMissing rest bs1
/-- Label subset predicate (Prop). -/
def labelsSubset (bs1 bs2 : List BranchR) : Prop :=
  ∀ lbl, labelIn lbl bs1 → labelIn lbl bs2
private theorem labelIn_head (lbl : Label) (vt : Option SessionTypes.ValType) (t : LocalTypeR) (rest : List BranchR) :
    labelIn lbl ((lbl, vt, t) :: rest) := by
  unfold labelIn lookupBranch
  simp
theorem labelIn_tail_of_ne {lbl l : Label} {vt : Option SessionTypes.ValType} {t : LocalTypeR}
    {rest : List BranchR} (h : l ≠ lbl) :
    labelIn lbl ((l, vt, t) :: rest) ↔ labelIn lbl rest := by
  cases rest with
  | nil =>
      simp [labelIn, lookupBranch, h]
  | cons head tail =>
      simp [labelIn, lookupBranch, h]
/-- lookupBranch success implies membership. -/
theorem mem_of_lookupBranch {lbl : Label} {t : LocalTypeR} {bs : List BranchR}
    (h : lookupBranch lbl bs = some t) : ∃ vt, (lbl, vt, t) ∈ bs := by
  induction bs with
  | nil =>
      cases h
  | cons head tail ih =>
      obtain ⟨l, vt0, t0⟩ := head
      by_cases hlt : l = lbl
      · subst hlt
        simp [lookupBranch] at h
        cases h
        exact ⟨vt0, List.Mem.head _⟩
      · simp [lookupBranch, hlt] at h
        obtain ⟨vt, hmem⟩ := ih h
        exact ⟨vt, List.mem_cons_of_mem _ hmem⟩
/-- sameLabels from both subset directions. -/
theorem sameLabels_of_subsets {bs1 bs2 : List BranchR}
    (h12 : labelsSubset bs1 bs2) (h21 : labelsSubset bs2 bs1) :
    sameLabels bs1 bs2 := by
  intro lbl
  constructor
  · intro h; exact h12 lbl h
  · intro h; exact h21 lbl h
/-- labelsSubsetb implies labelsSubset. -/
theorem labelsSubset_of_labelsSubsetb {bs1 bs2 : List BranchR}
    (h : labelsSubsetb bs1 bs2 = true) :
    labelsSubset bs1 bs2 := by
  induction bs1 with
  | nil =>
      intro lbl hIn
      simp [labelIn, lookupBranch] at hIn
  | cons head tail ih =>
      intro lbl hIn
      obtain ⟨l, vt, t⟩ := head
      have h' : labelInb l bs2 = true ∧ labelsSubsetb tail bs2 = true := by
        simpa [labelsSubsetb, List.all, Bool.and_eq_true] using h
      by_cases hlt : l = lbl
      ·
        have h'1 : labelInb lbl bs2 = true := by
          simpa [hlt] using h'.1
        cases hlookup2 : lookupBranch lbl bs2 with
        | none =>
            have : False := by
              simp [labelInb, hlookup2] at h'1
            exact this.elim
        | some _ =>
            simp [labelIn, hlookup2]
      ·
        have hIn_tail : labelIn lbl tail :=
          (labelIn_tail_of_ne (lbl := lbl) (l := l) (vt := vt) (t := t) (rest := tail) hlt).1 hIn
        exact ih h'.2 lbl hIn_tail
theorem appendMissing_nil (bs : List BranchR) :
    appendMissing bs [] = bs := by
  induction bs with
  | nil => rfl
  | cons head tail ih =>
      cases head with
      | mk lbl t =>
          simp [appendMissing, labelInb, lookupBranch, ih]
private theorem labelInb_of_lookup_none {lbl : Label} {bs : List BranchR}
    (h : lookupBranch lbl bs = none) : labelInb lbl bs = false := by
  simp [labelInb, h]
private theorem lookupBranch_appendMissing_of_not_in
    {lbl : Label} {bs2 bs1 : List BranchR}
    (hnot : lookupBranch lbl bs1 = none) :
    lookupBranch lbl (appendMissing bs2 bs1) = lookupBranch lbl bs2 := by
  induction bs2 with
  | nil => simp [appendMissing]
  | cons head tail ih =>
      cases head with
      | mk l t =>
          by_cases hlt : l = lbl
          ·
            have hfalse : labelInb lbl bs1 = false := by
              simpa [hlt] using (labelInb_of_lookup_none (lbl := lbl) hnot)
            simp [appendMissing, hfalse, lookupBranch, hlt]
          · by_cases hIn : labelInb l bs1 = true
            ·
              have happend : appendMissing ((l, t) :: tail) bs1 = appendMissing tail bs1 := by
                simp [appendMissing, hIn]
              calc
                lookupBranch lbl (appendMissing ((l, t) :: tail) bs1) =
                    lookupBranch lbl (appendMissing tail bs1) := by simp [happend]
                _ = lookupBranch lbl tail := ih
                _ = lookupBranch lbl ((l, t) :: tail) := by
                  simp [lookupBranch, hlt]
            ·
              have happend : appendMissing ((l, t) :: tail) bs1 = (l, t) :: appendMissing tail bs1 := by
                simp [appendMissing, hIn]
              calc
                lookupBranch lbl (appendMissing ((l, t) :: tail) bs1) =
                    lookupBranch lbl ((l, t) :: appendMissing tail bs1) := by simp [happend]
                _ = lookupBranch lbl (appendMissing tail bs1) := by simp [lookupBranch, hlt]
                _ = lookupBranch lbl tail := ih
                _ = lookupBranch lbl ((l, t) :: tail) := by
                  simp [lookupBranch, hlt]

/-! ## Merge Algorithm -/

private def lookupBranchEq (lbl : Label) :
    (bs : List BranchR) →
      Option { t : LocalTypeR // lookupBranch lbl bs = some t }
  | [] => none
  | (l, _vt, t) :: rest =>
      if h : l = lbl then
        some ⟨t, by simp [lookupBranch, h]⟩
      else
        match lookupBranchEq lbl rest with
        | none => none
        | some ⟨t', h'⟩ => some ⟨t', by simpa [lookupBranch, h] using h'⟩

private lemma lookupBranchEq_none {lbl : Label} :
    ∀ bs, lookupBranchEq lbl bs = none → lookupBranch lbl bs = none
  | [] => by
      intro _
      simp [lookupBranch]
  | (l, _vt, t) :: rest => by
      intro h
      by_cases hl : l = lbl
      ·
        have : False := by
          simp [lookupBranchEq, lookupBranch, hl] at h
        exact this.elim
      ·
        cases hrest : lookupBranchEq lbl rest with
        | none =>
            have hrest' := lookupBranchEq_none rest hrest
            simp [lookupBranch, hl, hrest']
        | some ht =>
            have : False := by
              simp [lookupBranchEq, hl, hrest] at h
            exact this.elim

mutual
  /-- Merge two local types, returning a common erasure if possible. -/
  def merge : LocalTypeR → LocalTypeR → Option LocalTypeR
    | .end, .end => some .end
    | .var v, .var w => if v = w then some (.var v) else none
    | .mu v a, .mu w b =>
        if _h : v = w then
          match merge a b with
          | some c => some (.mu v c)
          | none => none
        else
          none
    | .send p bs1, .send q bs2 =>
        if _h : p = q then
          match mergeBranchesSend bs1 bs2 with
          | some bs =>
              if labelsSubsetb bs2 bs1 then some (.send p bs) else none
          | none => none
        else
          none
    | .recv p bs1, .recv q bs2 =>
        if _h : p = q then
          match mergeBranchesRecv bs1 bs2 with
          | some bs => some (.recv p bs)
          | none => none
        else
          none
    | _, _ => none
  termination_by a b => sizeOf a + sizeOf b
  decreasing_by
    all_goals
      first
      | exact Nat.add_lt_add (sizeOf_body_lt_sizeOf_mu _ _) (sizeOf_body_lt_sizeOf_mu _ _)
      | exact Nat.add_lt_add (sizeOf_branches_lt_sizeOf_send _ _) (sizeOf_branches_lt_sizeOf_send _ _)
  /-- Merge send branches using `merge` on continuations. -/
  def mergeBranchesSend : List BranchR → List BranchR →
      Option (List BranchR)
    | [], bs2 => if labelsSubsetb bs2 [] then some [] else none
    | (lbl, vt1, t1) :: rest, bs2 =>
        match lookupBranchEq lbl bs2 with
        | none => none
        | some ⟨t2, _hlookup⟩ =>
            match merge t1 t2, mergeBranchesSend rest bs2 with
            | some t, some rest' => some ((lbl, vt1, t) :: rest')
            | _, _ => none
  termination_by bs1 bs2 => sizeOf bs1 + sizeOf bs2
  decreasing_by
    all_goals
      first
      | exact Nat.add_lt_add_right (sizeOf_tail_lt_sizeOf_branches (head := (lbl, vt1, t1)) (tail := rest)) _
      | -- merge call on branch continuations
        have hlookup' : lookupBranch lbl bs2 = some t2 := _hlookup
        have hmem2 : ∃ vt, (lbl, vt, t2) ∈ bs2 := mem_of_lookupBranch hlookup'
        obtain ⟨vt2, hmem2'⟩ := hmem2
        have hlt1 : sizeOf t1 < sizeOf ((lbl, vt1, t1) :: rest) :=
          sizeOf_cont_lt_sizeOf_branches lbl vt1 t1 rest
        have hmem2_cont : t2 ∈ bs2.map BranchR.cont := by
          exact List.mem_map.2 ⟨(lbl, vt2, t2), hmem2', rfl⟩
        have hlt2 : sizeOf t2 < sizeOf bs2 :=
          sizeOf_cont_lt_sizeOf_branches_mem hmem2_cont
        exact Nat.add_lt_add hlt1 hlt2
  /-- Merge recv branches using `merge` on continuations. -/
  def mergeBranchesRecv : List BranchR → List BranchR →
      Option (List BranchR)
    | [], bs2 => some (appendMissing bs2 [])
    | (lbl, vt1, t1) :: rest, bs2 =>
        match lookupBranchEq lbl bs2 with
        | none =>
            match mergeBranchesRecv rest bs2 with
            | some rest' => some ((lbl, vt1, t1) :: rest')
            | none => none
        | some ⟨t2, _hlookup⟩ =>
            match merge t1 t2, mergeBranchesRecv rest bs2 with
            | some t, some rest' => some ((lbl, vt1, t) :: rest')
            | _, _ => none
  termination_by bs1 bs2 => sizeOf bs1 + sizeOf bs2
  decreasing_by
    all_goals
      first
      | exact Nat.add_lt_add_right (sizeOf_tail_lt_sizeOf_branches (head := (lbl, vt1, t1)) (tail := rest)) _
      | -- merge call on branch continuations
        have hlookup' : lookupBranch lbl bs2 = some t2 := _hlookup
        have hmem2 : ∃ vt, (lbl, vt, t2) ∈ bs2 := mem_of_lookupBranch hlookup'
        obtain ⟨vt2, hmem2'⟩ := hmem2
        have hlt1 : sizeOf t1 < sizeOf ((lbl, vt1, t1) :: rest) :=
          sizeOf_cont_lt_sizeOf_branches lbl vt1 t1 rest
        have hmem2_cont : t2 ∈ bs2.map BranchR.cont := by
          exact List.mem_map.2 ⟨(lbl, vt2, t2), hmem2', rfl⟩
        have hlt2 : sizeOf t2 < sizeOf bs2 :=
          sizeOf_cont_lt_sizeOf_branches_mem hmem2_cont
        exact Nat.add_lt_add hlt1 hlt2
end

theorem mergeBranchesSend_eq_some {lbl : Label} {vt1 : Option SessionTypes.ValType} {t1 : LocalTypeR}
    {rest bs2 bs : List BranchR}
    (h : mergeBranchesSend ((lbl, vt1, t1) :: rest) bs2 = some bs) :
    ∃ t2 t rest',
      lookupBranch lbl bs2 = some t2 ∧
      merge t1 t2 = some t ∧
      mergeBranchesSend rest bs2 = some rest' ∧
      bs = (lbl, vt1, t) :: rest' := by
  classical
  cases hlookupEq : lookupBranchEq lbl bs2 with
  | none =>
      simp [mergeBranchesSend, hlookupEq] at h
  | some ht =>
      rcases ht with ⟨t2, hlookup⟩
      cases hmerge : merge t1 t2 with
      | none =>
          simp [mergeBranchesSend, hlookupEq, hmerge] at h
      | some t =>
          cases hrest : mergeBranchesSend rest bs2 with
          | none =>
              simp [mergeBranchesSend, hlookupEq, hmerge, hrest] at h
          | some rest' =>
              simp [mergeBranchesSend, hlookupEq, hmerge, hrest] at h
              refine ⟨t2, t, rest', ?_, ?_, ?_, ?_⟩
              · simp [hlookup]
              · simp [hmerge]
              · rfl
              · cases h; rfl

theorem mergeBranchesRecv_eq_some {lbl : Label} {vt1 : Option SessionTypes.ValType} {t1 : LocalTypeR}
    {rest bs2 bs : List BranchR}
    (h : mergeBranchesRecv ((lbl, vt1, t1) :: rest) bs2 = some bs) :
    (lookupBranch lbl bs2 = none ∧
        ∃ rest', mergeBranchesRecv rest bs2 = some rest' ∧ bs = (lbl, vt1, t1) :: rest') ∨
      ∃ t2 t rest',
        lookupBranch lbl bs2 = some t2 ∧
        merge t1 t2 = some t ∧
        mergeBranchesRecv rest bs2 = some rest' ∧
        bs = (lbl, vt1, t) :: rest' := by
  classical
  cases hlookupEq : lookupBranchEq lbl bs2 with
  | none =>
      cases hrest : mergeBranchesRecv rest bs2 with
      | none =>
          simp [mergeBranchesRecv, hlookupEq, hrest] at h
      | some rest' =>
          simp [mergeBranchesRecv, hlookupEq, hrest] at h
          left
          refine ⟨?_, rest', ?_, ?_⟩
          · exact lookupBranchEq_none (lbl := lbl) bs2 hlookupEq
          · rfl
          · cases h; rfl
  | some ht =>
      rcases ht with ⟨t2, hlookup⟩
      cases hmerge : merge t1 t2 with
      | none =>
          simp [mergeBranchesRecv, hlookupEq, hmerge] at h
      | some t =>
          cases hrest : mergeBranchesRecv rest bs2 with
          | none =>
              simp [mergeBranchesRecv, hlookupEq, hmerge, hrest] at h
          | some rest' =>
              simp [mergeBranchesRecv, hlookupEq, hmerge, hrest] at h
              right
              refine ⟨t2, t, rest', ?_, ?_, ?_, ?_⟩
              · simp [hlookup]
              · simp [hmerge]
              · rfl
              · cases h; rfl
/-- Merge a list of local types (right fold). -/
def mergeAll : List LocalTypeR → Option LocalTypeR
  | [] => none
  | [a] => some a
  | a :: rest =>
      match mergeAll rest with
      | none => none
      | some u => merge a u
/-- Erasure witness for a list (right fold). -/
def ErasesAll (ts : List LocalTypeR) (t : LocalTypeR) : Prop :=
  match ts with
  | [] => False
  | [a] => t = a
  | a :: rest => ∃ u, ErasesAll rest u ∧ Erases a u t


end
end Choreography.Projection.Erasure
