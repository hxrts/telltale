import Protocol.Coherence.ConfigEquivRenaming.Algebra
/-! # Protocol.Coherence.ConfigEquivRenaming.InverseMaps
Inverse-cancellation lemmas for renaming under session-id isomorphisms.
-/

/-
The Problem. Configuration-equivalence proofs need a reusable cancellation layer
showing inverse-after-forward renaming returns original values, local types, and
branch lists.

Solution Structure.
1. Prove inverse-cancellation for values and local/branch type structures.
2. Lift cancellation to list maps used by environment/trace-style arguments.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section

private theorem sizeOf_lt_branch_head_expanded
    (l : Label) (L : LocalType) (tl : List (Label × LocalType)) :
    sizeOf L < 1 + (1 + sizeOf l + sizeOf L) + sizeOf tl := by
  have hpos : 0 < 1 + (1 + sizeOf l) := by
    simpa [Nat.add_assoc] using (Nat.succ_pos (1 + sizeOf l))
  have h : sizeOf L < (1 + (1 + sizeOf l)) + sizeOf L := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (Nat.lt_add_of_pos_left (k := 1 + (1 + sizeOf l)) (n := sizeOf L) hpos)
  have h' : sizeOf L < ((1 + (1 + sizeOf l)) + sizeOf L) + sizeOf tl :=
    Nat.lt_of_lt_of_le h (Nat.le_add_right _ _)
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h'

/-! ## Inverse-Cancellation Lemmas -/

mutual

/-- Value-type renaming is canceled by the inverse isomorphism. -/
theorem renameValType_left_inv (σ : SessionIso) :
    ∀ T, renameValType (SessionIso.invRenaming σ)
      (renameValType (SessionIso.toRenaming σ) T) = T := by
  -- Structural recursion on value types.
  intro T
  induction T with
  | unit => rfl
  | bool => rfl
  | nat => rfl
  | string => rfl
  | prod T1 T2 ih1 ih2 =>
      simp [renameValType, ih1, ih2]
  | chan sid role =>
      simp [renameValType, SessionIso.toRenaming, SessionIso.invRenaming, σ.left_inv]

-- Inverse-Cancellation on Local/Branch Types

/-- Local-type renaming is canceled by the inverse isomorphism. -/
theorem renameLocalType_left_inv (σ : SessionIso) :
    ∀ L, renameLocalType (SessionIso.invRenaming σ)
      (renameLocalType (SessionIso.toRenaming σ) L) = L := by
  -- Structural recursion on local types.
  intro L
  cases L with
  | send r T L =>
      simp [renameLocalType, renameValType_left_inv, renameLocalType_left_inv (σ:=σ) L]
  | recv r T L =>
      simp [renameLocalType, renameValType_left_inv, renameLocalType_left_inv (σ:=σ) L]
  | select r bs =>
      simp [renameLocalType, renameBranches_left_inv (σ:=σ) bs]
  | branch r bs =>
      simp [renameLocalType, renameBranches_left_inv (σ:=σ) bs]
  | end_ =>
      simp [renameLocalType]
  | var n =>
      simp [renameLocalType]
  | mu L =>
      simp [renameLocalType, renameLocalType_left_inv (σ:=σ) L]
termination_by L => sizeOf L
decreasing_by
  all_goals
    simpa using (sizeOf_lt_branch_head_expanded (l:=_) (L:=_) (tl:=_))

-- Branch-Level Inverse-Cancellation

/-- Branch renaming is canceled by the inverse isomorphism. -/
theorem renameBranches_left_inv (σ : SessionIso) :
    ∀ bs, renameBranches (SessionIso.invRenaming σ)
      (renameBranches (SessionIso.toRenaming σ) bs) = bs := by
  -- Structural recursion on branch lists.
  intro bs
  cases bs with
  | nil =>
      simp [renameBranches]
  | cons hd tl =>
      cases hd with
      | mk l L =>
          simp [renameBranches, renameLocalType_left_inv (σ:=σ) L,
            renameBranches_left_inv (σ:=σ) tl]
termination_by bs => sizeOf bs
decreasing_by
  all_goals
    simpa using (sizeOf_lt_branch_head_expanded (l:=_) (L:=_) (tl:=_))

end

/-! ## Inverse Renaming Maps -/

/-- Mapping value types with inverse-after-forward renaming is identity. -/
theorem map_renameValType_left_inv (σ : SessionIso) (ts : List ValType) :
    ts.map (renameValType (SessionIso.invRenaming σ) ∘
      renameValType (SessionIso.toRenaming σ)) = ts := by
  -- Structural recursion on traces.
  induction ts with
  | nil => simp
  | cons t ts ih =>
      simp [renameValType_left_inv, ih, Function.comp]

end
