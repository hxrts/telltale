import RumpsteakV2.Protocol.Projection.Trans

/-! # RumpsteakV2.Protocol.Projection.Projectb

Boolean checker for V2 projection (`projectb`).

## Expose

The following definitions form the semantic interface for proofs:

- `projectb`
- `CProject`
-/

namespace RumpsteakV2.Protocol.Projection.Projectb

open RumpsteakV2.Protocol.GlobalType
open RumpsteakV2.Protocol.LocalTypeR
open RumpsteakV2.Protocol.Projection.Trans (lcontractive)

private theorem sizeOf_cons {α : Type} [SizeOf α] (x : α) (l : List α) :
    sizeOf (x :: l) = 1 + sizeOf x + sizeOf l := by
  simp [sizeOf, List._sizeOf_1]

private theorem sizeOf_prod {α β : Type} [SizeOf α] [SizeOf β] (a : α) (b : β) :
    sizeOf (a, b) = 1 + sizeOf a + sizeOf b := by
  simp [sizeOf, Prod._sizeOf_1]

private theorem sizeOf_snd_lt_prod {α β : Type} [SizeOf α] [SizeOf β] (a : α) (b : β) :
    sizeOf b < sizeOf (a, b) := by
  have hk : 0 < 1 + sizeOf a := by
    simpa [Nat.one_add] using (Nat.succ_pos (sizeOf a))
  have h : sizeOf b < (1 + sizeOf a) + sizeOf b :=
    Nat.lt_add_of_pos_left (n := sizeOf b) (k := 1 + sizeOf a) hk
  simpa [sizeOf_prod] using h

private theorem sizeOf_head_lt_cons {α : Type} [SizeOf α] (x : α) (l : List α) :
    sizeOf x < sizeOf (x :: l) := by
  have h1 : sizeOf x < 1 + sizeOf x := by
    simpa [Nat.one_add] using (Nat.lt_succ_self (sizeOf x))
  have h2 : 1 + sizeOf x ≤ 1 + sizeOf x + sizeOf l := Nat.le_add_right _ _
  have h : sizeOf x < 1 + sizeOf x + sizeOf l := Nat.lt_of_lt_of_le h1 h2
  simpa [sizeOf_cons] using h

private theorem sizeOf_tail_lt_cons {α : Type} [SizeOf α] (x : α) (l : List α) :
    sizeOf l < sizeOf (x :: l) := by
  have hk : 0 < 1 + sizeOf x := by
    simpa [Nat.one_add] using (Nat.succ_pos (sizeOf x))
  have h : sizeOf l < (1 + sizeOf x) + sizeOf l :=
    Nat.lt_add_of_pos_left (n := sizeOf l) (k := 1 + sizeOf x) hk
  simpa [sizeOf_cons] using h

private theorem sizeOf_head_snd_lt_cons (pair : Label × GlobalType) (rest : List (Label × GlobalType)) :
    sizeOf pair.2 < sizeOf (pair :: rest) := by
  have h1 : sizeOf pair.2 < sizeOf pair := sizeOf_snd_lt_prod pair.1 pair.2
  have h2 : sizeOf pair < sizeOf (pair :: rest) := sizeOf_head_lt_cons pair rest
  exact Nat.lt_trans h1 h2

private theorem sizeOf_body_lt_mu (t : String) (body : GlobalType) :
    sizeOf body < sizeOf (GlobalType.mu t body) := by
  have hk : 0 < 1 + sizeOf t := by
    simpa [Nat.one_add] using (Nat.succ_pos (sizeOf t))
  have h : sizeOf body < (1 + sizeOf t) + sizeOf body :=
    Nat.lt_add_of_pos_left (n := sizeOf body) (k := 1 + sizeOf t) hk
  simpa [GlobalType.mu.sizeOf_spec, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

mutual
  /-- Boolean projection checker (`projectb`). -/
  def projectb : GlobalType → String → LocalTypeR → Bool
    | .end, _, cand =>
        match cand with
        | .end => true
        | _ => false
    | .var t, _, cand =>
        match cand with
        | .var t' => t == t'
        | _ => false
    | .mu t body, role, cand =>
        match cand with
        | .mu t' candBody =>
            if t == t' then
              if lcontractive body then
                projectb body role candBody
              else
                false
            else
              false
        | _ => false
    | .comm sender receiver branches, role, cand =>
        if role == sender then
          match cand with
          | .send partner cands =>
              if partner == receiver then
                projectbBranches branches role cands
              else
                false
          | _ => false
        else if role == receiver then
          match cand with
          | .recv partner cands =>
              if partner == sender then
                projectbBranches branches role cands
              else
                false
          | _ => false
        else
          projectbAllBranches branches role cand

  /-- Check branch-wise projection for participant roles. -/
  def projectbBranches :
      List (Label × GlobalType) → String → List (Label × LocalTypeR) → Bool
    | [], _, [] => true
    | (label, cont) :: rest, role, (label', cand) :: rest' =>
        if label == label' then
          projectb cont role cand && projectbBranches rest role rest'
        else
          false
    | _, _, _ => false

  /-- Check a single candidate against all branches for non-participants. -/
  def projectbAllBranches :
      List (Label × GlobalType) → String → LocalTypeR → Bool
    | [], _, _ => true
    | (_, cont) :: rest, role, cand =>
        projectb cont role cand && projectbAllBranches rest role cand
end
termination_by
  projectb g _ _ => sizeOf g
  projectbBranches bs _ _ => sizeOf bs
  projectbAllBranches bs _ _ => sizeOf bs
decreasing_by
  simp [sizeOf_body_lt_mu, sizeOf_head_snd_lt_cons, sizeOf_tail_lt_cons]

/-- Placeholder definition: EQ via `projectb`.
    This will be replaced by the coinductive gfp-based relation in Phase A. -/
def CProject (g : GlobalType) (role : String) (cand : LocalTypeR) : Prop :=
  projectb g role cand = true

end RumpsteakV2.Protocol.Projection.Projectb
