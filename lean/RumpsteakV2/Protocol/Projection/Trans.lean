import RumpsteakV2.Protocol.GlobalType
import RumpsteakV2.Protocol.LocalTypeR

/-! # RumpsteakV2.Protocol.Projection.Trans

Candidate projection for V2 (Coq-style `trans`).

## Expose

The following definitions form the semantic interface for proofs:

- `trans`: candidate projection function
- `transBranches`: helper for projecting branch lists
- `lcontractive`: guardedness predicate for recursion
- `trans_freeVars_subset`: free variables are preserved
- `transBranches_freeVars_subset`: branch-wise free variable preservation
- `trans_comm_sender`: shape lemma for sender projection
- `trans_comm_receiver`: shape lemma for receiver projection
- `trans_comm_other`: shape lemma for non-participant projection
-/

namespace RumpsteakV2.Protocol.Projection.Trans

open RumpsteakV2.Protocol.GlobalType
open RumpsteakV2.Protocol.LocalTypeR

/-- Check if a global type is locally contractive (guarded recursion).
    A type is contractive if:
    - `end`, `var`, and `comm` are always contractive
    - `mu t body` is contractive iff body starts with a `comm` (not `var` or another `mu`)

    This ensures that unfolding recursion makes progress (necessary for coinductive projection). -/
def lcontractive : GlobalType → Bool
  | .end => true
  | .var _ => true
  | .comm _ _ _ => true
  | .mu _ body =>
      match body with
      | .var _ => false    -- Immediately recursive without guard
      | .mu _ _ => false   -- Nested mu without guard
      | .comm _ _ _ => true
      | .end => true       -- Degenerate but contractive

private theorem sizeOf_cons {α : Type} [SizeOf α] (x : α) (l : List α) :
    sizeOf (x :: l) = 1 + sizeOf x + sizeOf l := by
  simp [sizeOf, List._sizeOf_1]

private theorem sizeOf_prod {α β : Type} [SizeOf α] [SizeOf β] (a : α) (b : β) :
    sizeOf (a, b) = 1 + sizeOf a + sizeOf b := by
  simp [sizeOf, Prod._sizeOf_1]

private theorem sizeOf_snd_lt_prod {α β : Type} [SizeOf α] [SizeOf β] (a : α) (b : β) :
    sizeOf b < sizeOf (a, b) := by
  simp only [sizeOf, Prod._sizeOf_1]
  omega

private theorem sizeOf_head_lt_cons {α : Type} [SizeOf α] (x : α) (l : List α) :
    sizeOf x < sizeOf (x :: l) := by
  simp only [sizeOf, List._sizeOf_1]
  omega

private theorem sizeOf_tail_lt_cons {α : Type} [SizeOf α] (x : α) (l : List α) :
    sizeOf l < sizeOf (x :: l) := by
  simp only [sizeOf, List._sizeOf_1]
  omega

private theorem sizeOf_head_snd_lt_cons (pair : Label × GlobalType) (rest : List (Label × GlobalType)) :
    sizeOf pair.2 < sizeOf (pair :: rest) := by
  have h1 : sizeOf pair.2 < sizeOf pair := sizeOf_snd_lt_prod pair.1 pair.2
  have h2 : sizeOf pair < sizeOf (pair :: rest) := sizeOf_head_lt_cons pair rest
  exact Nat.lt_trans h1 h2

private theorem sizeOf_bs_lt_comm (sender receiver : String) (bs : List (Label × GlobalType)) :
    sizeOf bs < sizeOf (GlobalType.comm sender receiver bs) := by
  simp only [GlobalType.comm.sizeOf_spec]
  have h : 0 < 1 + sizeOf sender + sizeOf receiver := by omega
  omega

private theorem sizeOf_head_snd_lt_comm
    (sender receiver : String) (pair : Label × GlobalType) (rest : List (Label × GlobalType)) :
    sizeOf pair.2 < sizeOf (GlobalType.comm sender receiver (pair :: rest)) := by
  have h1 : sizeOf pair.2 < sizeOf (pair :: rest) := sizeOf_head_snd_lt_cons pair rest
  have h2 : sizeOf (pair :: rest) < sizeOf (GlobalType.comm sender receiver (pair :: rest)) :=
    sizeOf_bs_lt_comm sender receiver (pair :: rest)
  exact Nat.lt_trans h1 h2

private theorem sizeOf_cont_lt_comm
    (sender receiver : String) (label : Label) (cont : GlobalType) (rest : List (Label × GlobalType)) :
    sizeOf cont < sizeOf (GlobalType.comm sender receiver ((label, cont) :: rest)) := by
  exact sizeOf_head_snd_lt_comm sender receiver (label, cont) rest

private theorem sizeOf_cont_lt_cons (label : Label) (cont : GlobalType) (rest : List (Label × GlobalType)) :
    sizeOf cont < sizeOf ((label, cont) :: rest) := by
  exact sizeOf_head_snd_lt_cons (label, cont) rest

private theorem sizeOf_body_lt_mu (t : String) (body : GlobalType) :
    sizeOf body < sizeOf (GlobalType.mu t body) := by
  have hk : 0 < 1 + sizeOf t := by
    simp only [Nat.one_add]
    exact Nat.succ_pos (sizeOf t)
  have h : sizeOf body < (1 + sizeOf t) + sizeOf body :=
    Nat.lt_add_of_pos_left (n := sizeOf body) (k := 1 + sizeOf t) hk
  simp only [sizeOf, GlobalType._sizeOf_1]
  omega

mutual
  /-- Coq-style candidate projection (`trans`). -/
  def trans : GlobalType → String → LocalTypeR
    | .end, _ => .end
    | .var t, _ => .var t
    | .mu t body, role =>
        if lcontractive body then
          .mu t (trans body role)
        else
          .end
    | .comm sender receiver branches, role =>
        if role == sender then
          .send receiver (transBranches branches role)
        else if role == receiver then
          .recv sender (transBranches branches role)
        else
          match branches with
          | [] => .end
          | (_, cont) :: _ => trans cont role
  termination_by
    g _ => sizeOf g
  decreasing_by
    all_goals
      first
      | exact sizeOf_body_lt_mu _ _
      | exact sizeOf_bs_lt_comm _ _ _
      | exact sizeOf_cont_lt_comm _ _ _ _ _

  /-- Project branch continuations for `trans`. -/
  def transBranches : List (Label × GlobalType) → String → List (Label × LocalTypeR)
    | [], _ => []
    | (label, cont) :: rest, role =>
        (label, trans cont role) :: transBranches rest role
  termination_by
    branches _ => sizeOf branches
  decreasing_by
    all_goals
      first
      | exact sizeOf_cont_lt_cons _ _ _
      | exact sizeOf_tail_lt_cons _ _
end

/-- Sender shape lemma for `trans` on communications. -/
theorem trans_comm_sender
    (sender receiver role : String) (branches : List (Label × GlobalType))
    (hrole : role = sender) :
    trans (.comm sender receiver branches) role =
      .send receiver (transBranches branches role) := by
  have hsender : (role == sender) = true := by
    simp [hrole]
  cases branches with
  | nil =>
      rw [trans.eq_4]
      simp [hsender]
  | cons head tail =>
      cases head with
      | mk label cont =>
          rw [trans.eq_5]
          simp [hsender]

/-- Receiver shape lemma for `trans` on communications. -/
theorem trans_comm_receiver
    (sender receiver role : String) (branches : List (Label × GlobalType))
    (hrole : role = receiver) (hneq : role ≠ sender) :
    trans (.comm sender receiver branches) role =
      .recv sender (transBranches branches role) := by
  have hsender : (role == sender) = false :=
    beq_eq_false_iff_ne.mpr hneq
  have hreceiver : (role == receiver) = true := by
    simp [hrole]
  cases branches with
  | nil =>
      rw [trans.eq_4]
      simp [hsender, hreceiver]
  | cons head tail =>
      cases head with
      | mk label cont =>
          rw [trans.eq_5]
          simp [hsender, hreceiver]

/-- Non-participant shape lemma for `trans` on communications. -/
theorem trans_comm_other
    (sender receiver role : String) (branches : List (Label × GlobalType))
    (hs : role ≠ sender) (hr : role ≠ receiver) :
    trans (.comm sender receiver branches) role =
      match branches with
      | [] => .end
      | (_, cont) :: _ => trans cont role := by
  have hsender : (role == sender) = false := beq_eq_false_iff_ne.mpr hs
  have hreceiver : (role == receiver) = false := beq_eq_false_iff_ne.mpr hr
  cases branches with
  | nil =>
      rw [trans.eq_4]
      simp [hsender, hreceiver]
  | cons head tail =>
      cases head with
      | mk label cont =>
          rw [trans.eq_5]
          simp [hsender, hreceiver]

mutual
  /-- Free variables of `trans` are contained in global free variables. -/
  theorem trans_freeVars_subset (g : GlobalType) (role : String) :
      (trans g role).freeVars ⊆ g.freeVars := by
    intro x hx
    match g with
    | .end =>
        simp only [trans, LocalTypeR.freeVars, List.mem_nil_iff] at hx
    | .var t =>
        simp only [trans, LocalTypeR.freeVars, GlobalType.freeVars] at hx ⊢
        exact hx
    | .mu t body =>
        cases hcontract : lcontractive body with
        | true =>
            simp only [trans, hcontract, ↓reduceIte, LocalTypeR.freeVars, List.mem_filter,
              bne_iff_ne, ne_eq] at hx
            have hmem : x ∈ body.freeVars := trans_freeVars_subset body role hx.1
            simp only [GlobalType.freeVars, List.mem_filter, bne_iff_ne, ne_eq]
            exact ⟨hmem, hx.2⟩
        | false =>
            simp only [trans, hcontract] at hx
            contradiction
    | .comm sender receiver branches =>
        cases hsender : role == sender with
        | true =>
            match branches with
            | [] =>
                unfold trans at hx
                simp only [hsender, ↓reduceIte, transBranches, LocalTypeR.freeVars,
                  LocalTypeR.freeVarsOfBranches_eq_flatMap, List.flatMap_nil, List.mem_nil_iff] at hx
            | (label, cont) :: tail =>
                simp only [trans, hsender, ↓reduceIte, LocalTypeR.freeVars,
                  LocalTypeR.freeVarsOfBranches_eq_flatMap] at hx
                have hsub := transBranches_freeVars_subset ((label, cont) :: tail) role
                have hmem := hsub hx
                simp only [GlobalType.freeVars, GlobalType.freeVarsOfBranches_eq_flatMap]
                exact hmem
        | false =>
            cases hreceiver : role == receiver with
            | true =>
                match branches with
                | [] =>
                    unfold trans at hx
                    simp only [hsender, Bool.false_eq_true, ↓reduceIte, hreceiver, transBranches,
                      LocalTypeR.freeVars, LocalTypeR.freeVarsOfBranches_eq_flatMap,
                      List.flatMap_nil, List.mem_nil_iff] at hx
                | (label, cont) :: tail =>
                    simp only [trans, hsender, Bool.false_eq_true, ↓reduceIte, hreceiver,
                      LocalTypeR.freeVars, LocalTypeR.freeVarsOfBranches_eq_flatMap] at hx
                    have hsub := transBranches_freeVars_subset ((label, cont) :: tail) role
                    have hmem := hsub hx
                    simp only [GlobalType.freeVars, GlobalType.freeVarsOfBranches_eq_flatMap]
                    exact hmem
            | false =>
                match branches with
                | [] =>
                    simp only [trans, hsender, Bool.false_eq_true, ↓reduceIte, hreceiver,
                      LocalTypeR.freeVars, List.mem_nil_iff] at hx
                | (label, cont) :: tail =>
                    simp only [trans, hsender, Bool.false_eq_true, ↓reduceIte, hreceiver] at hx
                    have hmem' : x ∈ cont.freeVars := trans_freeVars_subset cont role hx
                    simp only [GlobalType.freeVars, GlobalType.freeVarsOfBranches_eq_flatMap,
                      List.flatMap_cons, List.mem_append]
                    left
                    exact hmem'
  termination_by sizeOf g
  decreasing_by
    all_goals
      first
      | exact sizeOf_body_lt_mu _ _
      | exact sizeOf_bs_lt_comm _ _ _
      | exact sizeOf_cont_lt_comm _ _ _ _ _

  /-- Branch-wise free variable inclusion for `transBranches`. -/
  theorem transBranches_freeVars_subset (branches : List (Label × GlobalType)) (role : String) :
      (transBranches branches role).flatMap (fun (_, t) => t.freeVars) ⊆
        branches.flatMap (fun (_, g) => g.freeVars) := by
    intro y hy
    match branches with
    | [] =>
        simp only [transBranches, List.flatMap_nil, List.mem_nil_iff] at hy
    | (label, cont) :: tail =>
        simp only [transBranches, List.flatMap_cons, List.mem_append] at hy
        cases hy with
        | inl hhead =>
            have hmem : y ∈ cont.freeVars := trans_freeVars_subset cont role hhead
            simp only [List.flatMap_cons, List.mem_append]
            left
            exact hmem
        | inr htail =>
            have hmem : y ∈ tail.flatMap (fun (_, g) => g.freeVars) :=
              transBranches_freeVars_subset tail role htail
            simp only [List.flatMap_cons, List.mem_append]
            right
            exact hmem
  termination_by sizeOf branches
  decreasing_by
    all_goals
      first
      | exact sizeOf_cont_lt_cons _ _ _
      | exact sizeOf_tail_lt_cons _ _
end

/-! ## Closedness Preservation (Coq-style)

These theorems establish that projection preserves closedness,
which is the key insight from the Coq subject_reduction implementation.
In Coq, this follows automatically from de Bruijn indices;
here we prove it explicitly from `trans_freeVars_subset`. -/

/-- If a global type is closed, then its projection is also closed.
    This is the Coq-style theorem that sidesteps the allVarsBound semantic gap. -/
theorem trans_closed_of_closed (g : GlobalType) (role : String)
    (h : g.freeVars = []) : (trans g role).freeVars = [] := by
  have hsub := trans_freeVars_subset g role
  rw [h] at hsub
  -- hsub : (trans g role).freeVars ⊆ []
  -- A subset of [] must be []
  exact List.subset_nil.mp hsub

/-- Corollary using the isClosed predicate. -/
theorem trans_isClosed_of_isClosed (g : GlobalType) (role : String)
    (h : g.isClosed = true) : (trans g role).isClosed = true := by
  simp only [LocalTypeR.isClosed, List.isEmpty_iff]
  simp only [GlobalType.isClosed, List.isEmpty_iff] at h
  exact trans_closed_of_closed g role h

/-- The result of trans on a closed global type has no free vars matching
    any specific variable name. This is useful for the mu case. -/
theorem trans_freeVars_empty_of_closed (g : GlobalType) (role : String) (t : String)
    (h : g.freeVars = []) : t ∉ (trans g role).freeVars := by
  have hclosed := trans_closed_of_closed g role h
  simp only [hclosed, List.mem_nil_iff, not_false_eq_true]

end RumpsteakV2.Protocol.Projection.Trans
