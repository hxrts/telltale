import SessionTypes.GlobalType
import SessionTypes.LocalTypeR
import SessionTypes.Participation


/-
The Problem. Define a candidate projection function `trans : GlobalType → String → LocalTypeR`
that extracts a role's local view from a global choreography. The key challenge is handling
recursive types (μt.body): we must project the body and then decide whether to keep the
recursion or collapse it to end based on guardedness.

The Coq approach checks guardedness of the PROJECTED type (trans body role), not the global
type body. This creates a termination challenge: to check guardedness of the projection,
we must first compute it, but computing it requires checking guardedness. The solution is
to use Lean's well-founded recursion on the structural size of the global type, which
ensures termination independent of guardedness checks.

Additional challenges arise from branch processing in communications:
1. Sender/receiver get explicit send/recv with projected branches
2. Non-participants get the projection of the first branch continuation
3. Free variables must be preserved through projection
4. Well-formedness properties must be maintained

Solution Structure. The module is organized into five main sections:
1. Core definitions: trans, transBranches, lcontractive, and termination proofs
2. Shape lemmas: trans_comm_sender, trans_comm_receiver, trans_comm_other
3. Closedness preservation: trans_freeVars_subset and derived theorems
4. Well-formedness: preservation of structure through projection
5. Participation: relating contractiveness to participation properties
-/

/-! # Choreography.Projection.Trans

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

namespace Choreography.Projection.Trans

open SessionTypes.GlobalType
open SessionTypes.LocalTypeR

/-! ## Contractiveness Predicate -/

/-- Check if a global type is locally contractive (guarded recursion).
    A type is contractive if:
    - `end`, `var`, `comm`, and `delegate` are always contractive
    - `mu t body` is contractive iff body starts with a `comm` or `delegate` (not `var` or another `mu`)

    This ensures that unfolding recursion makes progress (necessary for coinductive projection). -/
def lcontractive : GlobalType → Bool
  | .end => true
  | .var _ => true
  | .comm _ _ _ => true
  | .delegate _ _ _ _ _ => true
  | .mu _ body =>
      match body with
      | .var _ => false         -- Immediately recursive without guard
      | .mu _ _ => false        -- Nested mu without guard
      | .comm _ _ _ => true
      | .delegate _ _ _ _ _ => true
      | .end => true            -- Degenerate but contractive

/-! ## Size-Of Lemmas for Termination -/

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

private theorem sizeOf_cont_lt_comm_expanded (sender receiver : String)
    (label : Label) (cont : GlobalType) (tail : List (Label × GlobalType)) :
    sizeOf cont <
      1 + sizeOf sender + sizeOf receiver + (1 + (1 + sizeOf label + sizeOf cont) + sizeOf tail) := by
  simp [sizeOf, List._sizeOf_1, Prod._sizeOf_1]
  omega

private theorem sizeOf_branches_lt_comm_expanded (sender receiver : String)
    (label : Label) (cont : GlobalType) (tail : List (Label × GlobalType)) :
    sizeOf ((label, cont) :: tail) <
      1 + sizeOf sender + sizeOf receiver + (1 + (1 + sizeOf label + sizeOf cont) + sizeOf tail) := by
  simp [sizeOf, List._sizeOf_1, Prod._sizeOf_1]
  omega

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

/-! ## Core Projection Functions -/

mutual
  /-- Coq-style candidate projection (`trans`).
      Matches Coq: `GRec g0 => let e := trans p g0 in if eguarded 0 e then ERec e else EEnd`
      The key insight is to check guardedness of the PROJECTED type, not the global type. -/
  def trans : GlobalType → String → LocalTypeR
    | .end, _ => .end
    | .var t, _ => .var t
    | .mu t body, role =>
        let e := trans body role
        if e.isGuarded t then
          .mu t e
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
    | .delegate p q sid r cont, role =>
        -- Delegation: p sends channel (sid, r) to q
        -- - delegator p: sends the channel endpoint
        -- - delegatee q: receives the channel endpoint
        -- - others: not involved in this delegation step
        if role == p then
          -- Delegator sends channel type to delegatee
          .send q [(⟨"_delegate", .unit⟩, some (.chan sid r), trans cont role)]
        else if role == q then
          -- Delegatee receives channel type from delegator
          .recv p [(⟨"_delegate", .unit⟩, some (.chan sid r), trans cont role)]
        else
          -- Other roles just continue
          trans cont role
  termination_by
    g _ => sizeOf g
  decreasing_by
    all_goals
      first
      | exact sizeOf_body_lt_mu _ _
      | exact sizeOf_bs_lt_comm _ _ _
      | exact sizeOf_cont_lt_comm _ _ _ _ _
      | simp only [sizeOf, GlobalType._sizeOf_1]; omega

  /-- Project branch continuations for `trans`. -/
  def transBranches : List (Label × GlobalType) → String → List BranchR
    | [], _ => []
    | (label, cont) :: rest, role =>
        (label, none, trans cont role) :: transBranches rest role
  termination_by
    branches _ => sizeOf branches
  decreasing_by
    all_goals
      first
      | exact sizeOf_cont_lt_cons _ _ _
      | exact sizeOf_tail_lt_cons _ _
end

/-! ## Shape Lemmas for Communications -/

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

/-! ## Free Variables Preservation -/

mutual
  /-- Free variables of `trans` are contained in global free variables. -/
  theorem trans_freeVars_subset (role : String) :
      ∀ g x, x ∈ (trans g role).freeVars → x ∈ g.freeVars := by
    intro g x hx
    match g with
    | .end =>
        have : False := by
          simp [trans, LocalTypeR.freeVars] at hx
        exact this.elim
    | .var t =>
        simp only [trans, LocalTypeR.freeVars, GlobalType.freeVars] at hx ⊢
        exact hx
    | .mu t body =>
        simp only [trans] at hx
        by_cases hguard : (trans body role).isGuarded t  -- mu guard split
        ·
          simp only [hguard, ↓reduceIte, LocalTypeR.freeVars, List.mem_filter,
            bne_iff_ne, ne_eq] at hx
          have hmem : x ∈ body.freeVars := trans_freeVars_subset role body x hx.1
          simp only [GlobalType.freeVars, List.mem_filter, bne_iff_ne, ne_eq]
          exact ⟨hmem, hx.2⟩
        ·
          have : False := by
            simp [hguard, Bool.false_eq_true, ↓reduceIte, LocalTypeR.freeVars] at hx
          exact this.elim
    | .comm sender receiver branches =>
        cases hsender : role == sender with
        | true =>
            cases branches with
            | nil =>
                have : False := by
                  unfold trans at hx
                  simp [hsender, ↓reduceIte, transBranches, LocalTypeR.freeVars,
                    SessionTypes.LocalTypeR.freeVarsOfBranches_eq_flatMap, List.flatMap_nil] at hx
                exact this.elim
            | cons head tail =>
                cases head with
                | mk label cont =>
                    simp only [trans, hsender, ↓reduceIte, LocalTypeR.freeVars,
                      SessionTypes.LocalTypeR.freeVarsOfBranches_eq_flatMap] at hx
                    have hmem := transBranches_freeVars_subset role ((label, cont) :: tail) x hx
                    simpa [GlobalType.freeVars, SessionTypes.GlobalType.freeVarsOfBranches_eq_flatMap] using hmem
        | false =>
            cases hreceiver : role == receiver with
            | true =>
                cases branches with
                | nil =>
                    have : False := by
                      unfold trans at hx
                      simp [hsender, Bool.false_eq_true, ↓reduceIte, hreceiver, transBranches,
                        LocalTypeR.freeVars, SessionTypes.LocalTypeR.freeVarsOfBranches_eq_flatMap,
                        List.flatMap_nil] at hx
                    exact this.elim
                | cons head tail =>
                    cases head with
                    | mk label cont =>
                        simp only [trans, hsender, Bool.false_eq_true, ↓reduceIte, hreceiver,
                          LocalTypeR.freeVars, SessionTypes.LocalTypeR.freeVarsOfBranches_eq_flatMap] at hx
                        have hmem := transBranches_freeVars_subset role ((label, cont) :: tail) x hx
                        simpa [GlobalType.freeVars, SessionTypes.GlobalType.freeVarsOfBranches_eq_flatMap] using hmem
            | false =>
                cases branches with
                | nil =>
                    have : False := by
                      simp [trans, hsender, Bool.false_eq_true, ↓reduceIte, hreceiver,
                        LocalTypeR.freeVars] at hx
                    exact this.elim
                | cons head tail =>
                    cases head with
                    | mk label cont =>
                        simp only [trans, hsender, Bool.false_eq_true, ↓reduceIte, hreceiver] at hx
                        have hmem' : x ∈ cont.freeVars := trans_freeVars_subset role cont x hx
                        simp [GlobalType.freeVars, SessionTypes.GlobalType.freeVarsOfBranches_eq_flatMap,
                          List.flatMap_cons, List.mem_append, hmem']
    | .delegate p q sid r cont =>
        -- Delegate projects to continuation's freeVars
        simp only [trans] at hx
        by_cases hp : role == p
        · simp only [hp, ↓reduceIte, LocalTypeR.freeVars,
            SessionTypes.LocalTypeR.freeVarsOfBranches_eq_flatMap, List.flatMap,
            List.append_nil, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil] at hx
          have hmem : x ∈ cont.freeVars := trans_freeVars_subset role cont x hx
          simp [GlobalType.freeVars, hmem]
        · by_cases hq : role == q
          · simp only [hp, Bool.false_eq_true, ↓reduceIte, hq, LocalTypeR.freeVars,
              SessionTypes.LocalTypeR.freeVarsOfBranches_eq_flatMap, List.flatMap,
              List.append_nil, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil] at hx
            have hmem : x ∈ cont.freeVars := trans_freeVars_subset role cont x hx
            simp [GlobalType.freeVars, hmem]
          · simp only [hp, Bool.false_eq_true, ↓reduceIte, hq] at hx
            have hmem : x ∈ cont.freeVars := trans_freeVars_subset role cont x hx
            simp [GlobalType.freeVars, hmem]

  termination_by g _ _ => sizeOf g
  decreasing_by
    all_goals
      simp_wf
      try (simp [*])
      first
      | exact sizeOf_body_lt_mu _ _
      | exact sizeOf_branches_lt_comm_expanded _ _ _ _ _
      | exact sizeOf_cont_lt_comm_expanded _ _ _ _ _
      | exact sizeOf_bs_lt_comm _ _ _
      | exact sizeOf_cont_lt_comm _ _ _ _ _
      | omega

  /-- Branch-wise free variable inclusion for `transBranches`. -/
  theorem transBranches_freeVars_subset (role : String) :
      ∀ branches y,
        y ∈ (transBranches branches role).flatMap (fun (_, _, t) => t.freeVars) →
          y ∈ branches.flatMap (fun (_, g) => g.freeVars) := by
    intro branches y hy
    match branches with
    | [] =>
        simp [transBranches, List.flatMap_nil] at hy
    | (label, cont) :: tail =>
        simp only [transBranches, List.flatMap_cons, List.mem_append] at hy
        cases hy with
        | inl hhead =>
            have hmem : y ∈ cont.freeVars := trans_freeVars_subset role cont y hhead
            simp [List.flatMap_cons, List.mem_append, hmem]
        | inr htail =>
            have hmem : y ∈ tail.flatMap (fun (_, g) => g.freeVars) :=
              transBranches_freeVars_subset role tail y htail
            simp [List.flatMap_cons, List.mem_append, hmem]
  termination_by branches _ _ => sizeOf branches
  decreasing_by
    all_goals
      simp_wf
      first
      | exact sizeOf_cont_lt_cons _ _ _
      | exact sizeOf_tail_lt_cons _ _
      | omega
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
  have hsub := trans_freeVars_subset role g
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

/-! ## LocalTypeR.WellFormed Preservation

Projection preserves well-formedness under all-branch participation. -/

open SessionTypes.Participation

/-- Helper: .send and .recv types are guarded for any variable. -/
private theorem isGuarded_send (p : String) (bs : List BranchR) (v : String) :
    (LocalTypeR.send p bs).isGuarded v = true := by
  simp [LocalTypeR.isGuarded]

private theorem isGuarded_recv (p : String) (bs : List BranchR) (v : String) :
    (LocalTypeR.recv p bs).isGuarded v = true := by
  simp [LocalTypeR.isGuarded]

/-- Helper: .end is guarded for any variable. -/
private theorem isGuarded_end (v : String) : LocalTypeR.end.isGuarded v = true := by
  simp [LocalTypeR.isGuarded]

end Choreography.Projection.Trans
