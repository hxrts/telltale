import RumpsteakV2.Protocol.GlobalType
import RumpsteakV2.Protocol.LocalTypeR
import RumpsteakV2.Protocol.Participation

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
        -- New definition: trans (.mu t body) role = if (trans body role).isGuarded t then .mu t (trans body role) else .end
        simp only [trans] at hx
        by_cases hguard : (trans body role).isGuarded t
        · -- Guarded case: result is .mu t (trans body role)
          simp only [hguard, ↓reduceIte, LocalTypeR.freeVars, List.mem_filter,
            bne_iff_ne, ne_eq] at hx
          have hmem : x ∈ body.freeVars := trans_freeVars_subset body role hx.1
          simp only [GlobalType.freeVars, List.mem_filter, bne_iff_ne, ne_eq]
          exact ⟨hmem, hx.2⟩
        · -- Not guarded case: result is .end, so freeVars is empty
          simp only [hguard, Bool.false_eq_true, ↓reduceIte, LocalTypeR.freeVars,
            List.mem_nil_iff] at hx
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

/-! ## WellFormed Preservation

These theorems establish that projection preserves well-formedness properties.

**Important**: The theorem `trans_isContractive_of_lcontractive` is FALSE for
non-participants. Counterexample:
- `g = .mu "x" (.comm "A" "B" [(.mk "m" .unit, .var "x")])`
- `role = "C"` (not A or B)
- `lcontractive g = true` (body is .comm)
- `g.isClosed = true` (var x is bound by mu x)
- `trans g role = .mu "x" (.var "x")` (following non-participant path)
- `isContractive (.mu "x" (.var "x")) = false` (var x is NOT guarded by x)

For participants, the theorem DOES hold because:
- Participants project to .send or .recv which guard any variable
- The recursive structure preserves contractiveness

The provable version uses `participatesAllBranches` which requires participation in ALL
branch continuations for direct participants:
- `trans_isContractive_of_participatesAllBranches` - fully proven
- `trans_preserves_WellFormed_allBranches` - full WellFormed for all-branch participants
-/

open RumpsteakV2.Protocol.Participation

/-- Helper: .send and .recv types are guarded for any variable. -/
private theorem isGuarded_send (p : String) (bs : List (Label × LocalTypeR)) (v : String) :
    (LocalTypeR.send p bs).isGuarded v = true := by
  simp [LocalTypeR.isGuarded]

private theorem isGuarded_recv (p : String) (bs : List (Label × LocalTypeR)) (v : String) :
    (LocalTypeR.recv p bs).isGuarded v = true := by
  simp [LocalTypeR.isGuarded]

/-- Helper: .end is guarded for any variable. -/
private theorem isGuarded_end (v : String) : LocalTypeR.end.isGuarded v = true := by
  simp [LocalTypeR.isGuarded]

/-! ## First-Branch Participation

The theorem `trans_isContractive_of_participant` with existential `participates` is FALSE.
Counterexample: role participates in branch 2, but `trans` follows branch 1 where they
don't participate, producing `.mu "x" (.var "x")` which is not contractive.

The correct approach is to use a predicate that tracks the same path as `trans`:
`participatesFirstBranch` follows the first branch for non-direct participants,
matching exactly what `trans` does. -/

mutual
  /-- Participation check following the same path as `trans`.
      For non-direct participants, follows the first branch like `trans` does. -/
  def participatesFirstBranch (role : String) : GlobalType → Bool
    | .end => false
    | .var _ => false
    | .mu _ body => participatesFirstBranch role body
    | .comm sender receiver branches =>
        is_participant role sender receiver ||
        match branches with
        | [] => false
        | (_, cont) :: _ => participatesFirstBranch role cont

  /-- Branches version for mutual recursion (unused but needed for termination). -/
  def participatesFirstBranchBranches (role : String) : List (Label × GlobalType) → Bool
    | [] => false
    | (_, cont) :: _ => participatesFirstBranch role cont
end

/-- First-branch participation implies general participation. -/
theorem participatesFirstBranch_imp_participates (g : GlobalType) (role : String) :
    participatesFirstBranch role g = true → participates role g = true := by
  intro h
  match g with
  | .end =>
      -- participatesFirstBranch role .end = false, so h : false = true is contradiction
      unfold participatesFirstBranch at h
      contradiction
  | .var _ =>
      unfold participatesFirstBranch at h
      contradiction
  | .mu _ body =>
      unfold participatesFirstBranch at h
      unfold participates
      exact participatesFirstBranch_imp_participates body role h
  | .comm sender receiver branches =>
      unfold participatesFirstBranch at h
      unfold participates
      cases hpart : is_participant role sender receiver with
      | true =>
          simp
      | false =>
          simp only [hpart, Bool.false_or] at h ⊢
          match hbranches : branches with
          | [] =>
              simp at h
          | (label, cont) :: rest =>
              simp only [participatesBranches, Bool.or_eq_true]
              left
              exact participatesFirstBranch_imp_participates cont role h
termination_by sizeOf g
decreasing_by
  all_goals first
    | exact sizeOf_body_lt_mu _ _
    | (subst hbranches; exact sizeOf_cont_lt_comm _ _ _ _ _)

mutual
  /-- Participation that continues through ALL branch continuations, not just first branch.
      This is needed for contractiveness: when role is sender/receiver, we need
      participation to continue in ALL continuations, not just the outer level. -/
  def participatesAllBranches (role : String) : GlobalType → Bool
    | .end => false
    | .var _ => false
    | .mu _ body => participatesAllBranches role body
    | .comm sender receiver branches =>
        is_participant role sender receiver &&
        participatesAllBranchesList role branches ||
        -- OR: not direct participant but participates in first branch
        (!(is_participant role sender receiver) &&
         match branches with
         | [] => false
         | (_, cont) :: _ => participatesAllBranches role cont)

  /-- Helper for branch list participation. -/
  def participatesAllBranchesList (role : String) : List (Label × GlobalType) → Bool
    | [] => true
    | (_, cont) :: rest =>
        participatesAllBranches role cont && participatesAllBranchesList role rest
end

/-- Helper: trans result is guarded when role participates via first-branch path.

    The key insight: participation means we eventually reach a .send/.recv which
    guards any variable. The guardedness propagates up through the structure.

    Note: This does NOT require closedness - participation alone is sufficient. -/
theorem trans_isGuarded_of_participatesFirstBranch
    (g : GlobalType) (v : String) (role : String)
    (hpart : participatesFirstBranch role g = true) :
    (trans g role).isGuarded v = true := by
  match g with
  | .end =>
      unfold participatesFirstBranch at hpart
      contradiction
  | .var _ =>
      unfold participatesFirstBranch at hpart
      contradiction
  | .mu t body =>
      unfold participatesFirstBranch at hpart
      -- New definition: trans (.mu t body) = if (trans body).isGuarded t then .mu t (trans body) else .end
      simp only [trans]
      by_cases hguard : (trans body role).isGuarded t
      · -- Guarded case: result is .mu t (trans body role)
        simp only [hguard, ↓reduceIte, LocalTypeR.isGuarded]
        by_cases hvt : v = t
        · simp [hvt]
        · have hvne : (v == t) = false := beq_eq_false_iff_ne.mpr hvt
          simp only [hvne, Bool.false_eq_true, ↓reduceIte]
          exact trans_isGuarded_of_participatesFirstBranch body v role hpart
      · -- Not guarded case: result is .end, which is always guarded
        simp only [hguard, Bool.false_eq_true, ↓reduceIte, LocalTypeR.isGuarded]
  | .comm sender receiver branches =>
      unfold participatesFirstBranch at hpart
      cases hpart_direct : is_participant role sender receiver with
      | true =>
          -- Role is direct participant (sender or receiver)
          unfold is_participant at hpart_direct
          cases hrole_s : role == sender with
          | true =>
              have heq : role = sender := beq_iff_eq.mp hrole_s
              rw [trans_comm_sender sender receiver role branches heq]
              exact isGuarded_send receiver (transBranches branches role) v
          | false =>
              simp only [hrole_s, Bool.false_or] at hpart_direct
              have heq : role = receiver := beq_iff_eq.mp hpart_direct
              have hne : role ≠ sender := by
                intro heq'
                rw [heq'] at hrole_s
                simp at hrole_s
              rw [trans_comm_receiver sender receiver role branches heq hne]
              exact isGuarded_recv sender (transBranches branches role) v
      | false =>
          -- Role is not direct participant, follows first branch
          simp only [hpart_direct, Bool.false_or] at hpart
          unfold is_participant at hpart_direct
          have hne_s : role ≠ sender := by
            intro heq
            rw [heq] at hpart_direct
            simp at hpart_direct
          have hne_r : role ≠ receiver := by
            intro heq
            rw [heq] at hpart_direct
            simp at hpart_direct
          rw [trans_comm_other sender receiver role branches hne_s hne_r]
          match hbranches : branches with
          | [] =>
              simp [LocalTypeR.isGuarded]
          | (label, cont) :: rest =>
              exact trans_isGuarded_of_participatesFirstBranch cont v role hpart
termination_by sizeOf g
decreasing_by
  all_goals first
    | exact sizeOf_body_lt_mu _ _
    | (subst hbranches; exact sizeOf_cont_lt_comm _ _ _ _ _)

/-! ## Fully Proven Contractiveness with All-Branch Participation

The `participatesAllBranches` predicate is stronger than `participatesFirstBranch`:
- For direct participants, it requires participation in ALL branch continuations
- This ensures that `transBranches` produces contractive results
- The theorem `trans_isContractive_of_participatesAllBranches` is fully provable (no sorry)
-/

/-- participatesAllBranches implies participatesFirstBranch. -/
theorem participatesAllBranches_imp_participatesFirstBranch (g : GlobalType) (role : String) :
    participatesAllBranches role g = true → participatesFirstBranch role g = true := by
  intro h
  match g with
  | .end =>
      unfold participatesAllBranches at h
      contradiction
  | .var _ =>
      unfold participatesAllBranches at h
      contradiction
  | .mu _ body =>
      unfold participatesAllBranches at h
      unfold participatesFirstBranch
      exact participatesAllBranches_imp_participatesFirstBranch body role h
  | .comm sender receiver branches =>
      unfold participatesAllBranches at h
      unfold participatesFirstBranch
      cases hpart : is_participant role sender receiver with
      | true =>
          simp
      | false =>
          simp only [hpart, Bool.false_and, Bool.false_or] at h ⊢
          match hbranches : branches with
          | [] =>
              simp at h
          | (_, cont) :: _ =>
              exact participatesAllBranches_imp_participatesFirstBranch cont role h
termination_by sizeOf g
decreasing_by
  all_goals first
    | exact sizeOf_body_lt_mu _ _
    | (subst hbranches; exact sizeOf_cont_lt_comm _ _ _ _ _)

mutual
  /-- Projection is contractive when role participates through all branches.
      This version is FULLY PROVABLE (no sorry) because we have participation
      info for all branch continuations. -/
  theorem trans_isContractive_of_participatesAllBranches (g : GlobalType) (role : String)
      (hpart : participatesAllBranches role g = true) :
      (trans g role).isContractive = true := by
    match g with
    | .end =>
        unfold participatesAllBranches at hpart
        contradiction
    | .var _ =>
        unfold participatesAllBranches at hpart
        contradiction
    | .mu t body =>
        unfold participatesAllBranches at hpart
        -- New definition: trans (.mu t body) = if (trans body).isGuarded t then .mu t (trans body) else .end
        simp only [trans]
        by_cases hguard : (trans body role).isGuarded t
        · -- Guarded case: result is .mu t (trans body role)
          simp only [hguard, ↓reduceIte, LocalTypeR.isContractive, Bool.true_and]
          exact trans_isContractive_of_participatesAllBranches body role hpart
        · -- Not guarded case: result is .end, which is always contractive
          simp only [hguard, Bool.false_eq_true, ↓reduceIte, LocalTypeR.isContractive]
    | .comm sender receiver branches =>
        unfold participatesAllBranches at hpart
        cases hpart_direct : is_participant role sender receiver with
        | true =>
            -- Role is direct participant: need ALL branches to be contractive
            -- hpart : (true && participatesAllBranchesList ...) || (!true && ...) = true
            -- Simplify: !true = false, false && _ = false, _ || false = _
            simp only [hpart_direct, Bool.not_true, Bool.false_and, Bool.or_false] at hpart
            unfold is_participant at hpart_direct
            cases hrole_s : role == sender with
            | true =>
                have heq : role = sender := beq_iff_eq.mp hrole_s
                rw [trans_comm_sender sender receiver role branches heq]
                simp only [LocalTypeR.isContractive]
                exact transBranches_isContractive_of_participatesAllBranches branches role hpart
            | false =>
                simp only [hrole_s, Bool.false_or] at hpart_direct
                have heq : role = receiver := beq_iff_eq.mp hpart_direct
                have hne : role ≠ sender := by
                  intro heq'
                  rw [heq'] at hrole_s
                  simp at hrole_s
                rw [trans_comm_receiver sender receiver role branches heq hne]
                simp only [LocalTypeR.isContractive]
                exact transBranches_isContractive_of_participatesAllBranches branches role hpart
        | false =>
            -- Role is not direct participant, follows first branch
            -- hpart : (false && ...) || (!false && ...) = true
            simp only [hpart_direct, Bool.not_false, Bool.false_and, Bool.false_or,
              Bool.true_and] at hpart
            unfold is_participant at hpart_direct
            have hne_s : role ≠ sender := by
              intro heq
              rw [heq] at hpart_direct
              simp at hpart_direct
            have hne_r : role ≠ receiver := by
              intro heq
              rw [heq] at hpart_direct
              simp at hpart_direct
            rw [trans_comm_other sender receiver role branches hne_s hne_r]
            match hbranches : branches with
            | [] =>
                simp at hpart
            | (label, cont) :: rest =>
                -- need to prove for cont
                exact trans_isContractive_of_participatesAllBranches cont role hpart
  termination_by sizeOf g
  decreasing_by
    all_goals
      first
      | exact sizeOf_body_lt_mu _ _
      | exact sizeOf_bs_lt_comm _ _ _
      | (subst hbranches; exact sizeOf_cont_lt_comm _ _ _ _ _)

  /-- Helper: transBranches is contractive when role participates in all branches. -/
  theorem transBranches_isContractive_of_participatesAllBranches
      (branches : List (Label × GlobalType)) (role : String)
      (hpart : participatesAllBranchesList role branches = true) :
      LocalTypeR.isContractiveBranches (transBranches branches role) = true := by
    match branches with
    | [] =>
        simp [transBranches, LocalTypeR.isContractiveBranches]
    | (_, cont) :: rest =>
        simp only [transBranches, LocalTypeR.isContractiveBranches, Bool.and_eq_true]
        unfold participatesAllBranchesList at hpart
        simp only [Bool.and_eq_true] at hpart
        constructor
        · exact trans_isContractive_of_participatesAllBranches cont role hpart.1
        · exact transBranches_isContractive_of_participatesAllBranches rest role hpart.2
  termination_by sizeOf branches
  decreasing_by
    all_goals first
      | exact sizeOf_cont_lt_cons _ _ _
      | exact sizeOf_tail_lt_cons _ _
end

/-- Projection preserves well-formedness when role participates through all branches.
    This version is FULLY PROVABLE (no sorry). -/
theorem trans_preserves_WellFormed_allBranches (g : GlobalType) (role : String)
    (hclosed : g.isClosed = true)
    (hpart : participatesAllBranches role g = true) :
    LocalTypeR.WellFormed (trans g role) := by
  constructor
  · exact trans_isClosed_of_isClosed g role hclosed
  · exact trans_isContractive_of_participatesAllBranches g role hpart

end RumpsteakV2.Protocol.Projection.Trans
