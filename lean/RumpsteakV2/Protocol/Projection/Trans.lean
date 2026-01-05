import RumpsteakV2.Protocol.GlobalType
import RumpsteakV2.Protocol.LocalTypeR

/-! # RumpsteakV2.Protocol.Projection.Trans

Candidate projection for V2 (Coq-style `trans`).

## Expose

The following definitions form the semantic interface for proofs:

- `trans`
- `lcontractive`
-/

namespace RumpsteakV2.Protocol.Projection.Trans

open RumpsteakV2.Protocol.GlobalType
open RumpsteakV2.Protocol.LocalTypeR

/-- Placeholder guardedness check for recursive globals.
    This is intentionally permissive and will be refined in Phase A proofs. -/
def lcontractive (_g : GlobalType) : Bool :=
  true

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

private theorem sizeOf_bs_lt_comm (sender receiver : String) (bs : List (Label × GlobalType)) :
    sizeOf bs < sizeOf (GlobalType.comm sender receiver bs) := by
  have hk : 0 < 1 + sizeOf sender + sizeOf receiver := by
    have h : 0 < Nat.succ (sizeOf sender + sizeOf receiver) := Nat.succ_pos _
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
  have h : sizeOf bs < (1 + sizeOf sender + sizeOf receiver) + sizeOf bs :=
    Nat.lt_add_of_pos_left (n := sizeOf bs) (k := 1 + sizeOf sender + sizeOf receiver) hk
  simpa [GlobalType.comm.sizeOf_spec, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

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
  simpa using (sizeOf_head_snd_lt_comm sender receiver (label, cont) rest)

private theorem sizeOf_cont_lt_cons (label : Label) (cont : GlobalType) (rest : List (Label × GlobalType)) :
    sizeOf cont < sizeOf ((label, cont) :: rest) := by
  simpa using (sizeOf_head_snd_lt_cons (label, cont) rest)

private theorem sizeOf_body_lt_mu (t : String) (body : GlobalType) :
    sizeOf body < sizeOf (GlobalType.mu t body) := by
  have hk : 0 < 1 + sizeOf t := by
    simpa [Nat.one_add] using (Nat.succ_pos (sizeOf t))
  have h : sizeOf body < (1 + sizeOf t) + sizeOf body :=
    Nat.lt_add_of_pos_left (n := sizeOf body) (k := 1 + sizeOf t) hk
  simpa [GlobalType.mu.sizeOf_spec, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

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
    cases g with
    | «end» =>
        simpa [trans.eq_1, LocalTypeR.freeVars, GlobalType.freeVars] using hx
    | var t =>
        simpa [trans.eq_2, LocalTypeR.freeVars, GlobalType.freeVars] using hx
    | mu t body =>
        cases hcontract : lcontractive body with
        | true =>
            have hx' : x ∈ (trans body role).freeVars ∧ x ≠ t := by
              simpa [trans.eq_3, hcontract, LocalTypeR.freeVars, List.mem_filter, bne_iff_ne, ne_eq,
                decide_eq_true_eq] using hx
            have hmem : x ∈ body.freeVars := (trans_freeVars_subset body role) hx'.1
            have : x ∈ body.freeVars.filter (· != t) := by
              simp [List.mem_filter, bne_iff_ne, ne_eq, decide_eq_true_eq, hmem, hx'.2]
            simpa [GlobalType.freeVars] using this
        | false =>
            simpa [trans.eq_3, hcontract, LocalTypeR.freeVars, GlobalType.freeVars] using hx
    | comm sender receiver branches =>
        have hsubset := transBranches_freeVars_subset branches role
        cases hsender : role == sender with
        | true =>
            cases branches with
            | nil =>
                simp [trans.eq_4, hsender] at hx
                simp [LocalTypeR.freeVars, LocalTypeR.freeVarsOfBranches_eq_flatMap, List.mem_flatMap] at hx
                rcases hx with ⟨a, b, hmem, hxmem⟩
                have hxMem :
                    x ∈ (transBranches [] role).flatMap (fun (_, t) => t.freeVars) := by
                  exact (List.mem_flatMap).2 ⟨(a, b), hmem, hxmem⟩
                have : x ∈ ([] : List (Label × GlobalType)).flatMap (fun (_, g) => g.freeVars) :=
                  hsubset hxMem
                simpa [GlobalType.freeVars, GlobalType.freeVarsOfBranches_eq_flatMap] using this
            | cons head tail =>
                cases head with
                | mk label cont =>
                    simp [trans.eq_5, hsender] at hx
                    simp [LocalTypeR.freeVars, LocalTypeR.freeVarsOfBranches_eq_flatMap, List.mem_flatMap] at hx
                    rcases hx with ⟨a, b, hmem, hxmem⟩
                    have hxMem :
                        x ∈ (transBranches ((label, cont) :: tail) role).flatMap
                          (fun (_, t) => t.freeVars) := by
                      exact (List.mem_flatMap).2 ⟨(a, b), hmem, hxmem⟩
                    have : x ∈ ((label, cont) :: tail).flatMap (fun (_, g) => g.freeVars) :=
                      hsubset hxMem
                    simpa [GlobalType.freeVars, GlobalType.freeVarsOfBranches_eq_flatMap] using this
        | false =>
            cases hreceiver : role == receiver with
            | true =>
                cases branches with
                | nil =>
                    simp [trans.eq_4, hsender, hreceiver] at hx
                    simp [LocalTypeR.freeVars, LocalTypeR.freeVarsOfBranches_eq_flatMap, List.mem_flatMap] at hx
                    rcases hx with ⟨a, b, hmem, hxmem⟩
                    have hxMem :
                        x ∈ (transBranches [] role).flatMap (fun (_, t) => t.freeVars) := by
                      exact (List.mem_flatMap).2 ⟨(a, b), hmem, hxmem⟩
                    have : x ∈ ([] : List (Label × GlobalType)).flatMap (fun (_, g) => g.freeVars) :=
                      hsubset hxMem
                    simpa [GlobalType.freeVars, GlobalType.freeVarsOfBranches_eq_flatMap] using this
                | cons head tail =>
                    cases head with
                    | mk label cont =>
                        simp [trans.eq_5, hsender, hreceiver] at hx
                        simp [LocalTypeR.freeVars, LocalTypeR.freeVarsOfBranches_eq_flatMap, List.mem_flatMap] at hx
                        rcases hx with ⟨a, b, hmem, hxmem⟩
                        have hxMem :
                            x ∈ (transBranches ((label, cont) :: tail) role).flatMap
                              (fun (_, t) => t.freeVars) := by
                          exact (List.mem_flatMap).2 ⟨(a, b), hmem, hxmem⟩
                        have : x ∈ ((label, cont) :: tail).flatMap (fun (_, g) => g.freeVars) :=
                          hsubset hxMem
                        simpa [GlobalType.freeVars, GlobalType.freeVarsOfBranches_eq_flatMap] using this
            | false =>
                cases branches with
                | nil =>
                    simp [trans.eq_4, hsender, hreceiver] at hx
                    simp [LocalTypeR.freeVars] at hx
                    simpa [GlobalType.freeVars, GlobalType.freeVarsOfBranches_eq_flatMap] using hx
                | cons head tail =>
                    cases head with
                    | mk label cont =>
                        have hmem : x ∈ (trans cont role).freeVars := by
                          simpa [trans.eq_5, hsender, hreceiver] using hx
                        have hmem' : x ∈ cont.freeVars := (trans_freeVars_subset cont role) hmem
                        have hxMem : x ∈ ((label, cont) :: tail).flatMap (fun (_, g) => g.freeVars) := by
                          refine (List.mem_flatMap).2 ?_
                          exact ⟨(label, cont), by simp, by simpa using hmem'⟩
                        simpa [GlobalType.freeVars, GlobalType.freeVarsOfBranches_eq_flatMap] using hxMem
  termination_by
    g _ => sizeOf g

  /-- Branch-wise free variable inclusion for `transBranches`. -/
  theorem transBranches_freeVars_subset (branches : List (Label × GlobalType)) (role : String) :
      (transBranches branches role).flatMap (fun (_, t) => t.freeVars) ⊆
        branches.flatMap (fun (_, g) => g.freeVars) := by
    intro y hy
    induction branches with
    | nil =>
        simpa [transBranches] using hy
    | cons head tail ih =>
        cases head with
        | mk label cont =>
            have hy' :
                y ∈ (trans cont role).freeVars ∨
                  y ∈ (transBranches tail role).flatMap (fun (_, t) => t.freeVars) := by
              simpa [transBranches, List.flatMap, List.mem_append] using hy
            cases hy' with
            | inl hhead =>
                have hmem : y ∈ cont.freeVars := (trans_freeVars_subset cont role) hhead
                refine (List.mem_flatMap).2 ?_
                exact ⟨(label, cont), by simp, by simpa using hmem⟩
            | inr htail =>
                have hmem : y ∈ tail.flatMap (fun (_, g) => g.freeVars) := ih htail
                rcases (List.mem_flatMap).1 hmem with ⟨pair, hpair, hmem'⟩
                refine (List.mem_flatMap).2 ?_
                exact ⟨pair, by simp [hpair], hmem'⟩
  termination_by
    branches _ => sizeOf branches
  decreasing_by
    all_goals
      first
      | exact sizeOf_cont_lt_cons _ _ _
      | exact sizeOf_tail_lt_cons _ _
end

end RumpsteakV2.Protocol.Projection.Trans
