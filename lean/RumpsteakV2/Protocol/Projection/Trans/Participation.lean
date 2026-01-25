import RumpsteakV2.Protocol.Projection.Trans.Core


namespace RumpsteakV2.Protocol.Projection.Trans
open RumpsteakV2.Protocol.GlobalType
open RumpsteakV2.Protocol.LocalTypeR
open RumpsteakV2.Protocol.Participation
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

theorem participatesFirstBranch_imp_participates (g : GlobalType) (role : String) :
    participatesFirstBranch role g = true → participates role g = true := by
  intro h
  match g with
  | .end => simpa [participatesFirstBranch] using h
  | .var _ => simpa [participatesFirstBranch] using h
  | .mu t body =>
      unfold participatesFirstBranch at h
      unfold participates
      exact participatesFirstBranch_imp_participates body role h
  | .comm sender receiver branches =>
      unfold participatesFirstBranch at h
      unfold participates
      cases hpart : is_participant role sender receiver with
      | true =>
          simp [hpart]
      | false =>
          simp [hpart] at h ⊢
          match hbranches : branches with
          | [] =>
              simp at h
          | (label, cont) :: rest =>
              simp [participatesBranches, Bool.or_eq_true]
              exact Or.inl (participatesFirstBranch_imp_participates cont role h)

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

private theorem isGuarded_send (p : String) (bs : List (Label × LocalTypeR)) (v : String) :
    (LocalTypeR.send p bs).isGuarded v = true := by
  simp [LocalTypeR.isGuarded]

private theorem isGuarded_recv (p : String) (bs : List (Label × LocalTypeR)) (v : String) :
    (LocalTypeR.recv p bs).isGuarded v = true := by
  simp [LocalTypeR.isGuarded]

private theorem isGuarded_end (v : String) : (LocalTypeR.end).isGuarded v = true := by
  simp [LocalTypeR.isGuarded]

/-- Helper: trans result is guarded when role participates via first-branch path.

    The key insight: participation means we eventually reach a .send/.recv which
    guards any variable. The guardedness propagates up through the structure.

    Note: This does NOT require closedness - participation alone is sufficient. -/
private theorem trans_isGuarded_of_participatesFirstBranch_comm_participant
    (sender receiver : String) (branches : List (Label × GlobalType))
    (v : String) (role : String)
    (hpart : is_participant role sender receiver = true) :
    (trans (.comm sender receiver branches) role).isGuarded v = true := by
  -- Direct participant: sender or receiver.
  unfold is_participant at hpart
  cases hrole_s : role == sender with
  | true =>
      have heq : role = sender := beq_iff_eq.mp hrole_s
      rw [trans_comm_sender sender receiver role branches heq]
      exact isGuarded_send receiver (transBranches branches role) v
  | false =>
      simp only [hrole_s, Bool.false_or] at hpart
      have heq : role = receiver := beq_iff_eq.mp hpart
      have hne : role ≠ sender := by
        intro heq'
        rw [heq'] at hrole_s
        simp at hrole_s
      rw [trans_comm_receiver sender receiver role branches heq hne]
      exact isGuarded_recv sender (transBranches branches role) v

theorem trans_isGuarded_of_participatesFirstBranch
    (g : GlobalType) (v : String) (role : String)
    (hpart : participatesFirstBranch role g = true) :
    (trans g role).isGuarded v = true := by
  match g with
  | .end => simpa [participatesFirstBranch] using hpart
  | .var _ => simpa [participatesFirstBranch] using hpart
  | .mu t body =>
      -- Mu case: follow the body and propagate guardedness.
      unfold participatesFirstBranch at hpart
      simp only [trans]
      by_cases hguard : (trans body role).isGuarded t
      · simp only [hguard, ↓reduceIte, LocalTypeR.isGuarded]
        by_cases hvt : v = t
        · simp [hvt]
        · have hvne : (v == t) = false := beq_eq_false_iff_ne.mpr hvt
          simp only [hvne, Bool.false_eq_true, ↓reduceIte]
          exact trans_isGuarded_of_participatesFirstBranch body v role hpart
      · simp [hguard, Bool.false_eq_true, ↓reduceIte, LocalTypeR.isGuarded]
  | .comm sender receiver branches =>
      -- Comm case: direct participant or follow the first branch.
      cases hpart_direct : is_participant role sender receiver with
      | true =>
          exact trans_isGuarded_of_participatesFirstBranch_comm_participant sender receiver branches v role
            hpart_direct
      | false =>
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
          cases branches with
          | nil =>
              exact isGuarded_end v
          | cons head tail =>
              cases head with
              | mk label cont =>
                  have hcont' :
                      is_participant role sender receiver = true ∨
                        participatesFirstBranch role cont = true := by
                    simpa [participatesFirstBranch, Bool.or_eq_true] using hpart
                  have hcont : participatesFirstBranch role cont = true := by
                    cases hcont' with
                    | inl hleft =>
                        have hleft' : False := by
                          simpa [is_participant, hpart_direct] using hleft
                        exact hleft'.elim
                    | inr hright =>
                        exact hright
                  exact trans_isGuarded_of_participatesFirstBranch cont v role hcont

end RumpsteakV2.Protocol.Projection.Trans
