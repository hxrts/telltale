import SessionTypes.GlobalType
import SessionTypes.LocalTypeR

/-! # Choreography.Projection.DelegateFree

Delegation-free global types and payload-free local types. Several projection-agreement results relate
`CProject` to `trans`/`transBranches`, whose branches carry no payload
annotation. Delegation projects to a branch annotated with
`some (.chan sid r)`, so those results are stated for delegate-free globals.
-/

namespace SessionTypes.GlobalType

mutual
  /-- The global type contains no `delegate` constructor. -/
  def GlobalType.delegateFree : GlobalType → Bool
    | .end => true
    | .var _ => true
    | .mu _ body => body.delegateFree
    | .comm _ _ branches => delegateFreeBranches branches
    | .delegate _ _ _ _ _ => false

  /-- Branch-list version of `GlobalType.delegateFree`. -/
  def delegateFreeBranches : List (Label × GlobalType) → Bool
    | [] => true
    | (_, g) :: rest => g.delegateFree && delegateFreeBranches rest
end

/-! ## Simp Lemmas -/

@[simp] theorem delegate_free_end : GlobalType.end.delegateFree = true := by
  simp [GlobalType.delegateFree]

@[simp] theorem delegate_free_var (t : String) : (GlobalType.var t).delegateFree = true := by
  simp [GlobalType.delegateFree]

@[simp] theorem delegate_free_mu (t : String) (body : GlobalType) :
    (GlobalType.mu t body).delegateFree = body.delegateFree := by
  simp [GlobalType.delegateFree]

@[simp] theorem delegate_free_comm (s r : String) (bs : List (Label × GlobalType)) :
    (GlobalType.comm s r bs).delegateFree = delegateFreeBranches bs := by
  simp [GlobalType.delegateFree]

@[simp] theorem delegate_free_delegate (p q : String) (sid : Nat) (r : String) (c : GlobalType) :
    (GlobalType.delegate p q sid r c).delegateFree = false := by
  simp [GlobalType.delegateFree]

@[simp] theorem delegate_free_branches_nil : delegateFreeBranches [] = true := by
  simp [delegateFreeBranches]

@[simp] theorem delegate_free_branches_cons (l : Label) (g : GlobalType)
    (rest : List (Label × GlobalType)) :
    delegateFreeBranches ((l, g) :: rest) = (g.delegateFree && delegateFreeBranches rest) := by
  simp [delegateFreeBranches]

/-- Members of a delegate-free branch list are delegate-free. -/
theorem delegate_free_of_mem {bs : List (Label × GlobalType)} {gb : Label × GlobalType}
    (h : delegateFreeBranches bs = true) (hmem : gb ∈ bs) : gb.2.delegateFree = true := by
  induction bs with
  | nil => cases hmem
  | cons hd tl ih =>
      obtain ⟨l, g⟩ := hd
      simp only [delegate_free_branches_cons, Bool.and_eq_true] at h
      rcases List.mem_cons.mp hmem with rfl | htl
      · exact h.1
      · exact ih h.2 htl

/-! ## Preservation under Substitution and Unfolding -/

mutual
  /-- Substituting a delegate-free global into a delegate-free global stays delegate-free. -/
  theorem delegate_free_substitute : (g : GlobalType) → (v : String) → (repl : GlobalType) →
      g.delegateFree = true → repl.delegateFree = true →
      (g.substitute v repl).delegateFree = true
    | .end, _, _, _, _ => by simp [GlobalType.substitute]
    | .var t, v, repl, _, hr => by
        unfold GlobalType.substitute
        split <;> simp_all
    | .mu t body, v, repl, h, hr => by
        unfold GlobalType.substitute
        split
        · exact h
        · simpa using delegate_free_substitute body v repl (by simpa using h) hr
    | .comm _ _ bs, v, repl, h, hr => by
        simp only [GlobalType.substitute, delegate_free_comm]
        exact delegate_free_substitute_branches bs v repl (by simpa using h) hr
    | .delegate _ _ _ _ _, _, _, h, _ => by simp at h

  /-- Branch-list version of `delegate_free_substitute`. -/
  theorem delegate_free_substitute_branches : (bs : List (Label × GlobalType)) → (v : String) →
      (repl : GlobalType) → delegateFreeBranches bs = true → repl.delegateFree = true →
      delegateFreeBranches (substituteBranches bs v repl) = true
    | [], _, _, _, _ => by simp [substituteBranches]
    | (_, g) :: rest, v, repl, h, hr => by
        simp only [substituteBranches, delegate_free_branches_cons, Bool.and_eq_true] at h ⊢
        exact ⟨delegate_free_substitute g v repl h.1 hr,
          delegate_free_substitute_branches rest v repl h.2 hr⟩
end

/-- One unfold step preserves delegate-freedom. -/
theorem delegate_free_unfold (g : GlobalType) (h : g.delegateFree = true) :
    (GlobalType.unfold g).delegateFree = true := by
  cases g with
  | mu t body =>
      exact delegate_free_substitute body t (.mu t body) (by simpa using h) h
  | _ => exact h

/-- Full unfolding preserves delegate-freedom. -/
theorem delegate_free_full_unfold_iter (g : GlobalType) (h : g.delegateFree = true) :
    (GlobalType.fullUnfoldIter g).delegateFree = true := by
  unfold GlobalType.fullUnfoldIter
  induction g.muHeight with
  | zero => exact h
  | succ n ih => exact delegate_free_unfold _ ih

end SessionTypes.GlobalType

/-! ## Payload-Free Local Types -/

namespace SessionTypes.LocalTypeR

mutual
  /-- Every branch of the local type carries no payload annotation (`vt = none`). -/
  def PayloadFree : LocalTypeR → Prop
    | .end => True
    | .var _ => True
    | .mu _ body => PayloadFree body
    | .send _ lbs => BranchesPayloadFree lbs
    | .recv _ lbs => BranchesPayloadFree lbs

  /-- Branch-list version of `PayloadFree`. -/
  def BranchesPayloadFree : List BranchR → Prop
    | [] => True
    | (_, vt, cont) :: rest => vt = none ∧ PayloadFree cont ∧ BranchesPayloadFree rest
end

/-- Members of a payload-free branch list are unannotated and payload-free. -/
theorem branches_payload_free_mem {bs : List BranchR} {lb : BranchR}
    (h : BranchesPayloadFree bs) (hmem : lb ∈ bs) : lb.2.1 = none ∧ PayloadFree lb.2.2 := by
  induction bs with
  | nil => cases hmem
  | cons hd tl ih =>
      obtain ⟨l, vt, c⟩ := hd
      simp only [BranchesPayloadFree] at h
      rcases List.mem_cons.mp hmem with rfl | htl
      · exact ⟨h.1, h.2.1⟩
      · exact ih h.2.2 htl

mutual
  /-- Substitution preserves payload-freedom. -/
  theorem payload_free_substitute : (e : LocalTypeR) → (v : String) → (repl : LocalTypeR) →
      PayloadFree e → PayloadFree repl → PayloadFree (e.substitute v repl)
    | .end, _, _, _, _ => by simp [LocalTypeR.substitute, PayloadFree]
    | .var t, v, repl, _, hr => by
        unfold LocalTypeR.substitute
        split
        · exact hr
        · simp [PayloadFree]
    | .mu t body, v, repl, h, hr => by
        unfold LocalTypeR.substitute
        split
        · exact h
        · exact payload_free_substitute body v repl h hr
    | .send _ bs, v, repl, h, hr => by
        unfold LocalTypeR.substitute
        exact payload_free_substitute_branches bs v repl h hr
    | .recv _ bs, v, repl, h, hr => by
        unfold LocalTypeR.substitute
        exact payload_free_substitute_branches bs v repl h hr

  /-- Branch-list version of `payload_free_substitute`. -/
  theorem payload_free_substitute_branches : (bs : List BranchR) → (v : String) →
      (repl : LocalTypeR) → BranchesPayloadFree bs → PayloadFree repl →
      BranchesPayloadFree (substituteBranches bs v repl)
    | [], _, _, _, _ => by simp [substituteBranches, BranchesPayloadFree]
    | (_, _, c) :: rest, v, repl, h, hr => by
        unfold substituteBranches
        exact ⟨h.1, payload_free_substitute c v repl h.2.1 hr,
          payload_free_substitute_branches rest v repl h.2.2 hr⟩
end

/-- One unfold step preserves payload-freedom. -/
theorem payload_free_unfold (e : LocalTypeR) (h : PayloadFree e) :
    PayloadFree (LocalTypeR.unfold e) := by
  cases e with
  | mu t body => exact payload_free_substitute body t (.mu t body) h h
  | _ => exact h

/-- Full unfolding preserves payload-freedom. -/
theorem payload_free_full_unfold (e : LocalTypeR) (h : PayloadFree e) :
    PayloadFree e.fullUnfold := by
  unfold LocalTypeR.fullUnfold
  generalize e.muHeight = n
  induction n generalizing e with
  | zero => exact h
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      exact ih _ (payload_free_unfold e h)

end SessionTypes.LocalTypeR
