import SessionTypes.LocalTypeR
import SessionCoTypes.Observable
import SessionCoTypes.EQ2

/-! # LocalTypeR Duality

Duality lemmas for LocalTypeR and observable predicates.
This module reuses the existing `LocalTypeR.dual` definition and adds
preservation properties needed to reduce send/recv duplication.
-/

/-
The Problem. Session types have duality: send becomes recv and vice versa. Many
proofs for send have symmetric recv cases. We need duality lemmas that allow
proving one direction and deriving the other via duality.

Solution Structure. Proves `dual_involutive` (duality is its own inverse),
`mu_height_dual` (duality preserves mu-height), `unfold_dual` (duality commutes
with unfolding), and `full_unfold_dual` (duality commutes with full unfolding).
These enable reducing send/recv case duplication in proofs.
-/

namespace SessionTypes.LocalTypeR

open SessionTypes.GlobalType

/-- Duality is an involution (theorem alias). -/
theorem dual_involutive (t : LocalTypeR) : t.dual.dual = t :=
  LocalTypeR.dual_dual t

/-- dualBranches as a map (helper for branch proofs). -/
theorem dual_branches_eq_map (bs : List BranchR) :
    dualBranches bs = bs.map (fun b => (b.1, b.2.1, b.2.2.dual)) := by
  induction bs with
  | nil => rfl
  | cons head tail ih =>
      cases head with
      | mk l rest =>
          cases rest with
          | mk _vt t =>
              simp [dualBranches, ih]

/-- Duality on branches is an involution (theorem alias). -/
theorem dual_branches_involutive (bs : List BranchR) :
    dualBranches (dualBranches bs) = bs :=
  dualBranches_dualBranches bs

/-! ## μ-Height and Unfolding Compatibility -/

/-- Duality preserves muHeight. -/
theorem mu_height_dual : (t : LocalTypeR) → t.dual.muHeight = t.muHeight
  | .end => rfl
  | .var _ => rfl
  | .send _ _ => rfl
  | .recv _ _ => rfl
  | .mu _ body => by
      simp [LocalTypeR.dual, LocalTypeR.muHeight, mu_height_dual body]

/-- Duality commutes with one unfold step. -/
theorem unfold_dual (t : LocalTypeR) : (t.unfold).dual = (t.dual).unfold := by
  cases t <;> simp [LocalTypeR.unfold, LocalTypeR.dual, LocalTypeR.dual_substitute]

/-- Duality commutes with iterated unfold. -/
theorem unfold_iter_dual : ∀ n, ∀ t : LocalTypeR,
    ((LocalTypeR.unfold)^[n] t).dual = (LocalTypeR.unfold)^[n] t.dual
  | 0, t => rfl
  | Nat.succ n, t => by
      -- unfold^[n+1] t = unfold^[n] (unfold t)
      simp [Nat.iterate, unfold_dual, unfold_iter_dual n (t.unfold)]

/-- Duality commutes with fullUnfold. -/
theorem full_unfold_dual (t : LocalTypeR) : t.dual.fullUnfold = (t.fullUnfold).dual := by
  -- Reduce to iterated unfold with the same muHeight.
  simp [LocalTypeR.fullUnfold, mu_height_dual]
  exact (unfold_iter_dual t.muHeight t).symm

/-! ## Free Variable Invariants -/


mutual
  /-- Duality preserves free variables. -/
  theorem free_vars_dual : (t : LocalTypeR) → t.dual.freeVars = t.freeVars := by
    intro t
    cases t with
    | «end» => rfl
    | var v => rfl
    | send p bs =>
        simp [LocalTypeR.dual, LocalTypeR.freeVars, free_vars_of_branches_dual]
    | recv p bs =>
        simp [LocalTypeR.dual, LocalTypeR.freeVars, free_vars_of_branches_dual]
    | mu v body =>
        simp [LocalTypeR.dual, LocalTypeR.freeVars, free_vars_dual]

  /-- Duality preserves freeVarsOfBranches. -/
  theorem free_vars_of_branches_dual : (bs : List BranchR) →
      freeVarsOfBranches (dualBranches bs) = freeVarsOfBranches bs := by
    intro bs
    cases bs with
    | nil => rfl
    | cons head tail =>
        cases head with
        | mk l rest =>
            cases rest with
            | mk _vt t =>
                simp [dualBranches, freeVarsOfBranches, free_vars_dual, free_vars_of_branches_dual]
end

/-- Duality preserves closedness. -/
theorem dual_is_closed (t : LocalTypeR) : t.isClosed = t.dual.isClosed := by
  simp [LocalTypeR.isClosed, free_vars_dual]

/-! ## Guardedness Invariance -/

/-- Duality preserves guardedness. -/
theorem dual_is_guarded : (t : LocalTypeR) → (v : String) →
    t.dual.isGuarded v = t.isGuarded v
  | .end, _ => rfl
  | .var w, v => by simp [LocalTypeR.dual, LocalTypeR.isGuarded]
  | .send p bs, v => by simp [LocalTypeR.dual, LocalTypeR.isGuarded]
  | .recv p bs, v => by simp [LocalTypeR.dual, LocalTypeR.isGuarded]
  | .mu t body, v => by
      by_cases hv : v == t
      · simp [LocalTypeR.dual, LocalTypeR.isGuarded, hv]
      · simp [LocalTypeR.dual, LocalTypeR.isGuarded, hv, dual_is_guarded body v]

/-! ## Contractiveness Invariants -/

mutual
  /-- Duality preserves contractiveness. -/
  theorem dual_is_contractive : (t : LocalTypeR) → t.dual.isContractive = t.isContractive := by
    intro t
    cases t with
    | «end» => rfl
    | var v => rfl
    | send p bs =>
        simp [LocalTypeR.dual, LocalTypeR.isContractive, dual_is_contractive_branches]
    | recv p bs =>
        simp [LocalTypeR.dual, LocalTypeR.isContractive, dual_is_contractive_branches]
    | mu v body =>
        simp [LocalTypeR.dual, LocalTypeR.isContractive, dual_is_guarded, dual_is_contractive]

/-- Duality preserves contractiveness of branches. -/
  theorem dual_is_contractive_branches : (bs : List BranchR) →
      isContractiveBranches (dualBranches bs) = isContractiveBranches bs := by
    intro bs
    cases bs with
    | nil => rfl
    | cons head tail =>
        cases head with
        | mk l rest =>
            cases rest with
            | mk _vt t =>
                simp [dualBranches, isContractiveBranches, dual_is_contractive, dual_is_contractive_branches]
end

/-! ## Well-Formedness Preservation -/

/-- Well-formedness is preserved by duality. -/
theorem WellFormed.dual {t : LocalTypeR} (h : LocalTypeR.WellFormed t) :
    LocalTypeR.WellFormed t.dual := by
  -- Closedness and contractiveness are invariant under dual.
  refine ⟨?_, ?_⟩
  · have hclosed : t.dual.isClosed = t.isClosed := (dual_is_closed t).symm
    simpa [hclosed] using h.closed
  · have hcontr : t.dual.isContractive = t.isContractive := dual_is_contractive t
    simpa [hcontr] using h.contractive

end SessionTypes.LocalTypeR

namespace SessionCoTypes.EQ2

open SessionTypes.LocalTypeR
open SessionTypes.GlobalType

/-! ## EQ2 Duality Compatibility

This section shows that EQ2 is preserved by duality. The proof uses the
coinduction-up-to principle with a relation that tracks EQ2 on the undualized
pair and applies duals at the boundary.
-/

/-- Relation for duality: pairs that are duals of EQ2-equivalent types. -/
private def DualRel : Rel := fun a' b' =>
  ∃ a b, EQ2 a b ∧ a' = a.dual ∧ b' = b.dual

/-- BranchesRel lifts through dualBranches. -/
private theorem branches_rel_dual_branches {bs cs : List BranchR}
    (h : BranchesRel EQ2 bs cs) :
    BranchesRel DualRel (dualBranches bs) (dualBranches cs) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | @cons a b as bs' hhead _ ih =>
      apply List.Forall₂.cons
      · exact ⟨hhead.1, ⟨a.2.2, b.2.2, hhead.2, rfl, rfl⟩⟩
      · exact ih

/-! ## DualRel Branch-Lifting to Closure -/

/-- Convert BranchesRel DualRel to BranchesRel (EQ2_closure DualRel). -/
private theorem branches_rel_dual_rel_to_closure {bs cs : List BranchR}
    (h : BranchesRel DualRel bs cs) :
    BranchesRel (EQ2_closure DualRel) bs cs := by
  exact List.Forall₂.imp (fun _ _ hxy => ⟨hxy.1, Or.inl hxy.2⟩) h

/-! ## DualRel Postfix Helpers: Send/Recv -/

/-- Helper: send.send case for DualRel postfixpoint. -/
private theorem dual_rel_postfix_send_send {p q : String}
    {bs cs : List BranchR}
    (hp : p = q) (hbranches : BranchesRel EQ2 bs cs) :
    EQ2F (EQ2_closure DualRel) (LocalTypeR.send p bs).dual (LocalTypeR.send q cs).dual := by
  simp only [LocalTypeR.dual]
  exact ⟨hp, branches_rel_dual_rel_to_closure (branches_rel_dual_branches hbranches)⟩

/-- Helper: recv.recv case for DualRel postfixpoint. -/
private theorem dual_rel_postfix_recv_recv {p q : String}
    {bs cs : List BranchR}
    (hp : p = q) (hbranches : BranchesRel EQ2 bs cs) :
    EQ2F (EQ2_closure DualRel) (LocalTypeR.recv p bs).dual (LocalTypeR.recv q cs).dual := by
  simp only [LocalTypeR.dual]
  exact ⟨hp, branches_rel_dual_rel_to_closure (branches_rel_dual_branches hbranches)⟩

/-! ## DualRel Postfix Helper: μ/μ Case -/

/-- Helper: mu.mu case for DualRel postfixpoint. -/
private theorem dual_rel_postfix_mu_mu {t s : String} {body body' : LocalTypeR}
    (hleft : EQ2 (body.substitute t (LocalTypeR.mu t body)) (LocalTypeR.mu s body'))
    (hright : EQ2 (LocalTypeR.mu t body) (body'.substitute s (LocalTypeR.mu s body'))) :
    EQ2F (EQ2_closure DualRel) (LocalTypeR.mu t body).dual (LocalTypeR.mu s body').dual := by
  simp only [LocalTypeR.dual]
  constructor
  · left
    use body.substitute t (LocalTypeR.mu t body), LocalTypeR.mu s body'
    refine ⟨hleft, ?_, rfl⟩
    exact (LocalTypeR.dual_substitute body t (LocalTypeR.mu t body)).symm
  · left
    use LocalTypeR.mu t body, body'.substitute s (LocalTypeR.mu s body')
    refine ⟨hright, rfl, ?_⟩
    exact (LocalTypeR.dual_substitute body' s (LocalTypeR.mu s body')).symm

/-! ## DualRel Postfixpoint Proof -/

/-- DualRel is a post-fixpoint of EQ2F up to EQ2 closure. -/
private theorem dual_rel_postfix_upto :
    ∀ a' b', DualRel a' b' → EQ2F (EQ2_closure DualRel) a' b' := by
  intro a' b' ⟨a, b, hab, ha', hb'⟩; subst ha' hb'
  have hf : EQ2F EQ2 a b := EQ2.destruct hab
  cases a <;> cases b <;> simp only [EQ2F] at hf ⊢ <;> try exact hf
  case send.send p bs q cs =>
    obtain ⟨hp, hbranches⟩ := hf; exact dual_rel_postfix_send_send hp hbranches
  case recv.recv p bs q cs =>
    obtain ⟨hp, hbranches⟩ := hf; exact dual_rel_postfix_recv_recv hp hbranches
  case mu.mu t body s body' =>
    obtain ⟨hleft, hright⟩ := hf; exact dual_rel_postfix_mu_mu hleft hright

/-! ## DualRel Postfixpoint Proof: Asymmetric μ Cases -/

  case mu.end t body =>
    simp [LocalTypeR.dual]
    left
    use body.substitute t (LocalTypeR.mu t body), .end
    exact ⟨hf, (LocalTypeR.dual_substitute body t (LocalTypeR.mu t body)).symm, rfl⟩
  case mu.var t body v =>
    simp [LocalTypeR.dual]
    left
    use body.substitute t (LocalTypeR.mu t body), .var v
    exact ⟨hf, (LocalTypeR.dual_substitute body t (LocalTypeR.mu t body)).symm, rfl⟩
  case mu.send t body p bs =>
    simp [LocalTypeR.dual]
    left
    use body.substitute t (LocalTypeR.mu t body), .send p bs
    exact ⟨hf, (LocalTypeR.dual_substitute body t (LocalTypeR.mu t body)).symm, rfl⟩
  case mu.recv t body p bs =>
    simp [LocalTypeR.dual]
    left
    use body.substitute t (LocalTypeR.mu t body), .recv p bs
    exact ⟨hf, (LocalTypeR.dual_substitute body t (LocalTypeR.mu t body)).symm, rfl⟩
  case end.mu s body' =>
    simp [LocalTypeR.dual]
    left
    use .end, body'.substitute s (LocalTypeR.mu s body')
    exact ⟨hf, rfl, (LocalTypeR.dual_substitute body' s (LocalTypeR.mu s body')).symm⟩
  case var.mu v s body' =>
    simp [LocalTypeR.dual]
    left
    use .var v, body'.substitute s (LocalTypeR.mu s body')
    exact ⟨hf, rfl, (LocalTypeR.dual_substitute body' s (LocalTypeR.mu s body')).symm⟩
  case send.mu p bs s body' =>
    simp [LocalTypeR.dual]
    left
    use .send p bs, body'.substitute s (LocalTypeR.mu s body')
    exact ⟨hf, rfl, (LocalTypeR.dual_substitute body' s (LocalTypeR.mu s body')).symm⟩
  case recv.mu p bs s body' =>
    simp [LocalTypeR.dual]
    left
    use .recv p bs, body'.substitute s (LocalTypeR.mu s body')
    exact ⟨hf, rfl, (LocalTypeR.dual_substitute body' s (LocalTypeR.mu s body')).symm⟩

/-! ## EQ2 Duality Theorem -/

/-- Duality respects EQ2: if two types are EQ2-equivalent, their duals are too. -/
theorem eq2_dual {a b : LocalTypeR} (h : EQ2 a b) : EQ2 a.dual b.dual := by
  apply eq2_coind_upto dual_rel_postfix_upto
  exact ⟨a, b, h, rfl, rfl⟩

end SessionCoTypes.EQ2
