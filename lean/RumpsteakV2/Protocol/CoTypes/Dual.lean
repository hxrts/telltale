import RumpsteakV2.Protocol.LocalTypeR
import RumpsteakV2.Protocol.CoTypes.Observable
import RumpsteakV2.Protocol.CoTypes.EQ2

/-! # LocalTypeR Duality

Duality lemmas for LocalTypeR and observable predicates.
This module reuses the existing `LocalTypeR.dual` definition and adds
preservation properties needed to reduce send/recv duplication.
-/

namespace RumpsteakV2.Protocol.LocalTypeR

open RumpsteakV2.Protocol.GlobalType

/-- Duality is an involution (theorem alias). -/
theorem dual_involutive (t : LocalTypeR) : t.dual.dual = t :=
  LocalTypeR.dual_dual t

/-- dualBranches as a map (helper for branch proofs). -/
theorem dualBranches_eq_map (bs : List (Label × LocalTypeR)) :
    dualBranches bs = bs.map (fun b => (b.1, b.2.dual)) := by
  induction bs with
  | nil => rfl
  | cons head tail ih =>
      cases head with
      | mk l t =>
          simp [dualBranches, ih]

/-- Duality on branches is an involution (theorem alias). -/
theorem dualBranches_involutive (bs : List (Label × LocalTypeR)) :
    dualBranches (dualBranches bs) = bs :=
  dualBranches_dualBranches bs

/-- Duality preserves muHeight. -/
theorem muHeight_dual : (t : LocalTypeR) → t.dual.muHeight = t.muHeight
  | .end => rfl
  | .var _ => rfl
  | .send _ _ => rfl
  | .recv _ _ => rfl
  | .mu _ body => by
      simp [LocalTypeR.dual, LocalTypeR.muHeight, muHeight_dual body]

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
theorem fullUnfold_dual (t : LocalTypeR) : t.dual.fullUnfold = (t.fullUnfold).dual := by
  -- Reduce to iterated unfold with the same muHeight.
  simp [LocalTypeR.fullUnfold, muHeight_dual]
  exact (unfold_iter_dual t.muHeight t).symm


mutual
  /-- Duality preserves free variables. -/
  theorem freeVars_dual : (t : LocalTypeR) → t.dual.freeVars = t.freeVars := by
    intro t
    cases t with
    | «end» => rfl
    | var v => rfl
    | send p bs =>
        simp [LocalTypeR.dual, LocalTypeR.freeVars, freeVarsOfBranches_dual]
    | recv p bs =>
        simp [LocalTypeR.dual, LocalTypeR.freeVars, freeVarsOfBranches_dual]
    | mu v body =>
        simp [LocalTypeR.dual, LocalTypeR.freeVars, freeVars_dual]

  /-- Duality preserves freeVarsOfBranches. -/
  theorem freeVarsOfBranches_dual : (bs : List (Label × LocalTypeR)) →
      freeVarsOfBranches (dualBranches bs) = freeVarsOfBranches bs := by
    intro bs
    cases bs with
    | nil => rfl
    | cons head tail =>
        cases head with
        | mk l t =>
            simp [dualBranches, freeVarsOfBranches, freeVars_dual, freeVarsOfBranches_dual]
end

/-- Duality preserves closedness. -/
theorem dual_isClosed (t : LocalTypeR) : t.isClosed = t.dual.isClosed := by
  simp [LocalTypeR.isClosed, freeVars_dual]

/-- Duality preserves guardedness. -/
theorem dual_isGuarded : (t : LocalTypeR) → (v : String) →
    t.dual.isGuarded v = t.isGuarded v
  | .end, _ => rfl
  | .var w, v => by simp [LocalTypeR.dual, LocalTypeR.isGuarded]
  | .send p bs, v => by simp [LocalTypeR.dual, LocalTypeR.isGuarded]
  | .recv p bs, v => by simp [LocalTypeR.dual, LocalTypeR.isGuarded]
  | .mu t body, v => by
      by_cases hv : v == t
      · simp [LocalTypeR.dual, LocalTypeR.isGuarded, hv]
      · simp [LocalTypeR.dual, LocalTypeR.isGuarded, hv, dual_isGuarded body v]

mutual
  /-- Duality preserves contractiveness. -/
  theorem dual_isContractive : (t : LocalTypeR) → t.dual.isContractive = t.isContractive := by
    intro t
    cases t with
    | «end» => rfl
    | var v => rfl
    | send p bs =>
        simp [LocalTypeR.dual, LocalTypeR.isContractive, dual_isContractiveBranches]
    | recv p bs =>
        simp [LocalTypeR.dual, LocalTypeR.isContractive, dual_isContractiveBranches]
    | mu v body =>
        simp [LocalTypeR.dual, LocalTypeR.isContractive, dual_isGuarded, dual_isContractive]

  /-- Duality preserves contractiveness of branches. -/
  theorem dual_isContractiveBranches : (bs : List (Label × LocalTypeR)) →
      isContractiveBranches (dualBranches bs) = isContractiveBranches bs := by
    intro bs
    cases bs with
    | nil => rfl
    | cons head tail =>
        cases head with
        | mk l t =>
            simp [dualBranches, isContractiveBranches, dual_isContractive, dual_isContractiveBranches]
end

end RumpsteakV2.Protocol.LocalTypeR

namespace RumpsteakV2.Protocol.CoTypes.Observable

open RumpsteakV2.Protocol.LocalTypeR

open RumpsteakV2.Protocol.GlobalType

/-- Unfolding to end is preserved by dual. -/
theorem UnfoldsToEnd.dual {t : LocalTypeR} (h : UnfoldsToEnd t) : UnfoldsToEnd t.dual := by
  induction h with
  | base =>
      simpa [LocalTypeR.dual] using (UnfoldsToEnd.base)
  | @mu v body _ ih =>
      have ih' : UnfoldsToEnd (body.dual.substitute v (LocalTypeR.mu v body).dual) := by
        simpa [LocalTypeR.dual_substitute] using ih
      simpa [LocalTypeR.dual] using (UnfoldsToEnd.mu (t := v) (body := body.dual) ih')

/-- Unfolding to var is preserved by dual. -/
theorem UnfoldsToVar.dual {t : LocalTypeR} {v : String} (h : UnfoldsToVar t v) :
    UnfoldsToVar t.dual v := by
  induction h with
  | base =>
      simpa [LocalTypeR.dual] using (UnfoldsToVar.base)
  | @mu t body v' _ ih =>
      have ih' : UnfoldsToVar (body.dual.substitute t (LocalTypeR.mu t body).dual) v' := by
        simpa [LocalTypeR.dual_substitute] using ih
      simpa [LocalTypeR.dual] using (UnfoldsToVar.mu (t := t) (body := body.dual) (v := v') ih')

/-- Dual of CanSend is CanRecv. -/
theorem CanSend.dual {t : LocalTypeR} {p : String} {bs : List (Label × LocalTypeR)}
    (h : CanSend t p bs) : CanRecv t.dual p (LocalTypeR.dualBranches bs) := by
  induction h with
  | base =>
      simpa [LocalTypeR.dual] using (CanRecv.base)
  | @mu t body p' bs' _ ih =>
      have ih' : CanRecv (body.dual.substitute t (LocalTypeR.mu t body).dual) p' (LocalTypeR.dualBranches bs') := by
        simpa [LocalTypeR.dual_substitute] using ih
      simpa [LocalTypeR.dual] using (CanRecv.mu (t := t) (body := body.dual) (partner := p')
        (branches := LocalTypeR.dualBranches bs') ih')

/-- Dual of CanRecv is CanSend. -/
theorem CanRecv.dual {t : LocalTypeR} {p : String} {bs : List (Label × LocalTypeR)}
    (h : CanRecv t p bs) : CanSend t.dual p (LocalTypeR.dualBranches bs) := by
  induction h with
  | base =>
      simpa [LocalTypeR.dual] using (CanSend.base)
  | @mu t body p' bs' _ ih =>
      have ih' : CanSend (body.dual.substitute t (LocalTypeR.mu t body).dual) p' (LocalTypeR.dualBranches bs') := by
        simpa [LocalTypeR.dual_substitute] using ih
      simpa [LocalTypeR.dual] using (CanSend.mu (t := t) (body := body.dual) (partner := p')
        (branches := LocalTypeR.dualBranches bs') ih')

/-- Duality swaps CanSend and CanRecv. -/
theorem CanSend.dual_iff_CanRecv {t : LocalTypeR} {p : String} {bs : List (Label × LocalTypeR)} :
    CanSend t p bs ↔ CanRecv t.dual p (LocalTypeR.dualBranches bs) := by
  constructor
  · exact CanSend.dual
  · intro h
    have h' : CanSend t.dual.dual p (LocalTypeR.dualBranches (LocalTypeR.dualBranches bs)) :=
      CanRecv.dual (t := t.dual) h
    simpa [LocalTypeR.dual_involutive, LocalTypeR.dualBranches_involutive] using h'

/-- Duality swaps CanRecv and CanSend. -/
theorem CanRecv.dual_iff_CanSend {t : LocalTypeR} {p : String} {bs : List (Label × LocalTypeR)} :
    CanRecv t p bs ↔ CanSend t.dual p (LocalTypeR.dualBranches bs) := by
  constructor
  · exact CanRecv.dual
  · intro h
    have h' : CanRecv t.dual.dual p (LocalTypeR.dualBranches (LocalTypeR.dualBranches bs)) :=
      CanSend.dual (t := t.dual) h
    simpa [LocalTypeR.dual_involutive, LocalTypeR.dualBranches_involutive] using h'

end RumpsteakV2.Protocol.CoTypes.Observable

namespace RumpsteakV2.Protocol.CoTypes.EQ2

open RumpsteakV2.Protocol.LocalTypeR
open RumpsteakV2.Protocol.GlobalType

/-! ## EQ2 Duality Compatibility

This section shows that EQ2 is preserved by duality. The proof uses the
coinduction-up-to principle with a relation that tracks EQ2 on the undualized
pair and applies duals at the boundary.
-/

/-- Relation for duality: pairs that are duals of EQ2-equivalent types. -/
private def DualRel : Rel := fun a' b' =>
  ∃ a b, EQ2 a b ∧ a' = a.dual ∧ b' = b.dual

/-- BranchesRel lifts through dualBranches. -/
private theorem BranchesRel_dualBranches {bs cs : List (Label × LocalTypeR)}
    (h : BranchesRel EQ2 bs cs) :
    BranchesRel DualRel (dualBranches bs) (dualBranches cs) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | @cons a b as bs' hhead _ ih =>
      apply List.Forall₂.cons
      · exact ⟨hhead.1, ⟨a.2, b.2, hhead.2, rfl, rfl⟩⟩
      · exact ih

/-- Convert BranchesRel DualRel to BranchesRel (EQ2_closure DualRel). -/
private theorem BranchesRel_DualRel_to_closure {bs cs : List (Label × LocalTypeR)}
    (h : BranchesRel DualRel bs cs) :
    BranchesRel (EQ2_closure DualRel) bs cs := by
  exact List.Forall₂.imp (fun _ _ hxy => ⟨hxy.1, Or.inl hxy.2⟩) h

/-- Helper: send.send case for DualRel postfixpoint. -/
private theorem DualRel_postfix_send_send {p q : String}
    {bs cs : List (Label × LocalTypeR)}
    (hp : p = q) (hbranches : BranchesRel EQ2 bs cs) :
    EQ2F (EQ2_closure DualRel) (LocalTypeR.send p bs).dual (LocalTypeR.send q cs).dual := by
  simp only [LocalTypeR.dual]
  exact ⟨hp, BranchesRel_DualRel_to_closure (BranchesRel_dualBranches hbranches)⟩

/-- Helper: recv.recv case for DualRel postfixpoint. -/
private theorem DualRel_postfix_recv_recv {p q : String}
    {bs cs : List (Label × LocalTypeR)}
    (hp : p = q) (hbranches : BranchesRel EQ2 bs cs) :
    EQ2F (EQ2_closure DualRel) (LocalTypeR.recv p bs).dual (LocalTypeR.recv q cs).dual := by
  simp only [LocalTypeR.dual]
  exact ⟨hp, BranchesRel_DualRel_to_closure (BranchesRel_dualBranches hbranches)⟩

/-- Helper: mu.mu case for DualRel postfixpoint. -/
private theorem DualRel_postfix_mu_mu {t s : String} {body body' : LocalTypeR}
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

/-- DualRel is a post-fixpoint of EQ2F up to EQ2 closure. -/
private theorem DualRel_postfix_upto :
    ∀ a' b', DualRel a' b' → EQ2F (EQ2_closure DualRel) a' b' := by
  intro a' b' ⟨a, b, hab, ha', hb'⟩; subst ha' hb'
  have hf : EQ2F EQ2 a b := EQ2.destruct hab
  cases a <;> cases b <;> simp only [EQ2F] at hf ⊢ <;> try exact hf
  case send.send p bs q cs =>
    obtain ⟨hp, hbranches⟩ := hf; exact DualRel_postfix_send_send hp hbranches
  case recv.recv p bs q cs =>
    obtain ⟨hp, hbranches⟩ := hf; exact DualRel_postfix_recv_recv hp hbranches
  case mu.mu t body s body' =>
    obtain ⟨hleft, hright⟩ := hf; exact DualRel_postfix_mu_mu hleft hright
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

/-- Duality respects EQ2: if two types are EQ2-equivalent, their duals are too. -/
theorem EQ2_dual {a b : LocalTypeR} (h : EQ2 a b) : EQ2 a.dual b.dual := by
  apply EQ2_coind_upto DualRel_postfix_upto
  exact ⟨a, b, h, rfl, rfl⟩

end RumpsteakV2.Protocol.CoTypes.EQ2
