import SessionCoTypes.SubstCommBarendregt.SubstRel

/-! # SubstRel Standard Case Analysis and Main Theorem

Proves `SubstRel_postfix_standard` and `EQ2_substitute_barendregt`.
-/

/-
The Problem. The main theorem `EQ2_substitute_barendregt` requires showing SubstRel
is a post-fixpoint of EQ2F. This involves case analysis on all type constructors
with careful handling of the mu case under Barendregt conditions.

Solution Structure. Proves `BranchesRel_substitute` lifting branch relations through
substitution. `SubstRel_postfix_standard` handles case analysis on EQ2F, using
`bne_of_notBoundAt_mu` for mu cases. The main theorem `EQ2_substitute_barendregt`
follows by coinduction using SubstRel as the witness relation.
-/

namespace SessionCoTypes.SubstCommBarendregt
open SessionTypes.LocalTypeR
open SessionCoTypes.EQ2
open SessionTypes.GlobalType
/-! ## Standard Case Analysis -/

/-- Helper: lift BranchesRel through substitution. -/
theorem BranchesRel_substitute (var : String) (repl : LocalTypeR)
    (bs cs : List BranchR)
    (hbranches : BranchesRel EQ2 bs cs)
    (hbarBs : notBoundAtBranches var bs = true)
    (hbarCs : notBoundAtBranches var cs = true)
    (_hfresh : ∀ t, isFreeIn t repl = false) :
    BranchesRel (EQ2_closure (SubstRel var repl))
      (SessionTypes.LocalTypeR.substituteBranches bs var repl) (SessionTypes.LocalTypeR.substituteBranches cs var repl) := by
  induction hbranches with
  | nil => exact List.Forall₂.nil
  | @cons a b as bs' hhead _ ih =>
    unfold SessionTypes.LocalTypeR.substituteBranches
    unfold notBoundAtBranches at hbarBs hbarCs
    have ⟨hbarA, hbarAs⟩ := Bool.and_eq_true_iff.mp hbarBs
    have ⟨hbarB, hbarBs'⟩ := Bool.and_eq_true_iff.mp hbarCs
    apply List.Forall₂.cons
    · constructor
      · exact hhead.1
      · exact Or.inl (SubstRel.base a.2.2 b.2.2 hhead.2 hbarA hbarB)
    · exact ih hbarAs hbarBs'

/-- Helper to convert htvar/hsvar proofs to the expected form. -/
private theorem bne_of_notBoundAt_mu {v t : String} {body : LocalTypeR}
    (hbar : notBoundAt v (.mu t body) = true) :
    (t == v) = false := by
  unfold notBoundAt at hbar
  have ⟨hvt, _⟩ := Bool.and_eq_true_iff.mp hbar
  simp only [bne_iff_ne, ne_eq] at hvt
  exact beq_eq_false_iff_ne.mpr (Ne.symm hvt)

/-- Standard one-step analysis for SubstRel after flattening. -/

end SessionCoTypes.SubstCommBarendregt
