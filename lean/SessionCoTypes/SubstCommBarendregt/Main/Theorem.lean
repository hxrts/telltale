import SessionCoTypes.SubstCommBarendregt.Main.Postfix

/-! # SessionCoTypes.SubstCommBarendregt.Main.Theorem

Main Barendregt substitution theorem for EQ2.
-/

/-
The Problem. Downstream substitution proofs need a single theorem-level entry
point once postfix closure is established.

Solution Structure. Applies coinduction with `SubstRel` and the postfix theorem
from `Postfix`.
-/

namespace SessionCoTypes.SubstCommBarendregt

/-! ## Main Theorem -/

/-! ## Main Theorem -/

/-- EQ2 is preserved under substitution when Barendregt conditions hold.

    This theorem requires:
    - `notBoundAt var a = true` and `notBoundAt var b = true`: var is not used as a binder
    - `hfresh`: repl is closed (no free variables)
    - `hnomu`: repl is not a mu type at top level (needed for unfold_subst_eq_subst_unfold)

    For general EQ2_substitute without the hnomu restriction, use the Bisim approach
    in `EQ2_substitute_via_Bisim` (Bisim.lean) which uses EQ2 instead of syntactic equality. -/
theorem EQ2_substitute_barendregt (a b : LocalTypeR) (var : String) (repl : LocalTypeR)
    (h : EQ2 a b)
    (hbarA : notBoundAt var a = true)
    (hbarB : notBoundAt var b = true)
    (hfresh : ∀ t, isFreeIn t repl = false)
    (hnomu : ∀ t body, repl ≠ .mu t body) :
    EQ2 (a.substitute var repl) (b.substitute var repl) := by
  apply EQ2_coind_upto (R := SubstRel var repl)
  · intro x y hsr
    obtain ⟨a', b', hab', hbarA', hbarB', hx, hy⟩ := hsr.flatten hfresh hnomu
    subst hx hy
    have hf : EQ2F EQ2 a' b' := EQ2.destruct hab'
    exact SubstRel_postfix_standard var repl a' b' hab' hbarA' hbarB' hfresh hf
  · exact SubstRel.base a b h hbarA hbarB

end SessionCoTypes.SubstCommBarendregt
