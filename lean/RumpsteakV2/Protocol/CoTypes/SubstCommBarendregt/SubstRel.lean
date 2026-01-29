import RumpsteakV2.Protocol.CoTypes.SubstCommBarendregt.General

/-! # SubstRel and Helper Lemmas

Defines the `SubstRel` inductive relation for substitution congruence proofs.
-/

namespace RumpsteakV2.Protocol.CoTypes.SubstCommBarendregt
open RumpsteakV2.Protocol.LocalTypeR
open RumpsteakV2.Protocol.CoTypes.EQ2
open RumpsteakV2.Protocol.GlobalType
/-! ## Inductive SubstRel -/

/-- Relation for substitution congruence, closed under unfolding. -/
inductive SubstRel (var : String) (repl : LocalTypeR) : Rel where
  | base (a b : LocalTypeR) (hab : EQ2 a b)
      (hbarA : notBoundAt var a = true) (hbarB : notBoundAt var b = true) :
      SubstRel var repl (a.substitute var repl) (b.substitute var repl)
  | unfold_left {x y : LocalTypeR} :
      SubstRel var repl x y → SubstRel var repl x.unfold y
  | unfold_right {x y : LocalTypeR} :
      SubstRel var repl x y → SubstRel var repl x y.unfold

/-! ## The Flatten Lemma -/

/-- Flatten pushes unfolds into the EQ2 witnesses.

    Requires `hnomu : ∀ t body, repl ≠ .mu t body` (repl is not a mu type at top level).
    This is needed for the unfold_subst_eq_subst_unfold lemma when the witness is a var
    that matches the substitution variable. -/
theorem SubstRel.flatten {var : String} {repl : LocalTypeR}
    (hfresh : ∀ t, isFreeIn t repl = false)
    (hnomu : ∀ t body, repl ≠ .mu t body)
    {x y : LocalTypeR} (h : SubstRel var repl x y) :
    ∃ a b, EQ2 a b ∧
           notBoundAt var a = true ∧ notBoundAt var b = true ∧
           x = a.substitute var repl ∧ y = b.substitute var repl := by
  induction h with
  | base a b hab hbarA hbarB =>
    exact ⟨a, b, hab, hbarA, hbarB, rfl, rfl⟩
  | unfold_left _ ih =>
    obtain ⟨a, b, hab, hbarA, hbarB, hx, hy⟩ := ih
    use a.unfold, b
    refine ⟨EQ2_unfold_left hab, notBoundAt_unfold var a hbarA, hbarB, ?_, hy⟩
    rw [hx]
    exact unfold_subst_eq_subst_unfold a var repl hbarA hfresh hnomu
  | unfold_right _ ih =>
    obtain ⟨a, b, hab, hbarA, hbarB, hx, hy⟩ := ih
    use a, b.unfold
    refine ⟨EQ2_unfold_right hab, hbarA, notBoundAt_unfold var b hbarB, hx, ?_⟩
    rw [hy]
    exact unfold_subst_eq_subst_unfold b var repl hbarB hfresh hnomu

/-! ## Helper Lemmas for Substitution -/

/-- Substitute on mu when bound variable differs from substitution variable. -/
@[simp]
theorem mu_substitute_ne (t : String) (body : LocalTypeR) (var : String) (repl : LocalTypeR)
    (hne : (t == var) = false) :
    (LocalTypeR.mu t body).substitute var repl = .mu t (body.substitute var repl) := by
  simp only [LocalTypeR.substitute, hne, Bool.false_eq_true, ite_false]

/-- Substitute on var when variable equals substitution variable. -/
@[simp]
theorem var_substitute_eq (v : String) (var : String) (repl : LocalTypeR)
    (heq : (v == var) = true) :
    (LocalTypeR.var v).substitute var repl = repl := by
  simp only [LocalTypeR.substitute, heq, ite_true]

/-- Substitute on var when variable differs from substitution variable. -/
@[simp]
theorem var_substitute_ne (v : String) (var : String) (repl : LocalTypeR)
    (hne : (v == var) = false) :
    (LocalTypeR.var v).substitute var repl = .var v := by
  simp only [LocalTypeR.substitute, hne, Bool.false_eq_true, ite_false]

/-! ## EQ2F Reduction Lemmas -/

/-- EQ2F reduction for mu-end case. -/
@[simp] theorem EQ2F_mu_end (R : Rel) (t : String) (body : LocalTypeR) :
    EQ2F R (.mu t body) .end = R (body.substitute t (.mu t body)) .end := rfl

/-- EQ2F reduction for mu-var case. -/
@[simp] theorem EQ2F_mu_var (R : Rel) (t : String) (body : LocalTypeR) (v : String) :
    EQ2F R (.mu t body) (.var v) = R (body.substitute t (.mu t body)) (.var v) := rfl

/-- EQ2F reduction for mu-send case. -/
@[simp] theorem EQ2F_mu_send (R : Rel) (t : String) (body : LocalTypeR) (p : String)
    (bs : List (Label × LocalTypeR)) :
    EQ2F R (.mu t body) (.send p bs) = R (body.substitute t (.mu t body)) (.send p bs) := rfl

/-- EQ2F reduction for mu-recv case. -/
@[simp] theorem EQ2F_mu_recv (R : Rel) (t : String) (body : LocalTypeR) (p : String)
    (bs : List (Label × LocalTypeR)) :
    EQ2F R (.mu t body) (.recv p bs) = R (body.substitute t (.mu t body)) (.recv p bs) := rfl

/-- EQ2F reduction for end-mu case. -/
@[simp] theorem EQ2F_end_mu (R : Rel) (s : String) (body' : LocalTypeR) :
    EQ2F R .end (.mu s body') = R .end (body'.substitute s (.mu s body')) := rfl

/-- EQ2F reduction for var-mu case. -/
@[simp] theorem EQ2F_var_mu (R : Rel) (v : String) (s : String) (body' : LocalTypeR) :
    EQ2F R (.var v) (.mu s body') = R (.var v) (body'.substitute s (.mu s body')) := rfl

/-- EQ2F reduction for send-mu case. -/
@[simp] theorem EQ2F_send_mu (R : Rel) (p : String) (bs : List (Label × LocalTypeR))
    (s : String) (body' : LocalTypeR) :
    EQ2F R (.send p bs) (.mu s body') = R (.send p bs) (body'.substitute s (.mu s body')) := rfl

/-- EQ2F reduction for recv-mu case. -/
@[simp] theorem EQ2F_recv_mu (R : Rel) (p : String) (bs : List (Label × LocalTypeR))
    (s : String) (body' : LocalTypeR) :
    EQ2F R (.recv p bs) (.mu s body') = R (.recv p bs) (body'.substitute s (.mu s body')) := rfl

end RumpsteakV2.Protocol.CoTypes.SubstCommBarendregt
