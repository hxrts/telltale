import RumpsteakV2.Protocol.CoTypes.Bisim.Part7

/-! # Bisim Part 8: Congruence Framework and Substitution Compatibility

Proves duality is compatible and establishes substitution compatibility under Barendregt conditions.
-/

set_option linter.dupNamespace false
set_option linter.unnecessarySimpa false

namespace RumpsteakV2.Protocol.CoTypes.Bisim
open RumpsteakV2.Protocol.LocalTypeR
open RumpsteakV2.Protocol.GlobalType
open RumpsteakV2.Protocol.CoTypes.Observable
open RumpsteakV2.Protocol.CoTypes.EQ2
open RumpsteakV2.Protocol.CoTypes.CoinductiveRel
/-! ## Phase 4: Congruence Framework

This section provides the infrastructure for proving that Bisim (and hence EQ2)
is a congruence for various operations like substitution. The key idea is to
define "compatible" functions and show that compatible functions preserve Bisim.

Following the pattern from QpfTypes PR #49. -/

/-- RelImage lifts a relation through a function application.

    `RelImage f R u v` holds when there exist `a b` such that `R a b` and
    `u = f a` and `v = f b`. This is the image of R under f × f. -/
def RelImage (f : LocalTypeR → LocalTypeR) (R : Rel) : Rel :=
  fun u v => ∃ a b, R a b ∧ u = f a ∧ v = f b

/-- A function is compatible if it preserves BisimF structure.

    `Compatible f` means: if `BisimF R x y` holds, then
    `BisimF (RelImage f R) (f x) (f y)` holds.

    This is the key property that allows lifting Bisim through f. -/
def Compatible (f : LocalTypeR → LocalTypeR) : Prop :=
  ∀ {R : Rel} {x y : LocalTypeR}, BisimF R x y → BisimF (RelImage f R) (f x) (f y)

/-- BranchesRelBisim under RelImage. -/
theorem BranchesRelBisim.map_image {f : LocalTypeR → LocalTypeR} {R : Rel}
    {bs cs : List (Label × LocalTypeR)} (h : BranchesRelBisim R bs cs) :
    BranchesRelBisim (RelImage f R)
      (bs.map (fun b => (b.1, f b.2)))
      (cs.map (fun c => (c.1, f c.2))) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hbc _ ih =>
    apply List.Forall₂.cons
    · constructor
      · exact hbc.1
      · exact ⟨_, _, hbc.2, rfl, rfl⟩
    · exact ih

/-- Compatible functions are congruences for Bisim.

    If f is compatible, then Bisim x y implies Bisim (f x) (f y).
    This is the main theorem that enables proving EQ2_substitute via Bisim. -/
theorem Bisim.congr (f : LocalTypeR → LocalTypeR) (hf : Compatible f)
    {x y : LocalTypeR} (h : Bisim x y) : Bisim (f x) (f y) := by
  obtain ⟨R, hRpost, hxy⟩ := h
  -- Use RelImage f R as the witness relation
  let Rf := RelImage f R
  use Rf
  constructor
  · -- Show Rf is a post-fixpoint of BisimF
    intro u v ⟨a, b, hab, hu, hv⟩
    have hf_ab := hRpost a b hab
    rw [hu, hv]
    exact hf hf_ab
  · -- Show Rf (f x) (f y)
    exact ⟨x, y, hxy, rfl, rfl⟩

/-- Duality is compatible with BisimF. -/
theorem dual_compatible : Compatible LocalTypeR.dual := by
  intro R x y h
  cases h with
  | eq_end hx hy =>
      exact BisimF.eq_end (UnfoldsToEnd.dual hx) (UnfoldsToEnd.dual hy)
  | eq_var hx hy =>
      exact BisimF.eq_var (UnfoldsToVar.dual hx) (UnfoldsToVar.dual hy)
  | eq_send hx hy hbr =>
      rename_i p bsa bsb
      have hx' : CanRecv x.dual p (LocalTypeR.dualBranches bsa) := CanSend.dual hx
      have hy' : CanRecv y.dual p (LocalTypeR.dualBranches bsb) := CanSend.dual hy
      have hbr' : BranchesRelBisim (RelImage LocalTypeR.dual R)
          (LocalTypeR.dualBranches bsa) (LocalTypeR.dualBranches bsb) := by
        simpa [LocalTypeR.dualBranches_eq_map] using
          (BranchesRelBisim.map_image (f := LocalTypeR.dual) hbr)
      exact BisimF.eq_recv hx' hy' hbr'
  | eq_recv hx hy hbr =>
      rename_i p bsa bsb
      have hx' : CanSend x.dual p (LocalTypeR.dualBranches bsa) := CanRecv.dual hx
      have hy' : CanSend y.dual p (LocalTypeR.dualBranches bsb) := CanRecv.dual hy
      have hbr' : BranchesRelBisim (RelImage LocalTypeR.dual R)
          (LocalTypeR.dualBranches bsa) (LocalTypeR.dualBranches bsb) := by
        simpa [LocalTypeR.dualBranches_eq_map] using
          (BranchesRelBisim.map_image (f := LocalTypeR.dual) hbr)
      exact BisimF.eq_send hx' hy' hbr'



/-! ### Substitute Compatibility

To prove `EQ2_substitute` we need to show that substitution is compatible.
This requires showing that substitution preserves observable behavior. -/

open RumpsteakV2.Protocol.CoTypes.SubstCommBarendregt in
/-- After substituting `t → .mu t body`, the variable `t` is no longer free.

    This is because `.mu t body` binds `t`, so any free occurrence of `t` in the
    original type gets replaced by something where `t` is bound.

    Proven in SubstCommBarendregt.lean using the more general isFreeIn_subst_self_general. -/
theorem isFreeIn_mu_unfold_false (body : LocalTypeR) (t : String) :
    isFreeIn t (body.substitute t (.mu t body)) = false :=
  isFreeIn_subst_mu_self body t

open RumpsteakV2.Protocol.CoTypes.SubstCommBarendregt in
/-- If a variable is not free in a type, substituting for it is the identity on branches.

    This is used for the shadowed case in substitute_preserves_CanSend/CanRecv. -/
theorem map_substitute_eq_self_of_not_free {bs : List (Label × LocalTypeR)} {var : String} {repl : LocalTypeR}
    (hnot_free : ∀ (l : Label) (c : LocalTypeR), (l, c) ∈ bs → isFreeIn var c = false) :
    bs.map (fun b => (b.1, b.2.substitute var repl)) = bs := by
  induction bs with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons]
    obtain ⟨l, c⟩ := hd
    have hnot_free_c : isFreeIn var c = false := hnot_free l c (List.Mem.head _)
    have hc_eq : c.substitute var repl = c := substitute_not_free c var repl hnot_free_c
    have htl_eq := ih (fun l' c' hmem => hnot_free l' c' (List.Mem.tail _ hmem))
    simp only [hc_eq, htl_eq]

/-! ### Substitution Commutativity (EQ2 version)

The syntactic `subst_mu_comm` requires Barendregt conditions. For general use,
we need an EQ2-equivalence version that holds unconditionally.

## Proof Strategy

We rely on the fact that well-formed mu types are closed, so substituting a
distinct variable is a no-op. This yields the EQ2 commutation without the
Barendregt conditions or a fragile coinduction-up-to argument.
-/

/-- EQ2 version of mu-substitution commutativity.

    States that the order of two substitutions (var→repl and t→mu t body) can be
    swapped up to EQ2 equivalence, as long as t ≠ var and the mu type is well-formed
    (closed), so the var-substitution is a no-op.

    When Barendregt conditions hold (notBoundAt var body, repl is closed), this
    follows from syntactic `subst_mu_comm`. For well-formed mu types (closed),
    the `var` substitution is a no-op, so both sides are definitionally equal.

    Proof: closed mu types make the `var` substitution a no-op, so both sides
    are definitionally equal; use EQ2_refl (see `CoTypes.DBBridge`). -/
theorem EQ2_subst_mu_comm (body : LocalTypeR) (var t : String) (repl : LocalTypeR)
    (htne : t ≠ var) (hWFmu : LocalTypeR.WellFormed (.mu t body)) :
    EQ2 ((body.substitute var repl).substitute t (.mu t (body.substitute var repl)))
        ((body.substitute t (.mu t body)).substitute var repl) := by
  exact RumpsteakV2.Protocol.CoTypes.EQ2_subst_mu_comm_via_DB body var t repl htne hWFmu

/-- Transfer UnfoldsToEnd through EQ2 equivalence.

    If `a` unfolds to end and `a` is EQ2-equivalent to `b`, then `b` unfolds to end. -/
theorem UnfoldsToEnd_of_EQ2 {a b : LocalTypeR} (ha : UnfoldsToEnd a) (heq : EQ2 a b)
    (hWFb : LocalTypeR.WellFormed b) : UnfoldsToEnd b := by
  exact UnfoldsToEnd_transfer ha heq hWFb

/-- Substitution preserves UnfoldsToEnd.

    If a unfolds to end, then (a.substitute var repl) also unfolds to end
    (or to something EQ2-equivalent, when var is substituted).

    Proof: By induction on the UnfoldsToEnd proof.
    - Base case (a = .end): substitution gives .end, which has UnfoldsToEnd.
    - Mu case (a = .mu t body): Two subcases:
      - If t == var: substitution is shadowed, result is .mu t body, same as h.
      - If t != var: use subst_mu_comm (but this requires Barendregt conditions).

    Note: The full proof requires Barendregt conditions. We prove the simplified
    version that handles the base case and the shadowed mu case. The non-shadowed
    mu case requires substitution commutation which needs additional assumptions. -/
theorem substitute_preserves_UnfoldsToEnd {a : LocalTypeR} {var : String} {repl : LocalTypeR}
    (h : UnfoldsToEnd a) (hWFa : LocalTypeR.WellFormed a)
    (hWFrepl : LocalTypeR.WellFormed repl) :
    UnfoldsToEnd (a.substitute var repl) ∨
      ∃ n, UnfoldPathEndBounded n repl ∧ a = .var var := by
  refine (UnfoldsToEnd.rec
    (motive := fun a _ =>
      ∀ {repl}, LocalTypeR.WellFormed a → LocalTypeR.WellFormed repl →
        UnfoldsToEnd (a.substitute var repl) ∨
          ∃ n, UnfoldPathEndBounded n repl ∧ a = .var var)
    ?base ?mu h) hWFa hWFrepl
  · intro repl hWFa hWFrepl
    -- a = .end, substitute gives .end
    left
    simp only [LocalTypeR.substitute]
    exact UnfoldsToEnd.base
  · intro t body hinner ih repl hWFa hWFrepl
    -- For closed types, substitution is identity since no variable is free.
    -- hWFa : WellFormed (.mu t body) implies .mu t body is closed.
    left
    have hclosed : (LocalTypeR.mu t body).isClosed := hWFa.closed
    have hnotfree : LocalTypeR.isFreeIn var (.mu t body) = false :=
      LocalTypeR.isFreeIn_false_of_closed (.mu t body) var hclosed
    have hsubst : (LocalTypeR.mu t body).substitute var repl = .mu t body :=
      LocalTypeR.substitute_not_free (.mu t body) var repl hnotfree
    rw [hsubst]
    exact UnfoldsToEnd.mu hinner

open RumpsteakV2.Protocol.CoTypes.SubstCommBarendregt in
/-- Substitution preserves UnfoldsToEnd under Barendregt conditions.

    This version requires Barendregt conditions:
    - `hbar`: var is not used as a binder in a
    - `hfresh`: repl is closed (no free variables)

    These conditions ensure substitution commutativity in the mu case. -/
theorem substitute_preserves_UnfoldsToEnd_barendregt {a : LocalTypeR} {var : String} {repl : LocalTypeR}
    (h : UnfoldsToEnd a)
    (hbar : notBoundAt var a = true)
    (hfresh : ∀ w, isFreeIn w repl = false) :
    UnfoldsToEnd (a.substitute var repl) := by
  refine (UnfoldsToEnd.rec
    (motive := fun a _ =>
      ∀ {var repl}, notBoundAt var a = true →
        (∀ w, isFreeIn w repl = false) →
          UnfoldsToEnd (a.substitute var repl))
    ?base ?mu h) hbar hfresh
  · intro var repl hbar hfresh
    -- a = .end, substitute gives .end
    simp only [LocalTypeR.substitute]
    exact UnfoldsToEnd.base
  · intro t body hinner ih var repl hbar hfresh
    -- a = .mu t body
    -- notBoundAt var (.mu t body) = (var != t) && notBoundAt var body = true
    simp only [notBoundAt] at hbar
    have ⟨hvt, hbar_body⟩ := Bool.and_eq_true_iff.mp hbar
    have hvt' : var ≠ t := by simp only [bne_iff_ne, ne_eq] at hvt; exact hvt
    have htv' : t ≠ var := hvt'.symm
    -- Since var ≠ t, substitution goes through
    have htvar : (t == var) = false := by
      cases h : t == var
      · rfl
      · simp only [beq_iff_eq] at h; exact absurd h htv'
    simp only [LocalTypeR.substitute, htvar, Bool.false_eq_true, ↓reduceIte]
    -- Goal: UnfoldsToEnd (.mu t (body.substitute var repl))
    apply UnfoldsToEnd.mu
    -- Use subst_mu_comm to rewrite the goal
    have hcomm := subst_mu_comm body var t repl hbar_body hfresh htv'
    rw [hcomm]
    -- Now goal: UnfoldsToEnd ((body.substitute t (.mu t body)).substitute var repl)
    have hbar_unfold : notBoundAt var (body.substitute t (.mu t body)) = true :=
      notBoundAt_unfold var (.mu t body) (by simp [notBoundAt, hvt, hbar_body])
    exact ih hbar_unfold hfresh

open RumpsteakV2.Protocol.CoTypes.SubstCommBarendregt in
/-- Substitution preserves UnfoldsToVar (when not the substituted variable).

    This version requires Barendregt conditions:
    - `hbar`: var is not used as a binder in a
    - `hfresh`: repl is closed (no free variables)

    These conditions ensure substitution commutativity in the mu case. -/
theorem substitute_preserves_UnfoldsToVar {a : LocalTypeR} {var v : String} {repl : LocalTypeR}
    (h : UnfoldsToVar a v) (hne : v ≠ var)
    (hbar : notBoundAt var a = true)
    (hfresh : ∀ w, isFreeIn w repl = false) :
    UnfoldsToVar (a.substitute var repl) v := by
  refine (UnfoldsToVar.rec
    (motive := fun a v _ =>
      ∀ {var repl}, v ≠ var → notBoundAt var a = true →
        (∀ w, isFreeIn w repl = false) →
          UnfoldsToVar (a.substitute var repl) v)
    ?base ?mu h) hne hbar hfresh
  · intro v var repl hne hbar hfresh
    -- UnfoldsToVar (.var v) v means a = .var v
    simp only [LocalTypeR.substitute]
    split
    · rename_i hveq
      simp only [beq_iff_eq] at hveq
      exact absurd hveq hne
    · exact UnfoldsToVar.base
  · intro t body v h ih var repl hne hbar hfresh
    simp only [LocalTypeR.substitute]
    split
    · -- t == var is true: substitution is shadowed
      rename_i htvar
      simp only [beq_iff_eq] at htvar
      have hnotfree : isFreeIn t (body.substitute t (.mu t body)) = false :=
        isFreeIn_mu_unfold_false body t
      have hnotfree' : isFreeIn var (body.substitute t (.mu t body)) = false := by
        rw [← htvar]; exact hnotfree
      have hsame : (body.substitute t (.mu t body)).substitute var repl =
                   body.substitute t (.mu t body) :=
        substitute_not_free _ var repl hnotfree'
      -- Get notBoundAt for the unfolded body
      have hbar_unfold : notBoundAt var (body.substitute t (.mu t body)) = true :=
        notBoundAt_unfold var (.mu t body) hbar
      have ih' := ih hne hbar_unfold hfresh
      rw [hsame] at ih'
      exact UnfoldsToVar.mu ih'
    · -- t == var is false: substitution goes through
      rename_i htvar
      simp only [beq_iff_eq] at htvar
      -- Extract notBoundAt for body from hbar
      simp only [notBoundAt] at hbar
      have htne : t ≠ var := fun heq => by simp [heq] at htvar
      have hbne : (var != t) = true := bne_iff_ne.mpr htne.symm
      simp only [hbne, Bool.true_and] at hbar
      -- Use subst_mu_comm for commutativity
      have hcomm := subst_mu_comm body var t repl hbar hfresh htne
      -- Get notBoundAt for the unfolded body
      have hbar_unfold : notBoundAt var (body.substitute t (.mu t body)) = true :=
        notBoundAt_unfold var (.mu t body) (by simp [notBoundAt, hbne, hbar])
      have ih' := ih hne hbar_unfold hfresh
      rw [← hcomm] at ih'
      exact UnfoldsToVar.mu ih'

open RumpsteakV2.Protocol.CoTypes.SubstCommBarendregt in
/-- If a variable is not free in a type, the type cannot unfold to that variable.

    The proof is by induction on `UnfoldsToVar`:
    - Base case `.var v`: `isFreeIn v (.var v) = true`, contradicts hypothesis.
    - Mu case `.mu t body`: The induction hypothesis gives us that
      `isFreeIn v (body.substitute t (.mu t body)) = false` implies
      `¬UnfoldsToVar (body.substitute t (.mu t body)) v`, which contradicts the premise.

    This lemma is key for proving that the `t = var` case in `UnfoldsToVar_substitute_EQ2`
    is impossible: by `isFreeIn_subst_mu_self`, the bound variable is not free after unfolding,
    so `UnfoldsToVar (body.substitute t (.mu t body)) t` cannot hold. -/
theorem not_UnfoldsToVar_of_not_isFreeIn {x : LocalTypeR} {v : String}
    (h : isFreeIn v x = false) : ¬UnfoldsToVar x v := by
  intro hunf
  refine UnfoldsToVar.rec (motive := fun x v _ => isFreeIn v x = false → False) ?base ?mu hunf h
  · intro v h
    -- x = .var v, but isFreeIn v (.var v) = (v == v) = true, contradicting h
    simp only [isFreeIn, beq_self_eq_true] at h
    cases h
  · intro t body v hinner ih h
    -- x = .mu t body, with UnfoldsToVar (body.substitute t (.mu t body)) v
    -- h : isFreeIn v (.mu t body) = false
    -- ih : isFreeIn v (body.substitute t (.mu t body)) = false → False
    -- We need to show isFreeIn v (body.substitute t (.mu t body)) = false
    simp only [isFreeIn] at h
    by_cases hvt : v == t
    · -- v == t case: use isFreeIn_subst_mu_self
      simp only [beq_iff_eq] at hvt
      subst hvt
      have hnotfree := isFreeIn_subst_mu_self body v
      exact ih hnotfree
    · -- v ≠ t case: isFreeIn v (.mu t body) = isFreeIn v body = false
      simp only [hvt, Bool.false_eq_true, ↓reduceIte] at h
      -- h : isFreeIn v body = false
      -- Need: isFreeIn v (body.substitute t (.mu t body)) = false
      have hmu_notfree : isFreeIn v (.mu t body) = false := by
        simp only [isFreeIn, hvt, Bool.false_eq_true, ↓reduceIte, h]
      -- By isFreeIn_subst_preserves: v not free in body ∧ v not free in repl → v not free in result
      have hsubst_notfree := isFreeIn_subst_preserves body v t (.mu t body) h hmu_notfree
      exact ih hsubst_notfree

end RumpsteakV2.Protocol.CoTypes.Bisim
