import SessionCoTypes.EQ2
import SessionTypes.LocalTypeR

/-! # Barendregt Predicates and Substitution Helpers

Defines `isFreeIn`, `notBoundAt`, and related substitution helper lemmas.
-/

/-
The Problem. Substitution commutation requires the Barendregt convention: bound
variables must be fresh. We need predicates to check free variable occurrence
and binder freshness, plus helpers showing these are preserved by operations.

Solution Structure. Defines `isFreeIn` checking if a variable appears free in a
type, and `notBoundAt` checking if a variable is not used as a binder. Mutual
recursion handles branches. Proves duality preservation and substitution helpers
like `substitute_not_free` (substituting into a term where the variable isn't free).
-/

namespace SessionCoTypes.SubstCommBarendregt

open SessionCoTypes.EQ2
open SessionTypes.GlobalType
open SessionTypes.LocalTypeR

/-! ## Barendregt Predicates -/

mutual
  /-- Check if a variable appears free in a type. -/
  def isFreeIn (v : String) : LocalTypeR → Bool
    | .end => false
    | .var w => v == w
    | .send _ bs => isFreeInBranches v bs
    | .recv _ bs => isFreeInBranches v bs
    | .mu t body => if v == t then false else isFreeIn v body

  /-- Check if a variable appears free in any branch. -/
  def isFreeInBranches (v : String) : List BranchR → Bool
    | [] => false
    | (_, _, cont) :: rest => isFreeIn v cont || isFreeInBranches v rest
end

mutual
  /-- Check that a variable is not used as a binder anywhere. -/
  def notBoundAt (v : String) : LocalTypeR → Bool
    | .end => true
    | .var _ => true
    | .send _ bs => notBoundAtBranches v bs
    | .recv _ bs => notBoundAtBranches v bs
    | .mu t body => (v != t) && notBoundAt v body

  /-- Check notBoundAt for branches. -/
  def notBoundAtBranches (v : String) : List BranchR → Bool
    | [] => true
    | (_, _, cont) :: rest => notBoundAt v cont && notBoundAtBranches v rest
end

/-! ## Duality Preservation for Barendregt Predicates -/

mutual
  /-- isFreeIn is invariant under duality. -/
  theorem isFreeIn_dual (v : String) (t : LocalTypeR) :
      isFreeIn v t.dual = isFreeIn v t := by
    -- Structural recursion; send/recv share the branch case.
    cases t with
    | «end» => rfl
    | var w => rfl
    | send p bs =>
        simp [LocalTypeR.dual, isFreeIn, isFreeInBranches_dual]
    | recv p bs =>
        simp [LocalTypeR.dual, isFreeIn, isFreeInBranches_dual]
    | mu t body =>
        by_cases hv : v == t
        · simp [LocalTypeR.dual, isFreeIn, hv]
        · simp [LocalTypeR.dual, isFreeIn, hv, isFreeIn_dual v body]

  /-- isFreeInBranches is invariant under duality. -/
  theorem isFreeInBranches_dual (v : String) (bs : List BranchR) :
      isFreeInBranches v (dualBranches bs) = isFreeInBranches v bs := by
    -- Recurse over branches, dualizing continuations.
    cases bs with
    | nil => rfl
    | cons head tail =>
        cases head with
        | mk l rest =>
            cases rest with
            | mk vt t =>
                simp [dualBranches, isFreeInBranches, isFreeIn_dual, isFreeInBranches_dual]
end

mutual
  /-- notBoundAt is invariant under duality. -/
  theorem notBoundAt_dual (v : String) (t : LocalTypeR) :
      notBoundAt v t.dual = notBoundAt v t := by
    -- Structural recursion; send/recv share the branch case.
    cases t with
    | «end» => rfl
    | var w => rfl
    | send p bs =>
        simp [LocalTypeR.dual, notBoundAt, notBoundAtBranches_dual]
    | recv p bs =>
        simp [LocalTypeR.dual, notBoundAt, notBoundAtBranches_dual]
    | mu t body =>
        simp [LocalTypeR.dual, notBoundAt, notBoundAt_dual v body]

  /-- notBoundAtBranches is invariant under duality. -/
  theorem notBoundAtBranches_dual (v : String) (bs : List BranchR) :
      notBoundAtBranches v (dualBranches bs) = notBoundAtBranches v bs := by
    -- Recurse over branches; dual does not affect binders.
    cases bs with
    | nil => rfl
    | cons head tail =>
        cases head with
        | mk l rest =>
            cases rest with
            | mk vt t =>
                simp [dualBranches, notBoundAtBranches, notBoundAt_dual, notBoundAtBranches_dual]
end

mutual
  /-- notBoundAt is preserved through substitution when repl also satisfies it. -/
  theorem notBoundAt_subst (v var : String) (a repl : LocalTypeR)
      (hbar : notBoundAt v a = true)
      (hvarRepl : notBoundAt v repl = true) :
      notBoundAt v (a.substitute var repl) = true := by
    cases a with
    | «end» => simp [LocalTypeR.substitute, notBoundAt]
    | var w =>
        simp only [LocalTypeR.substitute]
        by_cases hwvar : w == var
        · simp only [hwvar, ↓reduceIte]; exact hvarRepl
        · simp only [hwvar, Bool.false_eq_true, ↓reduceIte, notBoundAt]
    | send p bs =>
        simp only [LocalTypeR.substitute, notBoundAt]
        exact notBoundAt_subst_branches v var bs repl (by unfold notBoundAt at hbar; exact hbar) hvarRepl
    | recv p bs =>
        simp only [LocalTypeR.substitute, notBoundAt]
        exact notBoundAt_subst_branches v var bs repl (by unfold notBoundAt at hbar; exact hbar) hvarRepl
    | mu t body =>
        simp only [LocalTypeR.substitute]
        by_cases htvar : t == var
        · -- Shadowed: substitution is identity
          simp only [htvar, ↓reduceIte]; exact hbar
        · -- Not shadowed: recurse
          simp only [htvar, Bool.false_eq_true, ↓reduceIte, notBoundAt]
          unfold notBoundAt at hbar
          have ⟨hvt, hbarBody⟩ := Bool.and_eq_true_iff.mp hbar
          exact Bool.and_eq_true_iff.mpr ⟨hvt, notBoundAt_subst v var body repl hbarBody hvarRepl⟩
  termination_by sizeOf a

  /-- notBoundAt for branches is preserved through substitution. -/
  theorem notBoundAt_subst_branches (v var : String) (bs : List BranchR) (repl : LocalTypeR)
      (hbar : notBoundAtBranches v bs = true)
      (hvarRepl : notBoundAt v repl = true) :
      notBoundAtBranches v (SessionTypes.LocalTypeR.substituteBranches bs var repl) = true :=
    match bs, hbar with
    | [], _ => by simp [SessionTypes.LocalTypeR.substituteBranches, notBoundAtBranches]
    | hd :: tl, hbar => by
        simp only [SessionTypes.LocalTypeR.substituteBranches, notBoundAtBranches]
        unfold notBoundAtBranches at hbar
        have ⟨hbarHd, hbarTl⟩ := Bool.and_eq_true_iff.mp hbar
        exact Bool.and_eq_true_iff.mpr ⟨notBoundAt_subst v var hd.2.2 repl hbarHd hvarRepl,
          notBoundAt_subst_branches v var tl repl hbarTl hvarRepl⟩
  termination_by sizeOf bs
  decreasing_by
    all_goals simp_wf
    -- sizeOf hd.2.2 < 1 + sizeOf hd + sizeOf tl = sizeOf (hd :: tl)
    case _ =>
      -- Destructure hd : BranchR = Label × Option ValType × LocalTypeR
      obtain ⟨label, vt, cont⟩ := hd
      exact sizeOf_cont_lt_sizeOf_branches label vt cont tl
    -- 0 < 1 + sizeOf hd is trivial
    case _ => omega
end

/-- notBoundAt is preserved through unfolding. -/
@[simp]
theorem notBoundAt_unfold (v : String) (a : LocalTypeR)
    (hbar : notBoundAt v a = true) :
    notBoundAt v a.unfold = true := by
  cases a with
  | «end» | var _ | send _ _ | recv _ _ =>
      -- Non-mu cases: unfold is identity
      simp only [LocalTypeR.unfold]; exact hbar
  | mu t body =>
      -- unfold (.mu t body) = body.substitute t (.mu t body)
      simp only [LocalTypeR.unfold]
      -- hbar : notBoundAt v (.mu t body) = true
      -- means: (v != t) && notBoundAt v body = true
      unfold notBoundAt at hbar
      have ⟨hvt, hbarBody⟩ := Bool.and_eq_true_iff.mp hbar
      -- Apply notBoundAt_subst: need notBoundAt v body and notBoundAt v (.mu t body)
      apply notBoundAt_subst v t body (.mu t body) hbarBody
      -- Need: notBoundAt v (.mu t body) = true
      unfold notBoundAt
      exact Bool.and_eq_true_iff.mpr ⟨hvt, hbarBody⟩

/-! ## Substitution Helper Lemmas -/

mutual
  /-- If x is not free in e, then substituting for x leaves e unchanged. -/
  theorem substitute_not_free (e : LocalTypeR) (x : String) (rx : LocalTypeR)
      (hnot_free : isFreeIn x e = false) :
      e.substitute x rx = e := by
    cases e with
    | «end» => rfl
    | var w =>
        simp only [LocalTypeR.substitute]
        simp only [isFreeIn] at hnot_free
        have hwx : (w == x) = false := by
          rw [beq_eq_false_iff_ne] at hnot_free ⊢; exact fun h => hnot_free h.symm
        simp only [hwx, Bool.false_eq_true, ↓reduceIte]
    | send p bs =>
        simp only [LocalTypeR.substitute]
        congr 1
        simp only [isFreeIn] at hnot_free
        exact substituteBranches_not_free bs x rx hnot_free
    | recv p bs =>
        simp only [LocalTypeR.substitute]
        congr 1
        simp only [isFreeIn] at hnot_free
        exact substituteBranches_not_free bs x rx hnot_free
    | mu t body =>
        simp only [LocalTypeR.substitute]
        by_cases hxt : t == x
        · simp only [hxt, ↓reduceIte]
        · simp only [hxt, Bool.false_eq_true, ↓reduceIte]
          congr 1
          simp only [isFreeIn] at hnot_free
          have hxt' : (x == t) = false := by
            simp only [beq_eq_false_iff_ne, ne_eq]; exact fun h => hxt (beq_iff_eq.mpr h.symm)
          simp only [hxt', Bool.false_eq_true, ↓reduceIte] at hnot_free
          exact substitute_not_free body x rx hnot_free
  termination_by sizeOf e

  /-- If x is not free in any branch, substituting for x leaves branches unchanged. -/
  theorem substituteBranches_not_free (bs : List BranchR) (x : String) (rx : LocalTypeR)
      (hnot_free : isFreeInBranches x bs = false) :
      SessionTypes.LocalTypeR.substituteBranches bs x rx = bs := by
    match bs with
    | [] => rfl
    | (label, vt, cont) :: rest =>
        simp only [SessionTypes.LocalTypeR.substituteBranches]
        simp only [isFreeInBranches, Bool.or_eq_false_iff] at hnot_free
        have h1 : cont.substitute x rx = cont := substitute_not_free cont x rx hnot_free.1
        have h2 : SessionTypes.LocalTypeR.substituteBranches rest x rx = rest := substituteBranches_not_free rest x rx hnot_free.2
        simp only [h1, h2]
  termination_by sizeOf bs
  decreasing_by
    all_goals simp_wf
    all_goals simp only [sizeOf, List._sizeOf_1, Prod._sizeOf_1]
    all_goals omega
end

/-- Substituting into a closed type leaves it unchanged. -/
@[simp]
theorem substitute_closed (e : LocalTypeR) (x : String) (rx : LocalTypeR)
    (hclosed : ∀ v, isFreeIn v e = false) :
    e.substitute x rx = e :=
  substitute_not_free e x rx (hclosed x)

/-- A variable bound by mu is not free in the mu type. -/
@[simp]
theorem isFreeIn_mu_self (t : String) (body : LocalTypeR) :
    isFreeIn t (.mu t body) = false := by
  simp only [isFreeIn, beq_self_eq_true, ↓reduceIte]

mutual
  /-- If t is not free in repl, then t is not free in (e.substitute t repl).

      Key insight: Every occurrence of t in e gets replaced by repl,
      and t is not free in repl, so t cannot be free in the result. -/
  theorem isFreeIn_subst_self_general (e : LocalTypeR) (t : String) (repl : LocalTypeR)
      (hrepl : isFreeIn t repl = false) :
      isFreeIn t (e.substitute t repl) = false := by
    cases e with
    | «end» =>
        simp only [LocalTypeR.substitute, isFreeIn]
    | var w =>
        simp only [LocalTypeR.substitute]
        by_cases hwt : w == t
        · -- w == t: substitute returns repl
          simp only [hwt, ↓reduceIte]
          exact hrepl
        · -- w != t: substitute returns .var w
          simp only [hwt, Bool.false_eq_true, ↓reduceIte, isFreeIn, beq_eq_false_iff_ne, ne_eq]
          exact fun h => hwt (beq_iff_eq.mpr h.symm)
    | send p bs =>
        simp only [LocalTypeR.substitute, isFreeIn]
        exact isFreeInBranches_subst_self_general bs t repl hrepl
    | recv p bs =>
        simp only [LocalTypeR.substitute, isFreeIn]
        exact isFreeInBranches_subst_self_general bs t repl hrepl
    | mu s inner =>
        simp only [LocalTypeR.substitute]
        by_cases hst : s == t
        · -- s == t: substitution is shadowed, returns .mu s inner
          simp only [hst, ↓reduceIte, isFreeIn]
          simp only [beq_iff_eq] at hst
          simp only [← hst, beq_self_eq_true, ↓reduceIte]
        · -- s != t: returns .mu s (inner.substitute t repl)
          simp only [hst, Bool.false_eq_true, ↓reduceIte, isFreeIn]
          have hts : (t == s) = false := by
            simp only [beq_eq_false_iff_ne, ne_eq]; exact fun h => hst (beq_iff_eq.mpr h.symm)
          simp only [hts, Bool.false_eq_true, ↓reduceIte]
          exact isFreeIn_subst_self_general inner t repl hrepl
  termination_by sizeOf e

  /-- Branch version of isFreeIn_subst_self_general. -/
  theorem isFreeInBranches_subst_self_general (bs : List BranchR) (t : String)
      (repl : LocalTypeR) (hrepl : isFreeIn t repl = false) :
      isFreeInBranches t (SessionTypes.LocalTypeR.substituteBranches bs t repl) = false := by
    match bs with
    | [] => simp only [SessionTypes.LocalTypeR.substituteBranches, isFreeInBranches]
    | (label, _vt, cont) :: rest =>
        simp only [SessionTypes.LocalTypeR.substituteBranches, isFreeInBranches, Bool.or_eq_false_iff]
        exact ⟨isFreeIn_subst_self_general cont t repl hrepl,
               isFreeInBranches_subst_self_general rest t repl hrepl⟩
  termination_by sizeOf bs
  decreasing_by
    all_goals simp_wf
    all_goals simp only [sizeOf, List._sizeOf_1, Prod._sizeOf_1]
    all_goals omega
end

/-- After substituting t with (mu t body), the variable t is not free.

    This is a special case of isFreeIn_subst_self_general where repl = .mu t body. -/
@[simp]
theorem isFreeIn_subst_mu_self (body : LocalTypeR) (t : String) :
    isFreeIn t (body.substitute t (.mu t body)) = false :=
  isFreeIn_subst_self_general body t (.mu t body) (isFreeIn_mu_self t body)

mutual
  /-- If v is not free in e and not free in repl, then v is not free in e.substitute t repl.

      The intuition is: substitution only replaces occurrences of t with repl.
      - Original occurrences of v in e: still there unless v = t (but then v not free in e means none)
      - New occurrences: only from repl copies, but v not free in repl

      This handles the case v ≠ t (v not being the substituted variable). -/
  theorem isFreeIn_subst_preserves (e : LocalTypeR) (v t : String) (repl : LocalTypeR)
      (hv_e : isFreeIn v e = false) (hv_repl : isFreeIn v repl = false) :
      isFreeIn v (e.substitute t repl) = false := by
    cases e with
    | «end» => simp only [LocalTypeR.substitute, isFreeIn]
    | var w =>
        simp only [LocalTypeR.substitute]
        by_cases hwt : w == t
        · -- w == t: substitute returns repl, v not free in repl
          simp only [hwt, ↓reduceIte]
          exact hv_repl
        · -- w != t: substitute returns .var w, v not free in .var w (since v not free in e)
          simp only [hwt, Bool.false_eq_true, ↓reduceIte]
          exact hv_e
    | send p bs =>
        simp only [LocalTypeR.substitute, isFreeIn]
        simp only [isFreeIn] at hv_e
        exact isFreeInBranches_subst_preserves bs v t repl hv_e hv_repl
    | recv p bs =>
        simp only [LocalTypeR.substitute, isFreeIn]
        simp only [isFreeIn] at hv_e
        exact isFreeInBranches_subst_preserves bs v t repl hv_e hv_repl
    | mu s body =>
        simp only [LocalTypeR.substitute]
        by_cases hst : s == t
        · -- s == t: substitution is shadowed
          simp only [hst, ↓reduceIte]
          exact hv_e
        · -- s != t: recurse
          simp only [hst, Bool.false_eq_true, ↓reduceIte, isFreeIn]
          simp only [isFreeIn] at hv_e
          by_cases hvs : v == s
          · -- v == s: v is bound by mu, so not free
            simp only [hvs, ↓reduceIte]
          · -- v != s
            simp only [hvs, Bool.false_eq_true, ↓reduceIte] at hv_e ⊢
            exact isFreeIn_subst_preserves body v t repl hv_e hv_repl
  termination_by sizeOf e

  /-- Branch version of isFreeIn_subst_preserves. -/
  theorem isFreeInBranches_subst_preserves (bs : List BranchR) (v t : String)
      (repl : LocalTypeR)
      (hv_bs : isFreeInBranches v bs = false) (hv_repl : isFreeIn v repl = false) :
      isFreeInBranches v (SessionTypes.LocalTypeR.substituteBranches bs t repl) = false := by
    match bs with
    | [] => simp only [SessionTypes.LocalTypeR.substituteBranches, isFreeInBranches]
    | (label, _vt, cont) :: rest =>
        simp only [SessionTypes.LocalTypeR.substituteBranches, isFreeInBranches, Bool.or_eq_false_iff]
        simp only [isFreeInBranches, Bool.or_eq_false_iff] at hv_bs
        exact ⟨isFreeIn_subst_preserves cont v t repl hv_bs.1 hv_repl,
               isFreeInBranches_subst_preserves rest v t repl hv_bs.2 hv_repl⟩
  termination_by sizeOf bs
  decreasing_by
    all_goals simp_wf
    all_goals simp only [sizeOf, List._sizeOf_1, Prod._sizeOf_1]
    all_goals omega
end

/-- Key helper: (mu t body).substitute var repl = mu t (body.substitute var repl) when t ≠ var. -/
@[simp]
theorem mu_subst_ne (t : String) (body : LocalTypeR) (var : String) (repl : LocalTypeR)
    (htne : t ≠ var) :
    (LocalTypeR.mu t body).substitute var repl = .mu t (body.substitute var repl) := by
  simp only [LocalTypeR.substitute]
  simp only [beq_eq_false_iff_ne.mpr htne, Bool.false_eq_true, ↓reduceIte]

end SessionCoTypes.SubstCommBarendregt
