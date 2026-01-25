import RumpsteakV2.Protocol.LocalTypeR
import RumpsteakV2.Protocol.CoTypes.EQ2

/-! # RumpsteakV2.Protocol.CoTypes.DBBridge

Bridge lemmas for EQ2 substitution commutation. The original DB-backed
assumption is now proven using closedness of well-formed mu types.
-/

namespace RumpsteakV2.Protocol.CoTypes

open RumpsteakV2.Protocol.LocalTypeR
open RumpsteakV2.Protocol.CoTypes.EQ2

theorem EQ2_subst_mu_comm_via_DB (body : LocalTypeR) (var t : String) (repl : LocalTypeR)
    (htne : t ≠ var) (hWFmu : LocalTypeR.WellFormed (.mu t body)) :
    EQ2 ((body.substitute var repl).substitute t (.mu t (body.substitute var repl)))
        ((body.substitute t (.mu t body)).substitute var repl) := by
  -- Closed mu types have no free vars except the binder.
  have hclosed : (LocalTypeR.mu t body).isClosed := hWFmu.closed
  have hnotfree_mu : LocalTypeR.isFreeIn var (.mu t body) = false :=
    LocalTypeR.isFreeIn_false_of_closed (.mu t body) var hclosed
  have hvne : var ≠ t := htne.symm
  have hbeq : (var == t) = false := beq_eq_false_iff_ne.mpr hvne
  have hnotfree_body : LocalTypeR.isFreeIn var body = false := by
    simpa [LocalTypeR.isFreeIn, hbeq] using hnotfree_mu
  have hsubst_body : body.substitute var repl = body :=
    LocalTypeR.substitute_not_free body var repl hnotfree_body
  have hclosed_unfold : (body.substitute t (.mu t body)).isClosed :=
    LocalTypeR.isClosed_substitute_mu (t := t) (body := body) hclosed
  have hnotfree_unfold : LocalTypeR.isFreeIn var (body.substitute t (.mu t body)) = false :=
    LocalTypeR.isFreeIn_false_of_closed (body.substitute t (.mu t body)) var hclosed_unfold
  have hsubst_rhs : (body.substitute t (.mu t body)).substitute var repl =
      (body.substitute t (.mu t body)) :=
    LocalTypeR.substitute_not_free (body.substitute t (.mu t body)) var repl hnotfree_unfold
  have hEq :
      (body.substitute var repl).substitute t (.mu t (body.substitute var repl)) =
      (body.substitute t (.mu t body)).substitute var repl := by
    calc
      (body.substitute var repl).substitute t (.mu t (body.substitute var repl)) =
          (body.substitute t (.mu t body)) := by
        simp [hsubst_body]
      _ = (body.substitute t (.mu t body)).substitute var repl := by
        symm
        exact hsubst_rhs
  -- Equality gives EQ2 by reflexivity.
  simpa [hEq] using
    (EQ2_refl ((body.substitute t (.mu t body)).substitute var repl))

end RumpsteakV2.Protocol.CoTypes
