import Mathlib
import RumpsteakV2.Coinductive.LocalTypeC
import RumpsteakV2.Protocol.LocalTypeR

set_option linter.dupNamespace false

/-
The Problem. We have two representations of local types: the inductive
LocalTypeR (finite, pattern-matchable) and the coinductive LocalTypeC
(potentially infinite, M-type). We need to embed inductive types into
the coinductive world for equivalence proofs and bisimulation.

Solution Structure. Define a recursive embedding `toCoind : LocalTypeR → LocalTypeC`
that maps each inductive constructor to its smart constructor counterpart.
Prove simp lemmas for each constructor case.
-/

namespace RumpsteakV2.Coinductive

open RumpsteakV2.Protocol.GlobalType
open RumpsteakV2.Protocol.LocalTypeR

/-! ## Embedding -/

mutual
  /-- Embed an inductive local type into the coinductive representation.
      This is a structure-preserving map: end → mkEnd, var → mkVar, etc. -/
  def toCoind : LocalTypeR → LocalTypeC
    | .end       => mkEnd
    | .var x     => mkVar x
    | .mu x body => mkMu x (toCoind body)
    | .send p bs => mkSend p (toCoindBranches bs)
    | .recv p bs => mkRecv p (toCoindBranches bs)

  /-- Embed a list of branches, converting each continuation. -/
  def toCoindBranches : List (Label × LocalTypeR) → List (Label × LocalTypeC)
    | []             => []
    | (lb, t) :: rest => (lb, toCoind t) :: toCoindBranches rest
end

/-! ## Simp Lemmas -/

@[simp] theorem toCoind_end : toCoind .end = mkEnd := rfl
@[simp] theorem toCoind_var (x : String) : toCoind (.var x) = mkVar x := rfl
@[simp] theorem toCoind_mu (x : String) (body : LocalTypeR) :
    toCoind (.mu x body) = mkMu x (toCoind body) := rfl
@[simp] theorem toCoind_send (p : String) (bs : List (Label × LocalTypeR)) :
    toCoind (.send p bs) = mkSend p (toCoindBranches bs) := rfl
@[simp] theorem toCoind_recv (p : String) (bs : List (Label × LocalTypeR)) :
    toCoind (.recv p bs) = mkRecv p (toCoindBranches bs) := rfl

end RumpsteakV2.Coinductive
