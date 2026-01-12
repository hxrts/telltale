import Mathlib
import RumpsteakV2.Coinductive.LocalTypeC
import RumpsteakV2.Protocol.LocalTypeR

set_option linter.dupNamespace false

/-!
# Bridges between LocalTypeR and LocalTypeC

Defines the embedding `toCoind` from inductive local types to the coinductive
representation.
-/

namespace RumpsteakV2.Coinductive

open RumpsteakV2.Protocol.GlobalType
open RumpsteakV2.Protocol.LocalTypeR

mutual
  /-- Embed inductive local types into the coinductive representation. -/
  def toCoind : LocalTypeR → LocalTypeC
    | .end => mkEnd
    | .var x => mkVar x
    | .mu x body => mkMu x (toCoind body)
    | .send p bs => mkSend p (toCoindBranches bs)
    | .recv p bs => mkRecv p (toCoindBranches bs)

  def toCoindBranches : List (Label × LocalTypeR) → List (Label × LocalTypeC)
    | [] => []
    | (lb, t) :: rest => (lb, toCoind t) :: toCoindBranches rest
end

@[simp] theorem toCoind_end : toCoind .end = mkEnd := rfl
@[simp] theorem toCoind_var (x : String) : toCoind (.var x) = mkVar x := rfl
@[simp] theorem toCoind_mu (x : String) (body : LocalTypeR) :
    toCoind (.mu x body) = mkMu x (toCoind body) := rfl

@[simp] theorem toCoind_send (p : String) (bs : List (Label × LocalTypeR)) :
    toCoind (.send p bs) = mkSend p (toCoindBranches bs) := rfl

@[simp] theorem toCoind_recv (p : String) (bs : List (Label × LocalTypeR)) :
    toCoind (.recv p bs) = mkRecv p (toCoindBranches bs) := rfl

end RumpsteakV2.Coinductive
