import Distributed.Families.CRDT.API

set_option autoImplicit false

/-! # Distributed.Families.CRDT.Profile

Profile constructors for CRDT theorem-pack attachment.
-/

namespace Distributed
namespace CRDT
namespace Profile

universe u v w x y z

/-- Build a CRDT theorem-family profile from semantic assumptions and premises. -/
def mk
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (model : Model State Op Context Obs Program)
    (assumptions : Assumptions model)
    (premises : Premises model) :
    CRDTProtocol where
  State := State
  Op := Op
  Context := Context
  Obs := Obs
  Program := Program
  model := model
  assumptions := assumptions
  premises := premises

/-- Build a CRDT erasure profile from erasure premises. -/
def mkErasure
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {KRich : Type z} {OpTag : Type v} {Args : Type w} {Enc : Type x}
    (model : Model State Op Context Obs Program)
    (premises : ErasurePremises model KRich OpTag Args Enc) :
    CRDTErasureProtocol where
  State := State
  Op := Op
  Context := Context
  Obs := Obs
  Program := Program
  KRich := KRich
  OpTag := OpTag
  Args := Args
  Enc := Enc
  model := model
  premises := premises

end Profile
end CRDT
end Distributed
