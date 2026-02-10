import Iris.Instances.IProp.Instance
import Iris.BaseLogic.Lib.Wsat
import Iris.BaseLogic.Lib.FancyUpdates
import Iris.BaseLogic.Lib.Invariants
import Iris.BaseLogic.Lib.CancelableInvariants
import Iris.BI.BigOp
import Iris.BaseLogic.Lib.GhostVar
import Iris.BaseLogic.Lib.GhostMap
import Iris.BaseLogic.Lib.SavedProp
import Iris.ProgramLogic.Language

/-!
# IrisExtractionAPI

Logical API for Iris-facing proof infrastructure.

## Expose

- `Telltale.TelltaleIris`
- `Telltale.iProp`, `Telltale.GhostName`, `Telltale.Mask`, `Telltale.Namespace`
- `Telltale.GhostVarSlot`, `Telltale.SavedPropSlot`, `Telltale.GhostMapSlot`
- `Telltale.wsatGS`

Runtime erasure mappings are attached in
`IrisExtractionInstance`.
-/

set_option autoImplicit false

namespace Telltale

open Iris Iris.Algebra Iris.Std Iris.BI Iris.BaseLogic COFE

/-! ## Parameter Bundle -/

class TelltaleIris where
  GF : BundledGFunctors
  M : Type _ → Type _
  F : Type _
  instUFraction : UFraction F
  instFiniteMap : FiniteMap Positive M
  instFiniteMapLaws : FiniteMapLaws Positive M
  instHeapFiniteMap : HeapFiniteMap Positive M
  instElemG_CoPsetDisj : ElemG GF (COFE.constOF CoPsetDisj)
  instElemG_GSetDisj : ElemG GF (COFE.constOF GSetDisj)
  instElemG_Inv : ElemG GF (InvF GF M F)
  instElemG_Cinv : ElemG GF (COFE.constOF (Iris.BaseLogic.CinvR F))
  W : WsatGS GF

attribute [instance] TelltaleIris.instUFraction
attribute [instance] TelltaleIris.instFiniteMap
attribute [instance] TelltaleIris.instFiniteMapLaws
attribute [instance] TelltaleIris.instHeapFiniteMap
attribute [instance] TelltaleIris.instElemG_CoPsetDisj
attribute [instance] TelltaleIris.instElemG_GSetDisj
attribute [instance] TelltaleIris.instElemG_Inv
attribute [instance] TelltaleIris.instElemG_Cinv

/-! ## Core Type Aliases -/

variable [ti : TelltaleIris]

abbrev iProp : Type _ := IProp ti.GF
abbrev GhostName := GName
abbrev Mask := Iris.Set Positive
abbrev Namespace := Iris.Namespace

/-! ## Dispatch Typeclasses for Ghost State -/

class GhostVarSlot (α : Type) where
  instOFE : OFE (LeibnizO α)
  instDiscrete : OFE.Discrete (LeibnizO α)
  instLeibniz : OFE.Leibniz (LeibnizO α)
  instElemG : ElemG ti.GF (GhostVarF ti.F (LeibnizO α))

attribute [instance] GhostVarSlot.instOFE
attribute [instance] GhostVarSlot.instDiscrete
attribute [instance] GhostVarSlot.instLeibniz
attribute [instance] GhostVarSlot.instElemG

class SavedPropSlot where
  instElemG : ElemG ti.GF (SavedPropF ti.GF ti.F)

attribute [instance] SavedPropSlot.instElemG

/-- Slot for ghost maps with value type `V`. -/
class GhostMapSlot (V : Type) where
  instOFE : OFE (LeibnizO V)
  instDiscrete : OFE.Discrete (LeibnizO V)
  instLeibniz : OFE.Leibniz (LeibnizO V)
  instElemG : ElemG ti.GF (GhostMapF ti.GF ti.M ti.F (LeibnizO V))

attribute [instance] GhostMapSlot.instOFE
attribute [instance] GhostMapSlot.instDiscrete
attribute [instance] GhostMapSlot.instLeibniz
attribute [instance] GhostMapSlot.instElemG

/-! ## Internal Alias -/

def wsatGS : WsatGS ti.GF := ti.W

end Telltale

/-! ## Root Exports -/

export Telltale (iProp GhostName GhostVarSlot GhostMapSlot SavedPropSlot)
export Iris (Positive)
export Telltale (Mask Namespace)
