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

Logical API for Iris separation logic infrastructure.

## Trust Boundary

This file and `IrisExtractionInstance.lean` form the **Iris extraction boundary**.
Together they provide:

1. **Logical definitions** (this file): Type aliases and parameter bundles that
   downstream modules use for proof obligations.

2. **Runtime erasure** (`IrisExtractionInstance`): `@[implemented_by]` overrides
   that substitute trivial implementations at codegen/eval time.

## Why Extraction Is Needed

Iris propositions (`iProp`) are **ghost state** — they exist purely for logical
reasoning and do not correspond to runtime data. The separation logic machinery
(invariants, fancy updates, ghost variables) guides proofs but has no
computational content.

At runtime:
- Ghost names don't exist
- Invariant masks don't exist
- Fancy updates are identity operations
- Ghost ownership assertions are vacuously true (`emp`)

This is intentional by design: Iris provides a *specification language* for
concurrent program correctness, not a runtime data structure.

## Expose

- `Telltale.TelltaleIris`: Parameter bundle for Iris infrastructure
- `Telltale.iProp`, `Telltale.GhostName`, `Telltale.Mask`, `Telltale.Namespace`
- `Telltale.GhostVarSlot`, `Telltale.SavedPropSlot`, `Telltale.GhostMapSlot`
- `Telltale.wsatGS`

Runtime erasure mappings are attached in `IrisExtractionInstance`.
-/

set_option autoImplicit false

namespace Telltale

open Iris Iris.Algebra Iris.Std Iris.BI Iris.BaseLogic COFE

/-! ## Parameter Bundle

The `TelltaleIris` class bundles all Iris infrastructure parameters needed by
the verification. This includes:
- Ghost functors (`GF`) for the recursive domain equation
- Finite map type (`M`) for heap-like structures
- Fraction type (`F`) for fractional permissions
- World satisfaction ghost state (`W`)
-/

/-- Bundle of Iris infrastructure parameters for Telltale verification.

This typeclass collects all the Iris-level parameters needed to instantiate
the separation logic. Downstream modules add `[TelltaleIris]` to access
ghost state, invariants, and fancy updates. -/
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

/-! ## Dispatch Typeclasses for Ghost State

These "slot" typeclasses register types for use with Iris ghost state primitives.
Each slot bundles the OFE (step-indexed equivalence) instances and ghost functor
membership proofs needed to use a type with the corresponding ghost construct.

**Why slots?** Iris ghost state is parameterized by resource algebras. The slot
pattern lets application code declare which types can be stored as ghost
variables/maps/props, with the necessary algebraic structure bundled together.
-/

/-- Slot for ghost variables of type `α`.

Registers `α` (wrapped as `LeibnizO α`) for use with `ghost_var`. Provides
the OFE structure and ghost functor membership needed by the ghost variable
resource algebra. -/
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
