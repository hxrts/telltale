import Iris.Instances.IProp.Instance
import Iris.Instances.Lib.WSat
import Iris.Instances.Lib.FUpd
import Iris.Instances.Lib.Invariants
import Iris.Instances.Lib.CInvariants
import Iris.BI.BigOp
import Iris.Instances.Lib.GhostVar
import Iris.Instances.Lib.GhostMap
import Iris.Instances.Lib.SavedProp
import Iris.ProgramLogic.Language
import Iris.ProgramLogic.WeakestPre
import Iris.ProgramLogic.Adequacy

/-! # IrisExtractionAPI

Logical API for Iris separation logic infrastructure. -/

/-
The Problem. Iris separation logic provides ghost state for reasoning about
concurrent programs, but this ghost state has no runtime representation. We need
a clean API that downstream modules can use without importing the full Iris machinery.

Solution Structure. We define:
1. Type aliases (`iProp`, `GhostName`, `Mask`, `Namespace`) hiding Iris internals
2. Parameter bundles (`TelltaleIris`) collecting all infrastructure
3. Slot types for ghost variables, saved propositions, and ghost maps
The companion `IrisExtractionInstance` provides runtime erasure.
-/


/-! ## Trust Boundary

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

- `Telltale.TelltaleIris`: Ghost-functor bundle with upstream Iris resource classes
- `Telltale.iProp`, `Telltale.GhostName`, `Telltale.Mask`, `Telltale.Namespace`
- `Telltale.GhostVarSlot`, `Telltale.SavedPropSlot`, `Telltale.GhostMapSlot`
- `Telltale.Positive`, `Telltale.GhostMapCarrier`

Runtime erasure mappings are attached in `IrisExtractionInstance`.
-/

set_option autoImplicit false

namespace Telltale

open Iris Iris.Std

/-! ## Parameter Bundle

The `TelltaleIris` class fixes the global ghost-functor bundle `GF` and the
upstream Iris resource classes Telltale needs on it:
- `InvGS` — world satisfaction, later credits, and fancy updates
- `CInvG` — cancelable invariants
- `SavedPropG` — saved propositions
-/

/-- Bundle of Iris infrastructure parameters for Telltale verification.

Downstream modules add `[TelltaleIris]` to access ghost state, invariants,
and fancy updates over a single ghost-functor bundle. -/
class TelltaleIris where
  GF : BundledGFunctors
  instInvGS : InvGS GF
  instCInvG : CInvG GF
  instSavedPropG : SavedPropG GF

attribute [instance] TelltaleIris.instInvGS
attribute [instance] TelltaleIris.instCInvG
attribute [instance] TelltaleIris.instSavedPropG

/-! ## Core Type Aliases -/

variable [ti : TelltaleIris]

abbrev iProp : Type := IProp ti.GF
abbrev GhostName := GName
/-- Masks are upstream Iris `CoPset`s of positive invariant names. -/
abbrev Mask := CoPset
abbrev Namespace := _root_.Namespace
/-- Positive binary naturals used as ghost-map keys. -/
abbrev Positive := _root_.Pos

/-! ## Dispatch Typeclasses for Ghost State

These "slot" typeclasses register types for use with Iris ghost state
primitives. Each slot carries the ghost-functor membership needed to use a
type with the corresponding ghost construct.
-/

/-- Carrier for ghost maps keyed by positives. -/
abbrev GhostMapCarrier := fun (V : Type) => _root_.Std.ExtTreeMap _root_.Pos V compare

/-- Slot for ghost variables of type `α`. -/
class GhostVarSlot (α : Type) where
  instG : GhostVarG ti.GF α

attribute [instance] GhostVarSlot.instG

/-- Slot for saved propositions (always available through `TelltaleIris`). -/
class SavedPropSlot : Prop where

instance : SavedPropSlot := {}

/-- Slot for ghost maps with value type `V`. -/
class GhostMapSlot (V : Type) where
  instG : GhostMapG ti.GF _root_.Pos V GhostMapCarrier

attribute [instance] GhostMapSlot.instG

end Telltale

/-! ## Root Exports -/

export Telltale (iProp GhostName GhostVarSlot GhostMapSlot SavedPropSlot Positive)
export Telltale (Mask)
