import Runtime.Proofs.Search.Inventory

set_option autoImplicit false

/-!
# Runtime.Proofs.Search.TheoremPack

Packaged theorem inventory and execution-profile-neutral metadata for the
reduced search theorem surface.

Execution-profile metadata in this pack classifies scheduler-side theorem
surfaces only. It does not redefine downstream search-problem semantics.

The theorem inventory is also split conceptually into:

- generic machine/refinement/fairness theorems
- generic selected-result/result-bound theorems
- path-problem-specific completeness/discovery theorems

Path-search reachability/publication theorems remain one supported
problem-specific family rather than the only machine shape.
-/

namespace Runtime
namespace Proofs
namespace Search

/-- First-class packaged artifact for the reduced search theorem surface. -/
structure SearchFairnessTheoremPack where
  inventory : List (String × Bool)
  inventorySupportClasses : List (String × SearchTheoremSupportClass)
  canonicalServiceBoundSteps : Nat
  canonicalGoalWindowDiscoverySuffixBoundSteps : Nat
  deriving Repr

/-- Canonical packaged theorem surface for search fairness. -/
def buildSearchFairnessTheoremPack : SearchFairnessTheoremPack :=
  { inventory := fairnessTheoremInventory
  , inventorySupportClasses := fairnessTheoremInventorySupportClasses
  , canonicalServiceBoundSteps := 1
  , canonicalGoalWindowDiscoverySuffixBoundSteps := 1
  }

/-- Compact theorem-pack inventory surface for downstream gates. -/
def theoremPackInventory : List (String × Bool) :=
  buildSearchFairnessTheoremPack.inventory

/-- Theorem-support classification surface for downstream gates and docs. -/
def theoremPackInventorySupportClasses :
    List (String × SearchTheoremSupportClass) :=
  buildSearchFairnessTheoremPack.inventorySupportClasses

/-- Generic-machine theorem rows from the packaged search theorem surface. -/
def theoremPackGenericMachineInventory : List (String × Bool) :=
  genericMachineTheoremInventory

/-- Generic selected-result theorem rows from the packaged search theorem surface. -/
def theoremPackGenericSelectedResultInventory : List (String × Bool) :=
  genericSelectedResultTheoremInventory

/-- Path-problem-specific theorem rows from the packaged search theorem surface. -/
def theoremPackProblemSpecificInventory : List (String × Bool) :=
  problemSpecificTheoremInventory

end Search
end Proofs
end Runtime
