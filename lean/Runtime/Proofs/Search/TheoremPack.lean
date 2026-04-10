import Runtime.Proofs.Search.Inventory

set_option autoImplicit false

/-!
# Runtime.Proofs.Search.TheoremPack

Packaged theorem inventory and profile-neutral metadata for the reduced search
theorem surface.
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

end Search
end Proofs
end Runtime
