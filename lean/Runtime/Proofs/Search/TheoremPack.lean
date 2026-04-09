import Runtime.Proofs.Search.Inventory

set_option autoImplicit false

/-!
# Runtime.Proofs.Search.TheoremPack

Packaged theorem inventory and profile-neutral metadata for the reduced search
fairness proof surface.
-/

namespace Runtime
namespace Proofs
namespace Search

/-- First-class packaged artifact for the reduced search fairness theorem
surface. -/
structure SearchFairnessTheoremPack where
  inventory : List (String × Bool)
  canonicalServiceBoundSteps : Nat
  canonicalGoalWindowDiscoverySuffixBoundSteps : Nat
  deriving Repr

/-- Canonical packaged theorem surface for search fairness. -/
def buildSearchFairnessTheoremPack : SearchFairnessTheoremPack :=
  { inventory := fairnessTheoremInventory
  , canonicalServiceBoundSteps := 1
  , canonicalGoalWindowDiscoverySuffixBoundSteps := 1
  }

/-- Compact theorem-pack inventory surface for downstream gates. -/
def theoremPackInventory : List (String × Bool) :=
  buildSearchFairnessTheoremPack.inventory

end Search
end Proofs
end Runtime
