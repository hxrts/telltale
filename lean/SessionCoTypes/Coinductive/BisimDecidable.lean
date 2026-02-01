import SessionCoTypes.Coinductive.BisimDecidable.Core
import SessionCoTypes.Coinductive.BisimDecidable.BisimAux
import SessionCoTypes.Coinductive.BisimDecidable.Correctness

/-!
# Decidable Bisimulation for Regular Types

This module implements a decidable bisimulation check for regular coinductive types,
following the approach in the Coq reference implementation (subject_reduction/theories/CoTypes/bisim.v).

## Two-Phase Approach

1. **Phase 1**: Define a decidable `bisim` function with explicit termination via a measure
   - Uses a visited set to detect cycles
   - Terminates because the set of unvisited pairs decreases

2. **Phase 2**: Prove `bisim_sound` - that `bisim = true` implies `EQ2C`
   - Uses the existing bisimulation infrastructure

## Key Definitions

- `fullUnfoldN`: Unfold mu up to n times (bounded unfolding)
- `fullUnfold`: Unfold all mu until non-mu head (for regular types)
- `nextChildren`: Get children of a type after unfolding
- `reachablePairs`: Cartesian product of reachable sets
- `observableMatch`: Check if observables match
- `bisim`: The decidable bisimulation check
- `bisim_sound`: Soundness theorem
-/
