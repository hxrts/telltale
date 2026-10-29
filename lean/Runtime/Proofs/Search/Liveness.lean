import Runtime.Proofs.Search.Liveness.Termination
import Runtime.Proofs.Search.Liveness.Fairness
import Runtime.Proofs.Search.Liveness.Completeness

/-!
# Runtime.Proofs.Search.Liveness

Machine-level liveness extensions for search, re-exported from:

- `Liveness.Termination`: fixed-phase and rebuild-aware termination under
  explicit finite reachable-state premises
- `Liveness.Fairness`: bounded fairness for entries that are not initially
  min-priority
- `Liveness.Completeness`: goal reachability from explicit witness-path and
  graph-reachability premises
-/
