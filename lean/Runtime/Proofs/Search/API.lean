import Runtime.Proofs.Search.Generic
import Runtime.Proofs.Search.PathProblems

set_option autoImplicit false

/-!
# Runtime.Proofs.Search.API

Barrel import for search-specific fairness definitions and execution-profile-
scoped theorem surfaces.

The search proof lane treats scheduler/profile variation as execution-side
variation only. It does not redefine downstream search-problem semantics or
objective meaning.

The public proof surface is split between:

- `Generic` for machine semantics, invariants, replay/refinement, generic
  liveness/fairness, and execution-profile claims
- `PathProblems` for the path-search-specific completeness/publication family

Additional helper modules expose:

- `Generic` for the curated generic-machine theorem barrel
- `PathProblems` for the path-search-specific completeness/publication family
- `SelectedResults` through `Generic` for generic selected-result/observable
  vocabulary over the historical incumbent/path field names
-/
