import Telltale.Semantics.EnvStep

/-! # Telltale.Semantics.Typing

Typing and well-formedness infrastructure for V2.

## Expose

The following definitions form the semantic interface for proofs:

- `WellFormedEnv`
-/

namespace Telltale.Semantics.Typing

open Telltale.Semantics.EnvStep (ProjectedEnv)

/-- Basic well-formedness predicate for projected environments. -/
structure WellFormedEnv (env : ProjectedEnv) : Prop where
  /-- No duplicate role entries in the environment. -/
  nodup_roles : (env.map Prod.fst).Nodup

end Telltale.Semantics.Typing
