import RumpsteakV2.Semantics.EnvStep

/-! # RumpsteakV2.Semantics.Typing

Typing and well-formedness infrastructure for V2.

## Expose

The following definitions form the semantic interface for proofs:

- `WellFormedEnv`
-/

namespace RumpsteakV2.Semantics.Typing

open RumpsteakV2.Semantics.EnvStep (ProjectedEnv)

/-- Basic well-formedness predicate for projected environments. -/
structure WellFormedEnv (env : ProjectedEnv) : Prop where
  /-- No duplicate role entries in the environment. -/
  nodup_roles : (env.map Prod.fst).Nodup

end RumpsteakV2.Semantics.Typing
