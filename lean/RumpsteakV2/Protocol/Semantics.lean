import RumpsteakV2.Semantics.EnvStep
import RumpsteakV2.Semantics.Typing

/-! # RumpsteakV2.Protocol.Semantics

Semantic infrastructure entry point for V2.

## Expose

The following definitions form the semantic interface for proofs:

- `ProjectedEnv`
- `ProjectedEnv.lookup`
- `ProjectedEnv.set`
- `projEnv`
- `EnvStep`
- `WellFormedEnv`
-/

namespace RumpsteakV2.Protocol.Semantics

export RumpsteakV2.Semantics.EnvStep (ProjectedEnv ProjectedEnv.lookup ProjectedEnv.set projEnv EnvStep)
export RumpsteakV2.Semantics.Typing (WellFormedEnv)

end RumpsteakV2.Protocol.Semantics
