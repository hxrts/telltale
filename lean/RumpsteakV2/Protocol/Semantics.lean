import RumpsteakV2.Semantics.EnvStep
import RumpsteakV2.Semantics.Typing
import RumpsteakV2.Semantics.Environment

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
- `EnvConfig`
- `EnvAction`
- `EnvConfigStep`
- `FairEnv`
-/

namespace RumpsteakV2.Protocol.Semantics

export RumpsteakV2.Semantics.EnvStep (ProjectedEnv ProjectedEnv.lookup ProjectedEnv.set projEnv EnvStep)
export RumpsteakV2.Semantics.Typing (WellFormedEnv)
export RumpsteakV2.Semantics.Environment (MsgQueue Channel EnvConfig EnvAction EnvConfigStep FairEnv)

end RumpsteakV2.Protocol.Semantics
