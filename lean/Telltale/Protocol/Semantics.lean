import Telltale.Semantics.EnvStep
import Telltale.Semantics.Typing
import Telltale.Semantics.Environment

/-! # Telltale.Protocol.Semantics

Semantic infrastructure entry point for V2.

## Expose

The following definitions form the semantic interface for proofs:

- `ProjectedEnv`
- `ProjectedEnv.lookup`
- `ProjectedEnv.set`
- `projEnv`
- `EnvStep`
- `WellFormedEnv`
- `MsgQueue`
- `Channel`
- `EnvConfig`
- `EnvAction`
- `EnvConfigStep`
- `FairEnv`
-/

namespace Telltale.Protocol.Semantics

export Telltale.Semantics.EnvStep (ProjectedEnv ProjectedEnv.lookup ProjectedEnv.set projEnv EnvStep)
export Telltale.Semantics.Typing (WellFormedEnv)
export Telltale.Semantics.Environment (MsgQueue Channel EnvConfig EnvAction EnvConfigStep FairEnv)

end Telltale.Protocol.Semantics
