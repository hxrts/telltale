import RumpsteakV2.Protocol.Core
import RumpsteakV2.Protocol.GlobalType
import RumpsteakV2.Protocol.LocalTypeR
import RumpsteakV2.Protocol.LocalTypeDB
import RumpsteakV2.Protocol.LocalTypeConv
import RumpsteakV2.Protocol.LocalTypeRDBBridge
import RumpsteakV2.Protocol.Projection
import RumpsteakV2.Protocol.CoTypes
import RumpsteakV2.Protocol.Semantics
import RumpsteakV2.Protocol.Spatial

/-! # RumpsteakV2.Protocol

Protocol entry point, collecting core types, projection, and semantics.

## Exposed Definitions

### Core
- `Role` — participant identifier
- `Action` — communication action (sender, receiver, label)
- `Action.origin` / `Action.destination` / `Action.label` — action accessors
- `LocalKind` — send or receive direction
- `LocalAction` — local view of an action
- `LocalType` — local session type (kind + action)
- `LocalKind.swap` — flip send/receive
- `LocalAction.dual` / `LocalType.dual` — session duality

### Global types
- `PayloadSort` — message payload classifier
- `Label` — branch label
- `GlobalType` — global choreography type
  - `.end` — protocol termination
  - `.comm sender receiver branches` — labeled communication with branching
  - `.mu name body` — recursive type binder
  - `.var name` — type variable (de Bruijn named)
- `GlobalType.wellFormed` — no self-communication, guarded recursion, non-empty branches
- `GlobalType.roles` — participants mentioned in a protocol
- `GlobalType.freeVars` — free type variables
- `GlobalType.substitute` — capture-avoiding substitution

### Local types
- `LocalTypeR` — inductive local session type with recursive binders
- `LocalTypeR.dual` — session duality (swap send/recv)
- `LocalTypeR.unfold` — one-step mu unfolding
- `LocalTypeR.freeVars` — free type variables
- `LocalTypeR.substitute` — capture-avoiding substitution

### Projection
- `trans` — direct (functional) projection from global to local type
- `lcontractive` — contractiveness check for projected types
- `projectb` — boolean projection checker
- `CProject` — coinductive projection relation (greatest fixed point)
- `projectR?` — proof-carrying projection returning `Option { lt // CProject g role lt }`

### Coinductive types
- `EQ2` — coinductive equality on local types (greatest fixed point)
- `QLocalTypeR` — quotient of `LocalTypeR` by `EQ2`
- `QLocalTypeR.unfold` — unfolding on the quotient

### Semantics
- `ProjectedEnv` — maps roles to local types
- `ProjectedEnv.lookup` / `ProjectedEnv.set` — environment access
- `projEnv` — project a global type to a full environment
- `EnvStep` — environment step relation
- `WellFormedEnv` — well-formedness predicate on environments

### Spatial
- `SpatialReq` — spatial deployment requirements (colocation, reliability)
- `Topology` — site assignment for roles
- `Satisfies` — topology satisfies a spatial requirement
- `SpatialLe` — implication ordering on requirements
- `spatial_le_sound` — monotonicity: `R₁ ≤ R₂ → (topo ⊨ R₁ → topo ⊨ R₂)`
-/

namespace RumpsteakV2.Protocol

export RumpsteakV2.Protocol.Core
  (Role Action Action.origin Action.destination Action.label
    LocalKind LocalAction LocalType LocalKind.swap LocalAction.dual LocalType.dual)

export RumpsteakV2.Protocol.GlobalType
  (PayloadSort Label GlobalType GlobalType.wellFormed GlobalType.roles
    GlobalType.freeVars GlobalType.substitute)

export RumpsteakV2.Protocol.LocalTypeR
  (LocalTypeR LocalTypeR.dual LocalTypeR.unfold LocalTypeR.freeVars
    LocalTypeR.substitute)

export RumpsteakV2.Protocol.Projection
  (trans lcontractive projectb CProject projectR?)

export RumpsteakV2.Protocol.CoTypes
  (EQ2 QLocalTypeR QLocalTypeR.unfold)

export RumpsteakV2.Protocol.Semantics
  (ProjectedEnv ProjectedEnv.lookup ProjectedEnv.set projEnv EnvStep WellFormedEnv)

export RumpsteakV2.Protocol.Spatial
  (SpatialReq Topology Satisfies SpatialLe spatial_le_sound)

end RumpsteakV2.Protocol
