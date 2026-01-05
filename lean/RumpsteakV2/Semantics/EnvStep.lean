import RumpsteakV2.Protocol.CoTypes.Quotient
import RumpsteakV2.Protocol.GlobalType
import RumpsteakV2.Protocol.LocalTypeR
import RumpsteakV2.Protocol.Projection.Trans

/-! # RumpsteakV2.Semantics.EnvStep

Environment-step relation for V2.

## Expose

The following definitions form the semantic interface for proofs:

- `ProjectedEnv`
- `ProjectedEnv.lookup`
- `ProjectedEnv.set`
- `projEnv`
- `EnvStep`
-/

namespace RumpsteakV2.Semantics.EnvStep

open RumpsteakV2.Protocol.GlobalType
open RumpsteakV2.Protocol.LocalTypeR
open RumpsteakV2.Protocol.Projection.Trans
open RumpsteakV2.Protocol.CoTypes.Quotient

/-- Projected environment mapping roles to local types (quotiented). -/
abbrev ProjectedEnv := List (String × QLocalTypeR)

namespace ProjectedEnv

/-- Lookup a role in a projected environment. -/
def lookup (env : ProjectedEnv) (role : String) : Option QLocalTypeR :=
  (env.find? (fun pair => pair.1 == role)).map Prod.snd

/-- Set a role in a projected environment (insert if missing). -/
def set (env : ProjectedEnv) (role : String) (lt : QLocalTypeR) : ProjectedEnv :=
  match env with
  | [] => [(role, lt)]
  | (r, t) :: rest =>
      if r == role then
        (role, lt) :: rest
      else
        (r, t) :: set rest role lt

end ProjectedEnv

/-- Project a global type into a role-indexed environment. -/
def projEnv (g : GlobalType) : ProjectedEnv :=
  g.roles.map fun role => (role, QLocalTypeR.ofLocal (trans g role))

/-- Environment step induced by a global step through projection. -/
inductive EnvStep : ProjectedEnv → GlobalActionR → ProjectedEnv → Prop where
  | of_global (g g' : GlobalType) (act : GlobalActionR) :
      step g act g' →
      EnvStep (projEnv g) act (projEnv g')

end RumpsteakV2.Semantics.EnvStep
