-- Program-side view of exported effects used by the Lean runner.
import Rumpsteak.Projection

/-! Encodes exported effect sequences so the runner can compare them with
    projected local types. -/

namespace Rumpsteak.Program

open Rumpsteak.Projection

/- Standard effect operations produced by the choreography exporter. -/
inductive Effect
| send (partner : String) (label : String)
| recv (partner : String) (label : String)
deriving Inhabited, Repr, DecidableEq, BEq

/- Program bundles the role and its sequence of effects for verification. -/
structure Program where
  role : String
  effects : List Effect
deriving Inhabited, Repr, BEq

/- Convert handler effects into local actions for comparison with projection. -/
def effectToLocalAction : Effect → LocalAction
  | .send partner label => { kind := LocalKind.send, partner, label }
  | .recv partner label => { kind := LocalKind.recv, partner, label }

/- Build the local type seen by this role from its exported effects. -/
def localTypeOf (program : Program) : LocalType :=
  { actions := program.effects.map effectToLocalAction }

/- Compare the generated local type to the projection result. -/
def matchesLocalType (program : Program) (lt : LocalType) : Bool :=
  localTypeOf program == lt

/- Convenience helpers for diagnostics and tests. -/
def isEmpty (program : Program) : Bool :=
  program.effects.isEmpty

/- Extract all labels for quick comparisons or logging. -/
def effectLabels (program : Program) : List String :=
  program.effects.map fun effect =>
    match effect with
    | .send _ label => label
    | .recv _ label => label

/- Append an effect while building a program dynamically. -/
def appendEffect (program : Program) (effect : Effect) : Program :=
  { program with effects := program.effects ++ [effect] }

end Rumpsteak.Program
