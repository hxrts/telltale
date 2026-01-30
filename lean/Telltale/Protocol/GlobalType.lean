import Telltale.Protocol.GlobalType.Part1
import Telltale.Protocol.GlobalType.Part2
import Telltale.Protocol.GlobalType.Part3
import Telltale.Protocol.GlobalType.Part4
import Telltale.Protocol.GlobalType.Part5

/-! # Telltale.Protocol.GlobalType

Global types for the V2 development.

## Expose

The following definitions form the semantic interface for proofs:

- `PayloadSort`: payload type annotations
- `Label`: message labels with payload sorts
- `GlobalType`: global protocol types
- `GlobalType.wellFormed`: well-formedness predicate
- `GlobalType.roles`: extract role names
- `GlobalType.freeVars`: extract free type variables
- `GlobalType.substitute`: type variable substitution
- `GlobalActionR`: global action with sender, receiver, label
- `canStep`: global enabledness predicate
- `BranchesStep`: branch-wise step relation
- `step`: global async step relation
-/
