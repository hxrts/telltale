import RumpsteakV2.Protocol.GlobalType.Part1
import RumpsteakV2.Protocol.GlobalType.Part2
import RumpsteakV2.Protocol.GlobalType.Part3
import RumpsteakV2.Protocol.GlobalType.Part4
import RumpsteakV2.Protocol.GlobalType.Part5

/-! # RumpsteakV2.Protocol.GlobalType

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
