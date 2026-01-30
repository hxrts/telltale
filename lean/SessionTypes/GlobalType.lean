import SessionTypes.GlobalType.Part1
import SessionTypes.GlobalType.Part2
import SessionTypes.GlobalType.Part3
import SessionTypes.GlobalType.Part4
import SessionTypes.GlobalType.Part5

/-! # SessionTypes.GlobalType

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
