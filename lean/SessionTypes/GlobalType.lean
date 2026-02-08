import SessionTypes.GlobalType.Core
import SessionTypes.GlobalType.ValType
import SessionTypes.GlobalType.Semantics
import SessionTypes.GlobalType.WellFormedLemmas
import SessionTypes.GlobalType.ProductivityLemmas
import SessionTypes.GlobalType.Closedness

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
