import Telltale.Protocol.LocalTypeDB.Core
import Telltale.Protocol.LocalTypeDB.Preservation

/-! # Telltale.Protocol.LocalTypeDB

De Bruijn indexed local types for clean substitution proofs.

This module provides a de Bruijn representation of local types where:
- Variables are natural numbers (de Bruijn indices)
- `mu` binds index 0 in its body
- Substitution and lifting follow standard de Bruijn conventions

The key advantage: guardedness and contractiveness proofs are simpler
because bound variables are structurally separate from free variables.
-/
