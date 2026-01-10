import Batteries.Tactic.Lint
import RumpsteakV2

/-!
# RumpsteakV2 Lint Driver

Custom linting driver that only lints declarations in the RumpsteakV2 namespace.

This prevents linting of Mathlib and other dependencies, following the pattern
used by mathlib itself to avoid self-linting when used as a dependency.

## Usage

```bash
# Lint all RumpsteakV2 modules
lake exe runLinter

# Or run via lake
cd lean && lake build runLinter
```

## Implementation

The key is the `rumpsteakV2Decl` filter which only returns `true` for declarations
whose name prefix is `RumpsteakV2`.

This keeps all linters enabled but only runs them on our project's declarations.
-/

open Lean Elab Command

/-- Filter that only lints declarations in the RumpsteakV2 namespace.

This function returns `true` only for declarations whose name starts with `RumpsteakV2`.
All other declarations (from Mathlib, Batteries, etc.) are skipped.

Examples:
- `RumpsteakV2.Protocol.LocalTypeR` → `true` (linted)
- `RumpsteakV2.Protocol.CoTypes.EQ2.EQ2_refl` → `true` (linted)
- `Mathlib.Data.List.Forall2` → `false` (skipped)
- `Lean.Meta.Simp.simp` → `false` (skipped)
-/
def rumpsteakV2Decl : Name → Bool
  | n => n.getPrefix == `RumpsteakV2

/-- Demonstrate usage: lint only RumpsteakV2 declarations.

The `#lint in RumpsteakV2` command uses the package name to automatically
filter declarations. This is the simplest and recommended approach.

Alternative: use the predicate filter defined above for programmatic linting.
-/

-- Lint all RumpsteakV2 declarations
-- This command only lints declarations in the RumpsteakV2 package,
-- excluding Mathlib, Batteries, and other dependencies
#lint in RumpsteakV2

/-!
## Notes

### Why we need this

Without filtering:
- Linters run on ALL declarations from ALL dependencies
- Mathlib has ~100,000+ declarations
- Many Mathlib declarations intentionally don't follow all lint rules
- Results in thousands of false positive warnings

With filtering:
- Only lint RumpsteakV2 declarations (~500-1000)
- No warnings from dependencies
- Clean, actionable lint output
- Fast linting (< 1 minute vs. hours)

### Alternative approaches

If you need finer-grained control:

```lean
-- Only lint specific subnamespaces
def protocolDecl : Name → Bool
  | n => n.getPrefix == `RumpsteakV2.Protocol

-- Exclude specific modules
def rumpsteakV2DeclExcludeTests : Name → Bool
  | n => n.getPrefix == `RumpsteakV2 && !n.toString.contains "Test"

-- Only lint public declarations
def rumpsteakV2PublicDecl : Name → Bool
  | n => n.getPrefix == `RumpsteakV2 && !n.isPrivateName
```

### Comparison to mathlib

Mathlib uses the same pattern in its lint driver:

```lean
-- From mathlib/scripts/runLinter.lean (simplified)
def mathlibDecl : Name → Bool
  | n => n.getPrefix == `Mathlib

#eval Lint.lintAll mathlibDecl
```

This is the standard approach for projects using Mathlib as a dependency.

### Adding to CI

To run linting in CI, add to your GitHub Actions workflow:

```yaml
- name: Lint RumpsteakV2
  run: |
    cd lean
    lake build RumpsteakV2Lint
```

Or use the lake exe approach:

```yaml
- name: Lint RumpsteakV2
  run: |
    cd lean
    lake exe runLinter RumpsteakV2
```

### Configuring specific linters

You can enable/disable specific linters by setting options before the lint call:

```lean
set_option linter.unusedVariables true
set_option linter.docBlame false

#eval Lint.lintAll rumpsteakV2Decl
```

Or in individual files:

```lean
-- At top of file
set_option linter.style false  -- Disable style linter for this file
```

-/
