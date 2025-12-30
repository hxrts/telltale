/-! # Rumpsteak.Proofs

Entry point for all Rumpsteak proof modules.

## Overview

This module re-exports all proof modules and their claims bundles. Reviewers can
start here to audit the verified properties of the Rumpsteak verification library.

## Claims Summary

### Core Properties (Complete)
- `Duality.claims`: Duality operations are involutive
- `Subtyping.claims`: Subtyping is reflexive
- `Projection.claims`: Label subset check is reflexive
- `Projection.Merging.claims`: Merge is self-idempotent, commutative, and associative

### Safety Properties (Partial)
- `Safety.SubjectReduction.partialClaims`: Type preservation (in progress)
- `Safety.Progress.partialClaims`: Deadlock freedom (in progress)

## Usage

Import this module for access to all proofs:

```lean
import Rumpsteak.Proofs
```

Or import specific proof modules:

```lean
import Rumpsteak.Proofs.Duality
import Rumpsteak.Proofs.Projection.Merging
```

## Axioms

All axioms are centralized in `Rumpsteak.Proofs.Assumptions`. Currently empty
as no hardness assumptions are required for the proven properties.
-/

import Rumpsteak.Proofs.Assumptions
import Rumpsteak.Proofs.Duality
import Rumpsteak.Proofs.Projection
import Rumpsteak.Proofs.Projection.Merging
import Rumpsteak.Proofs.Subtyping
import Rumpsteak.Proofs.Safety.Progress
import Rumpsteak.Proofs.Safety.SubjectReduction

namespace Rumpsteak.Proofs

/-! ## Claims Re-exports -/

/-- Claims bundle for duality involutiveness. -/
abbrev dualityClaims := Duality.claims

/-- Claims bundle for subtyping reflexivity. -/
abbrev subtypingClaims := Subtyping.claims

/-- Claims bundle for projection reflexivity. -/
abbrev projectionClaims := Projection.claims

/-- Claims bundle for merge algebraic laws. -/
abbrev mergeClaims := Projection.Merging.claims

/-! ## Partial Claims (Safety Proofs in Progress) -/

/-- Partial claims for progress theorem. -/
abbrev progressPartialClaims := Safety.Progress.partialClaims

/-- Partial claims for subject reduction theorem. -/
abbrev subjectReductionPartialClaims := Safety.SubjectReduction.partialClaims

end Rumpsteak.Proofs
