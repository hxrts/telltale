import Runtime.Proofs.Conservation.Evidence
import Runtime.Proofs.Conservation.Authority
import Runtime.Proofs.Conservation.Identity
import Runtime.Proofs.Conservation.Commitment
import Runtime.Proofs.Conservation.Structure
import Runtime.Proofs.Conservation.Premise

set_option autoImplicit false

/-!
# Runtime.Proofs.Conservation.API

Public proof-facing facade for the six conservation-law theorem families.

Downstream modules should use this import when they want the direct theorem
surface corresponding to `work/design_principles.md`.
-/
