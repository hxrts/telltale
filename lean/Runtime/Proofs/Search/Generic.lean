import Runtime.Proofs.Search.Core
import Runtime.Proofs.Search.Problem
import Runtime.Proofs.Search.SelectedResults
import Runtime.Proofs.Search.Authority
import Runtime.Proofs.Search.Fairness
import Runtime.Proofs.Search.Executable
import Runtime.Proofs.Search.FullMachine
import Runtime.Proofs.Search.Reseeding
import Runtime.Proofs.Search.Machine
import Runtime.Proofs.Search.GenericLiveness
import Runtime.Proofs.Search.Refinement
import Runtime.Proofs.Search.GenericProfileClaims
import Runtime.Proofs.Search.Inventory
import Runtime.Proofs.Search.TheoremPack

set_option autoImplicit false

/-!
# Runtime.Proofs.Search.Generic

Curated generic-machine proof barrel for the search lane.

This surface collects machine semantics, invariants, replay/refinement,
generic liveness/fairness, selected-result vocabulary, execution-profile
claims, and theorem-pack metadata without pulling in the path-problem-specific
completeness/publication family.
-/
