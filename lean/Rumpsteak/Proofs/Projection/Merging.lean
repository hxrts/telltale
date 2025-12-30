import Rumpsteak.Proofs.Projection.Merging.Basic
import Rumpsteak.Proofs.Projection.Merging.SortLemmas
import Rumpsteak.Proofs.Projection.Merging.Self
import Rumpsteak.Proofs.Projection.Merging.Commutative
import Rumpsteak.Proofs.Projection.Merging.Associative

/-! # Rumpsteak.Proofs.Projection.Merging

Proofs about the merge operator on recursive local types (`LocalTypeR.merge`).

## Overview

In MPST projection with merging (Yoshida & Gheri), when a role is *not* involved in a global
choice, we merge that role's projected local types across the branches. The merge operator is
partial:

- For **external choice** (`recv` / branching), merge unions labels and merges shared continuations.
- For **internal choice** (`send` / selection), merge is defined only when both sides have the same
  labels (a role cannot be forced to choose different outgoing labels based on an unseen choice).

This file proves algebraic laws that justify folding merge across multiple branch projections.

## Module Structure

The proof is split across multiple files for maintainability:

- `Basic.lean`: Infrastructure (termination helpers, canonicalization, Claims definitions)
- `SortLemmas.lean`: Branch sorting and helper lemmas
- `Self.lean`: `merge_self` proof
- `Commutative.lean`: `merge_commutative` proof
- `Associative.lean`: `merge_associative` proof (largest module)

## Claims

- `MergeSelf`: merging a type with itself succeeds and returns a canonicalized form.
- `MergeCommutative`: merge is commutative.
- `MergeAssociative`: 3-way merge is associative/commutative (in `Option` form).
-/

namespace Rumpsteak.Proofs.Projection.Merging

/-- Construct the claims bundle with all proven properties. -/
def claims : Claims := ⟨merge_self, merge_commutative, merge_associative⟩

end Rumpsteak.Proofs.Projection.Merging
