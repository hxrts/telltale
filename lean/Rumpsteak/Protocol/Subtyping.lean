import Rumpsteak.Protocol.Core

/-! # Rumpsteak.Protocol.Subtyping

Subsequence-based subtyping for local type comparison.

## Overview

This module provides subtyping operations used to verify that exported programs
conform to their projected local types. Subtyping is based on the subsequence
relation: a program's actions must appear in the same order as the projection,
though not necessarily contiguously.

## Expose

The following definitions form the semantic interface for proofs:

- `isSubsequence`: Check if one list is a subsequence of another
- `isSubtype`: Check if one local type is a subtype of another

Proofs about these definitions (reflexivity, etc.) are in `Rumpsteak.Proofs.Subtyping`.

## Main Definitions

- `isSubsequence` - Generic subsequence check with decidable equality
- `isSubtype` - Local type subtyping combining length and subsequence checks
-/

namespace Rumpsteak.Protocol.Subtyping

open Rumpsteak.Protocol.Core

/-- Check if `sub` is a subsequence of `sup`, preserving order.
    Elements of `sub` must appear in `sup` in the same relative order,
    but not necessarily contiguously.

    Examples:
    - `[a, c]` is a subsequence of `[a, b, c]`
    - `[a, c]` is NOT a subsequence of `[c, a]` (order matters)
    - `[]` is a subsequence of any list -/
def isSubsequence {α : Type} [DecidableEq α] : List α → List α → Bool
  | [], _ => true
  | _, [] => false
  | a :: as, b :: bs =>
    if a = b then
      isSubsequence as bs
    else
      isSubsequence (a :: as) bs
termination_by xs ys => (xs.length, ys.length)

/-- Check if `sub` is a subtype of `sup` in the asynchronous session type sense.
    This requires:
    1. The subtype has at most as many actions as the supertype
    2. The subtype's actions form a subsequence of the supertype's actions

    This captures the idea that a program can omit some optional actions
    but must preserve the order of the actions it does perform. -/
def isSubtype (sub sup : LocalType) : Bool :=
  sub.actions.length <= sup.actions.length &&
    isSubsequence sub.actions sup.actions

end Rumpsteak.Protocol.Subtyping
