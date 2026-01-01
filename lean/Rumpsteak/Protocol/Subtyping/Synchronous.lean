import Rumpsteak.Protocol.Core
import Rumpsteak.Protocol.LocalTypeR
import Rumpsteak.Protocol.GlobalType

/-! # Rumpsteak.Protocol.Subtyping.Synchronous

Synchronous subtyping for recursive local types.

## Overview

This module implements synchronous session subtyping for recursive local types.
Synchronous subtyping follows the standard covariant/contravariant rules:
- Outputs (sends) are covariant: subtypes can have fewer/smaller outputs
- Inputs (recvs) are contravariant: subtypes can have more/larger inputs

This is the "safe substitution" relation: if T ≤ T', a process with type T
can safely replace one with type T'.

Based on: "A Very Gentle Introduction to Multiparty Session Types" (Yoshida & Gheri)

## Expose

The following definitions form the semantic interface for proofs:

- `syncSubtype`: Check if one recursive local type is a subtype of another
- `syncSubtypeFlat`: Check subtyping for flat (non-recursive) local types

## Main Definitions

- `syncSubtype` - Synchronous subtyping check for LocalTypeR
- `branchSubtype` - Helper for comparing branch lists
-/

namespace Rumpsteak.Protocol.Subtyping.Synchronous

open Rumpsteak.Protocol.Core
open Rumpsteak.Protocol.LocalTypeR
open Rumpsteak.Protocol.GlobalType (Label)

/-! ## Flat Subtyping (from existing implementation) -/

/-- Check if `sub` is a subsequence of `sup`, preserving order.
    Elements of `sub` must appear in `sup` in the same relative order,
    but not necessarily contiguously.

    This is the original flat subtyping used by the runner. -/
def isSubsequence {α : Type} [DecidableEq α] : List α → List α → Bool
  | [], _ => true
  | _, [] => false
  | a :: as, b :: bs =>
    if a = b then
      isSubsequence as bs
    else
      isSubsequence (a :: as) bs
termination_by xs ys => (xs.length, ys.length)

/-- Check if a flat local type is a subtype of another.
    Uses subsequence-based comparison for action sequences. -/
def syncSubtypeFlat (sub sup : LocalType) : Bool :=
  sub.actions.length <= sup.actions.length &&
    isSubsequence sub.actions sup.actions

/-! ## Recursive Subtyping -/

/-- Check if all labels in `sub` appear in `sup` with compatible continuations.
    For send (output), sub can have fewer branches (covariant).
    For recv (input), sub must have at least the branches of sup (contravariant). -/
partial def branchSubtypeSend
    (sub sup : List (Label × LocalTypeR))
    (subtypeFn : LocalTypeR → LocalTypeR → Bool) : Bool :=
  -- Covariant: every branch in sub must have a matching branch in sup
  sub.all fun (subLabel, subCont) =>
    match sup.find? (fun (l, _) => l.name == subLabel.name) with
    | some (_, supCont) => subtypeFn subCont supCont
    | none => false

/-- Check branch subtyping for receive (contravariant).
    The subtype must accept at least what the supertype accepts. -/
partial def branchSubtypeRecv
    (sub sup : List (Label × LocalTypeR))
    (subtypeFn : LocalTypeR → LocalTypeR → Bool) : Bool :=
  -- Contravariant: every branch in sup must have a matching branch in sub
  sup.all fun (supLabel, supCont) =>
    match sub.find? (fun (l, _) => l.name == supLabel.name) with
    | some (_, subCont) => subtypeFn subCont supCont
    | none => false

/-- Synchronous subtyping for recursive local types.

    Rules:
    - end ≤ end
    - var t ≤ var t
    - !q{branches₁} ≤ !q{branches₂} if branches covariant
    - ?p{branches₁} ≤ ?p{branches₂} if branches contravariant
    - μt.T₁ ≤ μt.T₂ if T₁ ≤ T₂

    Note: This is a coinductive definition; for simplicity we use
    a bounded depth check to handle recursion. -/
partial def syncSubtype (sub sup : LocalTypeR) (fuel : Nat := 100) : Bool :=
  if fuel == 0 then true  -- Assume true at depth limit (coinductive base)
  else match sub, sup with
  | .end, .end => true
  | .var v1, .var v2 => v1 == v2
  | .send p1 branches1, .send p2 branches2 =>
    p1 == p2 && branchSubtypeSend branches1 branches2 (fun t1 t2 => syncSubtype t1 t2 (fuel - 1))
  | .recv p1 branches1, .recv p2 branches2 =>
    p1 == p2 && branchSubtypeRecv branches1 branches2 (fun t1 t2 => syncSubtype t1 t2 (fuel - 1))
  | .mu v1 body1, .mu v2 body2 =>
    v1 == v2 && syncSubtype body1 body2 (fuel - 1)
  | _, _ => false

/-- Check structural equality of recursive local types.
    Two types are equal if they have the same structure. -/
def syncEqual (t1 t2 : LocalTypeR) : Bool :=
  syncSubtype t1 t2 && syncSubtype t2 t1

/-! ## Subtyping with Width and Depth -/

/-- Width subtyping: can add more recv branches or remove send branches. -/
def widthSubtype (sub sup : LocalTypeR) : Bool :=
  syncSubtype sub sup

/-- Check if a LocalTypeR is already unfolded (not a mu). -/
def isLocalTypeUnfolded (lt : LocalTypeR) : Bool :=
  match lt with
  | .mu _ _ => false
  | _ => true

/-- Depth subtyping: recursive types can be unfolded for comparison. -/
partial def depthSubtype (sub sup : LocalTypeR) (fuel : Nat := 10) : Bool :=
  if fuel == 0 then syncSubtype sub sup
  else
    let sub' := sub.unfold
    let sup' := sup.unfold
    -- If both are already unfolded, just check sync subtype
    if isLocalTypeUnfolded sub && isLocalTypeUnfolded sup then
      syncSubtype sub sup
    else
      depthSubtype sub' sup' (fuel - 1)

end Rumpsteak.Protocol.Subtyping.Synchronous
