import Rumpsteak.Protocol.LocalTypeR
import Rumpsteak.Protocol.GlobalType

/-! # Rumpsteak.Protocol.Subtyping.TreeDecomposition

SISO (Single-Input-Single-Output) tree decomposition for async subtyping.

## Overview

This module implements the tree decomposition technique from the POPL 2021 paper
"Precise Subtyping for Asynchronous Multiparty Sessions" (Ghilezan et al.).

The key insight is that asynchronous session types can be decomposed into
alternating input and output trees, which can then be compared independently.

## Expose

The following definitions form the semantic interface for proofs:

- `InputTree`: Tree of input (receive) prefixes
- `OutputTree`: Tree of output (send) prefixes
- `sisoDecompose`: Decompose a local type into SISO trees

## Main Definitions

- `InputTree` - Inductive type for input prefix trees
- `OutputTree` - Inductive type for output prefix trees
- `sisoDecompose` - Main decomposition function
-/

namespace Rumpsteak.Protocol.Subtyping.TreeDecomposition

open Rumpsteak.Protocol.LocalTypeR
open Rumpsteak.Protocol.GlobalType (Label)

/-- An input tree captures all input (receive) prefixes of a local type.

    Shape: A tree where each node is labeled by a receive action,
    and children represent continuations after receiving that message. -/
inductive InputTree where
  /-- Leaf node: no more inputs at this point -/
  | leaf : InputTree
  /-- Input node: receive from partner with label, then children -/
  | node : String → Label → List InputTree → InputTree
deriving Repr, Inhabited

/-- An output tree captures all output (send) prefixes of a local type.

    Shape: A tree where each node is labeled by a send action,
    and children represent continuations after sending that message. -/
inductive OutputTree where
  /-- Leaf node: no more outputs at this point -/
  | leaf : OutputTree
  /-- Output node: send to partner with label, then children -/
  | node : String → Label → List OutputTree → OutputTree
deriving Repr, Inhabited

/-- A SISO segment is an alternating pair of input and output trees.
    The decomposition produces a list of these segments. -/
structure SisoSegment where
  /-- Input tree (receives that can happen) -/
  inputs : InputTree
  /-- Output tree (sends that can happen) -/
  outputs : OutputTree
deriving Repr, Inhabited

/-- Extract the input tree from the head of a local type.
    Collects all receive prefixes until a send or end is reached. -/
partial def extractInputTree (lt : LocalTypeR) (fuel : Nat := 50) : InputTree × LocalTypeR :=
  if fuel == 0 then (InputTree.leaf, lt)
  else match lt with
  | .end => (InputTree.leaf, .end)
  | .var _ => (InputTree.leaf, lt)
  | .send _ _ => (InputTree.leaf, lt)  -- Stop at sends
  | .recv partner branches =>
    let children := branches.map fun (label, cont) =>
      let (childTree, _) := extractInputTree cont (fuel - 1)
      (label, childTree)
    -- Build input tree with all branches
    let tree := if children.isEmpty then InputTree.leaf
      else InputTree.node partner children[0]!.1 (children.map fun (_, t) => t)
    -- Return remainder (for now, just the first branch continuation)
    let remainder := match branches.head? with
      | some (_, cont) => cont
      | none => .end
    (tree, remainder)
  | .mu _ body => extractInputTree body (fuel - 1)

/-- Extract the output tree from the head of a local type.
    Collects all send prefixes until a receive or end is reached. -/
partial def extractOutputTree (lt : LocalTypeR) (fuel : Nat := 50) : OutputTree × LocalTypeR :=
  if fuel == 0 then (OutputTree.leaf, lt)
  else match lt with
  | .end => (OutputTree.leaf, .end)
  | .var _ => (OutputTree.leaf, lt)
  | .recv _ _ => (OutputTree.leaf, lt)  -- Stop at receives
  | .send partner branches =>
    let children := branches.map fun (label, cont) =>
      let (childTree, _) := extractOutputTree cont (fuel - 1)
      (label, childTree)
    -- Build output tree with all branches
    let tree := if children.isEmpty then OutputTree.leaf
      else OutputTree.node partner children[0]!.1 (children.map fun (_, t) => t)
    -- Return remainder
    let remainder := match branches.head? with
      | some (_, cont) => cont
      | none => .end
    (tree, remainder)
  | .mu _ body => extractOutputTree body (fuel - 1)

/-- Check if a LocalTypeR is an end or variable (base case for recursion). -/
def isLocalTypeBase (lt : LocalTypeR) : Bool :=
  match lt with
  | .end => true
  | .var _ => true
  | _ => false

/-- Decompose a local type into alternating SISO segments.

    The decomposition alternates between extracting input trees and output trees,
    producing a list of (InputTree, OutputTree) pairs. -/
partial def sisoDecompose (lt : LocalTypeR) (fuel : Nat := 20) : List SisoSegment :=
  if fuel == 0 then []
  else match lt with
  | .end => []
  | .var _ => []
  | _ =>
    let (inputTree, afterInputs) := extractInputTree lt fuel
    let (outputTree, afterOutputs) := extractOutputTree afterInputs (fuel - 1)
    let segment : SisoSegment := { inputs := inputTree, outputs := outputTree }
    if isLocalTypeBase afterOutputs then
      [segment]
    else
      segment :: sisoDecompose afterOutputs (fuel - 1)

/-- Count the number of nodes in an input tree. -/
def InputTree.size : InputTree → Nat
  | .leaf => 0
  | .node _ _ children => 1 + children.foldl (fun acc t => acc + t.size) 0

/-- Count the number of nodes in an output tree. -/
def OutputTree.size : OutputTree → Nat
  | .leaf => 0
  | .node _ _ children => 1 + children.foldl (fun acc t => acc + t.size) 0

/-- Check if an input tree is empty (just a leaf). -/
def InputTree.isEmpty : InputTree → Bool
  | .leaf => true
  | .node _ _ _ => false

/-- Check if an output tree is empty (just a leaf). -/
def OutputTree.isEmpty : OutputTree → Bool
  | .leaf => true
  | .node _ _ _ => false

end Rumpsteak.Protocol.Subtyping.TreeDecomposition
