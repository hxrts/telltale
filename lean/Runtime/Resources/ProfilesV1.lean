import Runtime.VM.Model.TypeClasses

/-
The Problem. V1 needs concrete, transparent instances for authenticated
structures without committing to SMTs or ZK proofs.

Solution Structure. Provide list-backed accumulated sets and hash-equality
based authenticated trees, leaving proof-carrying structures for V2.
-/

set_option autoImplicit false

universe u

/-! ## V1 helper instances -/

instance instDecEqHash (ν : Type u) [VerificationModel ν] : DecidableEq (VerificationModel.Hash ν) :=
  -- Use the verification model's decidable equality.
  VerificationModel.decEqH

/-! ## V1 authenticated tree (content IDs only) -/

instance instAuthTreeV1 (ν : Type u) [VerificationModel ν] : AuthTree ν where
  -- Roots/leaves are hashes; paths are ignored in V1.
  Root := VerificationModel.Hash ν
  Leaf := VerificationModel.Hash ν
  Path := Unit
  verifyPath := fun root leaf _ => decide (root = leaf)

/-! ## V1 accumulated set (list-backed) -/

instance instAccumulatedSetV1 (ν : Type u) [VerificationModel ν] : AccumulatedSet ν where
  -- Keys are hashes; state is a list with membership checks.
  Key := VerificationModel.Hash ν
  State := List (VerificationModel.Hash ν)
  ProofMember := Unit
  ProofNonMember := Unit
  empty := []
  keyOfHash := fun h => h
  insert := fun st k => if decide (k ∈ st) then st else k :: st
  verifyMember := fun st k _ => decide (k ∈ st)
  verifyNonMember := fun st k _ => decide (k ∉ st)
