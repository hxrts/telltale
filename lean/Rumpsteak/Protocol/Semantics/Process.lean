import Rumpsteak.Protocol.GlobalType
import Rumpsteak.Protocol.ListCompat

/-! # Rumpsteak.Protocol.Semantics.Process

Process expressions for operational semantics.

## Overview

This module defines process expressions that represent the runtime behavior
of session-typed programs. Processes can send/receive messages, make choices,
recurse, and run in parallel.

Based on: "A Very Gentle Introduction to Multiparty Session Types" (Yoshida & Gheri)

## Expose

The following definitions form the semantic interface for proofs:

- `Process`: Inductive type for process expressions
- `Process.freeVars`: Extract free process variables
- `Process.substitute`: Substitute a process for a variable

## Main Definitions

- `Process` - Inductive type for process syntax
- `Value` - Runtime values
- Substitution and free variable operations
-/

namespace Rumpsteak.Protocol.Semantics.Process

open Rumpsteak.Protocol.GlobalType (PayloadSort Label)

/-- Runtime values that can be sent in messages. -/
inductive Value where
  /-- Unit value -/
  | unit : Value
  /-- Natural number -/
  | nat : Nat → Value
  /-- Boolean -/
  | bool : Bool → Value
  /-- String -/
  | string : String → Value
  /-- Pair of values -/
  | pair : Value → Value → Value
deriving Repr, DecidableEq, BEq, Inhabited

/-- Process expressions.

    Syntax:
    - `inaction`: Terminated process (0)
    - `send role label value P`: Send value with label to role, continue as P
    - `recv role branches`: Receive from role, branch on label
    - `cond b P Q`: If-then-else
    - `rec X P`: Recursive process μX.P
    - `var X`: Process variable
    - `par P Q`: Parallel composition P | Q

    Processes represent the runtime behavior of session-typed programs. -/
inductive Process where
  /-- Terminated process -/
  | inaction : Process
  /-- Send a message: role!label⟨v⟩.P -/
  | send : String → Label → Value → Process → Process
  /-- Receive with branching: role?{lᵢ.Pᵢ} -/
  | recv : String → List (Label × Process) → Process
  /-- Conditional: if b then P else Q -/
  | cond : Bool → Process → Process → Process
  /-- Recursive process: μX.P -/
  | recurse : String → Process → Process
  /-- Process variable: X -/
  | var : String → Process
  /-- Parallel composition: P | Q -/
  | par : Process → Process → Process
deriving Repr, Inhabited

-- Extract free process variables from a process.
-- Uses mutual recursion to handle the nested `List (Label × Process)` case.
mutual
  /-- Extract free process variables from a process. -/
  def Process.freeVars : Process → List String
    | .inaction => []
    | .send _ _ _ p => p.freeVars
    | .recv _ branches => freeVarsOfBranches branches
    | .cond _ p q => p.freeVars ++ q.freeVars
    | .recurse x p => p.freeVars.filter (· != x)
    | .var x => [x]
    | .par p q => p.freeVars ++ q.freeVars

  /-- Extract free variables from a list of branches. -/
  def freeVarsOfBranches : List (Label × Process) → List String
    | [] => []
    | (_, p) :: rest => p.freeVars ++ freeVarsOfBranches rest
end

/-- If x is in freeVarsOfBranches, it's in some branch's freeVars. -/
theorem freeVarsOfBranches_mem (branches : List (Label × Process)) (x : String)
    (h : x ∈ freeVarsOfBranches branches)
    : ∃ i, ∃ _ : i < branches.length, x ∈ (branches[i]).2.freeVars := by
  induction branches with
  | nil => simp only [freeVarsOfBranches, List.not_mem_nil] at h
  | cons b rest ih =>
    simp only [freeVarsOfBranches, List.mem_append] at h
    cases h with
    | inl hb =>
      exact ⟨0, Nat.zero_lt_succ _, hb⟩
    | inr hrest =>
      have ⟨i, hi, hx⟩ := ih hrest
      exact ⟨i + 1, Nat.succ_lt_succ hi, hx⟩

/-- Converse: if x is in branch i's freeVars, it's in freeVarsOfBranches. -/
theorem freeVarsOfBranches_mem_of (branches : List (Label × Process)) (x : String) (i : Nat)
    (h : x ∈ (branches.get! i).2.freeVars)
    : x ∈ freeVarsOfBranches branches := by
  induction branches generalizing i with
  | nil =>
    simp only [List.get!_nil] at h
    cases h
  | cons b rest ih =>
    simp only [freeVarsOfBranches, List.mem_append]
    cases i with
    | zero =>
      simp only [List.get!_cons_zero] at h
      exact Or.inl h
    | succ n =>
      simp only [List.get!_cons_succ] at h
      exact Or.inr (ih n h)

mutual
  -- Substitute a process for a variable.
  /-- Substitute a process for a variable. -/
  def Process.substitute (proc : Process) (varName : String) (replacement : Process) : Process :=
    match proc with
    | .inaction => .inaction
    | .send role label value p =>
      .send role label value (p.substitute varName replacement)
    | .recv role branches =>
      .recv role (substituteBranches branches varName replacement)
    | .cond b p q =>
      .cond b (p.substitute varName replacement) (q.substitute varName replacement)
    | .recurse x p =>
      if x == varName then
        .recurse x p  -- Variable is shadowed
      else
        .recurse x (p.substitute varName replacement)
    | .var x =>
      if x == varName then replacement else .var x
    | .par p q =>
      .par (p.substitute varName replacement) (q.substitute varName replacement)

  /-- Substitute in a list of branches. -/
  def substituteBranches (branches : List (Label × Process)) (varName : String) (replacement : Process)
      : List (Label × Process) :=
    match branches with
    | [] => []
    | (l, p) :: rest => (l, p.substitute varName replacement) :: substituteBranches rest varName replacement
end

@[simp] theorem substitute_inaction (varName : String) (replacement : Process) :
    Process.substitute .inaction varName replacement = .inaction := by
  simp [Process.substitute]

@[simp] theorem instInhabitedProcess_default : instInhabitedProcess.default = Process.inaction := rfl

@[simp] theorem default_snd_eq_default : (default : Label × Process).snd = (default : Process) := rfl

@[simp] theorem substitute_default (varName : String) (replacement : Process) :
    (default : Process).substitute varName replacement = default := by
  change instInhabitedProcess.default.substitute varName replacement = instInhabitedProcess.default
  simp [Process.substitute]

/-- substituteBranches preserves length.

    PROOF: `substituteBranches` is just `List.map`, so lengths match. -/
theorem substituteBranches_length (branches : List (Label × Process)) (varName : String) (replacement : Process)
    : (substituteBranches branches varName replacement).length = branches.length := by
  induction branches with
  | nil =>
    simp [substituteBranches]
  | cons b rest ih =>
    cases b with
    | mk l p =>
      simp [substituteBranches, ih]

/-- substituteBranches get! preserves label and substitutes process.

    PROOF: By induction on branches, reducing `List.get!` through `map`. -/
theorem substituteBranches_get! (branches : List (Label × Process)) (varName : String) (replacement : Process) (i : Nat)
    : (substituteBranches branches varName replacement).get! i =
      ((branches.get! i).1, (branches.get! i).2.substitute varName replacement) := by
  induction branches generalizing i with
  | nil =>
    cases i <;>
      ext <;> simp [substituteBranches, substitute_default]
  | cons b rest ih =>
    cases b with
    | mk l p =>
      cases i with
      | zero =>
        simp [substituteBranches]
      | succ n =>
        simpa [substituteBranches] using ih n

/-- Unfold one level of recursion: μX.P ↦ P[μX.P/X] -/
def Process.unfold : Process → Process
  | p@(.recurse x body) => body.substitute x p
  | p => p

/-- Check if a process is closed (no free variables). -/
def Process.isClosed (p : Process) : Bool :=
  p.freeVars.isEmpty

/-- Check if a process has terminated. -/
def Process.isTerminated : Process → Bool
  | .inaction => true
  | .par p q => p.isTerminated && q.isTerminated
  | _ => false

/-- Count the size of a process (for termination arguments). -/
partial def Process.size : Process → Nat
  | .inaction => 1
  | .send _ _ _ p => 1 + p.size
  | .recv _ branches => 1 + branches.foldl (fun acc (_, p) => acc + p.size) 0
  | .cond _ p q => 1 + p.size + q.size
  | .recurse _ p => 1 + p.size
  | .var _ => 1
  | .par p q => 1 + p.size + q.size

/-- A role process pairs a role name with its process. -/
structure RoleProcess where
  /-- The role name -/
  role : String
  /-- The process implementing this role -/
  process : Process
deriving Repr, Inhabited

/-- Check if all role processes have terminated. -/
def allTerminated (rps : List RoleProcess) : Bool :=
  rps.all fun rp => rp.process.isTerminated

end Rumpsteak.Protocol.Semantics.Process
