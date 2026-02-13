import Std
import Runtime.VM.Model.Core
import Runtime.VM.Model.TypeClasses
import SessionTypes.LocalTypeR
import Protocol.LocalType

/-! # Compile LocalTypeR to VM Bytecode

Compiler from SessionTypes.LocalTypeR into Runtime VM instructions, plus a
LocalTypeR → LocalType conversion helper for building program images.
-/

/-
The Problem. Session types are defined in `SessionTypes.LocalTypeR` using named
recursion, but the VM works with `LocalType` using de Bruijn indices. We need
a compiler that performs this translation while preserving semantics.

Solution Structure. Defines `localTypeRToLocalType` converting named recursion to
de Bruijn indices by tracking a context of bound names. Helper `valTypeRToValType`
converts value types. The mutual recursion handles continuation types correctly,
enabling `Protocol.LocalType` values to be generated from high-level session type
definitions.
-/

set_option autoImplicit false

universe u

open SessionTypes.LocalTypeR

/-! ## Core Conversion and Compilation -/

/-! ### LocalTypeR to LocalType conversion helpers -/

/-- LocalType is inhabited for partial conversions. -/
instance : Inhabited LocalType := ⟨.end_⟩

/-- Convert SessionTypes.ValType to Protocol.ValType. -/
def valTypeRToValType : SessionTypes.ValType → ValType
  | .unit => .unit
  | .bool => .bool
  | .nat => .nat
  | .string => .string
  | .prod a b => .prod (valTypeRToValType a) (valTypeRToValType b)
  | .chan sid role => .chan sid role

/-- Find the de Bruijn index of a variable in a binder context. -/
def findVarIdx (ctx : List String) (name : String) : Nat :=
  match ctx.findIdx? (fun x => x == name) with
  | some idx => idx
  | none => 0

/-! #### Mutual conversion recursion -/

mutual
  /-- Convert LocalTypeR (named recursion) to LocalType (de Bruijn). -/
  def localTypeRToLocalTypeAux (ctx : List String) : LocalTypeR → LocalType
    | .end => .end_
    | .send partner branches =>
        match branches with
        | [] => .end_
        | (lbl, vt, cont) :: [] =>
            match vt with
            | some t => .send partner (valTypeRToValType t) (localTypeRToLocalTypeAux ctx cont)
            | none => .select partner [(lbl.name, localTypeRToLocalTypeAux ctx cont)]
        | (lbl₁, _vt₁, cont₁) :: (lbl₂, _vt₂, cont₂) :: rest =>
            .select partner
              ((lbl₁.name, localTypeRToLocalTypeAux ctx cont₁) ::
               (lbl₂.name, localTypeRToLocalTypeAux ctx cont₂) ::
               localTypeRBranchesToChoices ctx rest)
    | .recv partner branches =>
        match branches with
        | [] => .end_
        | (lbl, vt, cont) :: [] =>
            match vt with
            | some t => .recv partner (valTypeRToValType t) (localTypeRToLocalTypeAux ctx cont)
            | none => .branch partner [(lbl.name, localTypeRToLocalTypeAux ctx cont)]
        | (lbl₁, _vt₁, cont₁) :: (lbl₂, _vt₂, cont₂) :: rest =>
            .branch partner
              ((lbl₁.name, localTypeRToLocalTypeAux ctx cont₁) ::
               (lbl₂.name, localTypeRToLocalTypeAux ctx cont₂) ::
               localTypeRBranchesToChoices ctx rest)
    | .mu v body => .mu (localTypeRToLocalTypeAux (v :: ctx) body)
    | .var v => .var (findVarIdx ctx v)
  termination_by
    lt => sizeOf lt
  decreasing_by
    all_goals
      simp
      try omega

  /-- Convert LocalTypeR branch lists to LocalType branch lists. -/
  def localTypeRBranchesToChoices (ctx : List String) : List BranchR → List (String × LocalType)
    | [] => []
    | (lbl, _vt, cont) :: rest =>
        (lbl.name, localTypeRToLocalTypeAux ctx cont) :: localTypeRBranchesToChoices ctx rest
  termination_by
    bs => sizeOf bs
  decreasing_by
    all_goals
      simp
      try omega
end

/-- Public LocalTypeR → LocalType conversion. -/
def localTypeRToLocalType (lt : LocalTypeR) : LocalType :=
  localTypeRToLocalTypeAux [] lt

/-! ### Bytecode construction helper -/

/-- Replace the element at index `n` in a list. -/
def listSet {α : Type u} : List α → Nat → α → List α
  | [], _, _ => []
  | _ :: xs, 0, v => v :: xs
  | x :: xs, n + 1, v => x :: listSet xs n v

/-! ### Recursive bytecode compiler -/

mutual
  def compileInner {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
      [Inhabited (EffectRuntime.EffectAction ε)]
      (defaultAction : EffectRuntime.EffectAction ε)
      (t : LocalTypeR)
      (code : List (Instr γ ε))
      (loopTargets : List (String × PC))
      : List (Instr γ ε) × List (String × PC) :=
    match t with
    | .end => (code ++ [Instr.halt (γ:=γ) (ε:=ε)], loopTargets)
    | .send _ branches =>
        match branches with
        | [] => (code ++ [Instr.halt (γ:=γ) (ε:=ε)], loopTargets)
        | (_, _vt, cont) :: [] =>
            let code := code ++ [Instr.send (γ:=γ) (ε:=ε) 0 1, Instr.invoke (γ:=γ) (ε:=ε) defaultAction]
            compileInner defaultAction cont code loopTargets
        | (lbl, _vt, cont) :: _ =>
            -- Deterministic choice: select the first label (matches default handler behavior).
            let code := code ++ [Instr.offer (γ:=γ) (ε:=ε) 0 lbl.name]
            compileInner defaultAction cont code loopTargets

    -- `recv` case code generation

    | .recv _ branches =>
        match branches with
        | [] => (code ++ [Instr.halt (γ:=γ) (ε:=ε)], loopTargets)
        | (_, _vt, cont) :: [] =>
            let code := code ++ [Instr.receive (γ:=γ) (ε:=ε) 0 1, Instr.invoke (γ:=γ) (ε:=ε) defaultAction]
            compileInner defaultAction cont code loopTargets
        | (lbl₁, _vt₁, cont₁) :: (lbl₂, _vt₂, cont₂) :: rest =>
            let placeholderPc := code.length
            let code := code ++ [Instr.choose (γ:=γ) (ε:=ε) 0 ([] : List (String × PC))]
            let startPc₁ := code.length
            let (code, loopTargets) := compileInner defaultAction cont₁ code loopTargets
            let table := [(lbl₁.name, startPc₁)]
            let startPc₂ := code.length
            let (code, loopTargets) := compileInner defaultAction cont₂ code loopTargets
            let table := table ++ [(lbl₂.name, startPc₂)]
            let (code, table, loopTargets) :=
              compileRecvBranchesAux defaultAction rest code table loopTargets
            let code : List (Instr γ ε) :=
              listSet code placeholderPc (Instr.choose (γ:=γ) (ε:=ε) 0 table)
            (code, loopTargets)

    -- recursion-variable code generation

    | .mu v body =>
        let target := code.length
        let loopTargets := (v, target) :: loopTargets
        compileInner defaultAction body code loopTargets
    | .var v =>
        match loopTargets.find? (fun p => p.fst == v) with
        | some (_, target) => (code ++ [Instr.jump (γ:=γ) (ε:=ε) target], loopTargets)
        | none => (code ++ [Instr.halt (γ:=γ) (ε:=ε)], loopTargets)
  termination_by
    sizeOf t
  decreasing_by
    all_goals
      simp
      try omega

  -- Receive-branch table compilation helper

  def compileRecvBranchesAux {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
      [Inhabited (EffectRuntime.EffectAction ε)]
      (defaultAction : EffectRuntime.EffectAction ε)
      (branches : List BranchR)
      (accCode : List (Instr γ ε))
      (table : List (String × PC))
      (loopTargets : List (String × PC))
      : List (Instr γ ε) × List (String × PC) × List (String × PC) :=
    match branches with
    | [] => (accCode, table, loopTargets)
    | (lbl, _vt, cont) :: rest =>
        let startPc := accCode.length
        let (accCode', loopTargets') := compileInner defaultAction cont accCode loopTargets
        compileRecvBranchesAux defaultAction rest accCode' (table ++ [(lbl.name, startPc)]) loopTargets'
  termination_by
    sizeOf branches
  decreasing_by
    all_goals
      simp
      try omega
end

/-! ### Public compile entrypoint -/

/-- Compile LocalTypeR into bytecode instructions. -/
def ensureTerminal {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    (code : List (Instr γ ε)) : List (Instr γ ε) :=
  match code.getLast? with
  | some .halt => code
  | some (.jump _) => code
  | _ => code ++ [Instr.halt (γ:=γ) (ε:=ε)]

/- ensureTerminal does not change program behavior for well-formed compiles; it
   only guarantees a terminal instruction at the end. -/
def compileLocalTypeR {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    [Inhabited (EffectRuntime.EffectAction ε)]
    (lt : LocalTypeR) : List (Instr γ ε) :=
  let defaultAction : EffectRuntime.EffectAction ε := default
  let (code, _) := compileInner (γ:=γ) (ε:=ε) defaultAction lt [] []
  ensureTerminal (γ:=γ) (ε:=ε) code
