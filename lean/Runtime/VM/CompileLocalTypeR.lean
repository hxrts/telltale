import Std
import Runtime.VM.Core
import Runtime.VM.TypeClasses
import SessionTypes.LocalTypeR
import Protocol.LocalType

/-!
# Compile LocalTypeR to VM Bytecode

Compiler from SessionTypes.LocalTypeR into Runtime VM instructions, plus a
LocalTypeR → LocalType conversion helper for building program images.
-/

set_option autoImplicit false

universe u

open SessionTypes.LocalTypeR

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
        | _ => .select partner (localTypeRBranchesToChoices ctx branches)
    | .recv partner branches =>
        match branches with
        | [] => .end_
        | (lbl, vt, cont) :: [] =>
            match vt with
            | some t => .recv partner (valTypeRToValType t) (localTypeRToLocalTypeAux ctx cont)
            | none => .branch partner [(lbl.name, localTypeRToLocalTypeAux ctx cont)]
        | _ => .branch partner (localTypeRBranchesToChoices ctx branches)
    | .mu v body => .mu (localTypeRToLocalTypeAux (v :: ctx) body)
    | .var v => .var (findVarIdx ctx v)

  /-- Convert LocalTypeR branch lists to LocalType branch lists. -/
  def localTypeRBranchesToChoices (ctx : List String) : List BranchR → List (String × LocalType)
    | [] => []
    | (lbl, _vt, cont) :: rest =>
        (lbl.name, localTypeRToLocalTypeAux ctx cont) :: localTypeRBranchesToChoices ctx rest

  termination_by
    localTypeRToLocalTypeAux _ lt => sizeOf lt
    localTypeRBranchesToChoices _ bs => sizeOf bs
  decreasing_by
    all_goals simp_wf
end

/-- Public LocalTypeR → LocalType conversion. -/
def localTypeRToLocalType (lt : LocalTypeR) : LocalType :=
  localTypeRToLocalTypeAux [] lt

/-- Replace the element at index `n` in a list. -/
def listSet {α : Type u} : List α → Nat → α → List α
  | [], _, _ => []
  | _ :: xs, 0, v => v :: xs
  | x :: xs, n + 1, v => x :: listSet xs n v

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
    | .recv _ branches =>
        match branches with
        | [] => (code ++ [Instr.halt (γ:=γ) (ε:=ε)], loopTargets)
        | (_, _vt, cont) :: [] =>
            let code := code ++ [Instr.recv (γ:=γ) (ε:=ε) 0 1, Instr.invoke (γ:=γ) (ε:=ε) defaultAction]
            compileInner defaultAction cont code loopTargets
        | _ =>
            let placeholderPc := code.length
            let code := code ++ [Instr.choose (γ:=γ) (ε:=ε) 0 ([] : List (String × PC))]
            let (code, table, loopTargets) :=
              compileRecvBranchesAux defaultAction branches code ([] : List (String × PC)) loopTargets
            let code : List (Instr γ ε) :=
              listSet code placeholderPc (Instr.choose (γ:=γ) (ε:=ε) 0 table)
            (code, loopTargets)
    | .mu v body =>
        let target := code.length
        let loopTargets := (v, target) :: loopTargets
        compileInner defaultAction body code loopTargets
    | .var v =>
        match loopTargets.find? (fun p => p.fst == v) with
        | some (_, target) => (code ++ [Instr.jmp (γ:=γ) (ε:=ε) target], loopTargets)
        | none => (code ++ [Instr.halt (γ:=γ) (ε:=ε)], loopTargets)

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
    compileInner _ t _ _ => sizeOf t
    compileRecvBranchesAux _ branches _ _ _ => sizeOf branches
  decreasing_by
    all_goals simp_wf
end

/-- Compile LocalTypeR into bytecode instructions. -/
def ensureTerminal {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    (code : List (Instr γ ε)) : List (Instr γ ε) :=
  match code.getLast? with
  | some .halt => code
  | some (.jmp _) => code
  | _ => code ++ [Instr.halt (γ:=γ) (ε:=ε)]

/- ensureTerminal does not change program behavior for well-formed compiles; it
   only guarantees a terminal instruction at the end. -/
def compileLocalTypeR {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    [Inhabited (EffectRuntime.EffectAction ε)]
    (lt : LocalTypeR) : List (Instr γ ε) :=
  let defaultAction : EffectRuntime.EffectAction ε := default
  let (code, _) := compileInner (γ:=γ) (ε:=ε) defaultAction lt [] []
  ensureTerminal (γ:=γ) (ε:=ε) code
